/**
  * DelSAT
  *
  * A tool for differentiable satisfiability and differentiable answer set programming
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  * THIS CODE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
  *
  */

package solving

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.{AbstractBinaryFunction, AbstractUnaryFunction, DifferentialFunction, Variable}

import com.carrotsearch.hppc._

import commandline.delSAT
import commandline.delSAT._

import diff.UncertainAtomsSeprt

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import sharedDefs._

import scala.annotation.tailrec
import scala.collection.{Iterator, Seq, mutable}
import scala.collection.mutable.ArrayBuffer
import scala.concurrent.{Await, Future}
import scala.concurrent.duration.Duration

class Preparation(val aspifOrDIMACSParserResult: sharedDefs.AspifOrDIMACSPlainParserResult, costsOpt: Option[UncertainAtomsSeprt],
                  satMode: Boolean, omitAtomNogoods: Boolean) {

  val timerPrepNs = System.nanoTime()

  val rulesOpt: Option[ArrayBuffer[Rule]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.left.toOption

  val dimacsClauseNogoodsOpt: Option[ArrayBuffer[Array[Eli]]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.right.toOption

  var symbols = aspifOrDIMACSParserResult.symbols

  var symbolsWithIndex: Array[(String, Int)] = null.asInstanceOf[Array[(String, Int)]]

  var noOfPosAtomElis: Int = null.asInstanceOf[Int]

  var noOfPosBlits: Int = aspifOrDIMACSParserResult.noOfPosBlits

  var posNegEliBoundary: Int = null.asInstanceOf[Int]

  var emptyBodyBlit: Eli = aspifOrDIMACSParserResult.emptyBodyBlit

  var noOfAllElis: Int = null.asInstanceOf[Int]

  var assgnmFullSize: Int = null.asInstanceOf[Int]

  var noOfPosElis: Int = null.asInstanceOf[Int]

  def setFoundStructures = {

    symbolsWithIndex = symbols.zipWithIndex

    noOfPosAtomElis = symbols.length

    posNegEliBoundary = noOfPosAtomElis + noOfPosBlits

    noOfAllElis = posNegEliBoundary * 2

    assgnmFullSize = noOfAllElis / 2

    noOfPosElis = assgnmFullSize

    assert(noOfPosElis == posNegEliBoundary, "Error: Internal (1)")

  }

  setFoundStructures

  @inline def isPosAtomEli(eli: Eli) = eli < noOfPosAtomElis

  @inline def isPosEli(eli: Eli) = eli < posNegEliBoundary

  @inline def isNegEli(eli: Eli) = eli >= posNegEliBoundary

  @inline def negateEli(eli: Eli): Eli = {

    if (eli < posNegEliBoundary)
      eli + posNegEliBoundary
    else
      eli - posNegEliBoundary

  }

  @inline def negatePosEli(eli: Eli): Eli = eli + posNegEliBoundary

  @inline def negateNegEli(eli: Eli): Eli = eli - posNegEliBoundary

  @inline def absEli(eli: Eli): Eli = if (isPosEli(eli)) eli else negateNegEli(eli)

  @inline def isFactEli(eli: Eli) = eli < noOfPosAtomElis || eli >= posNegEliBoundary && eli < posNegEliBoundary + noOfPosAtomElis

  @inline def isBlit(eli: Eli) = !isFactEli(eli)

  var posHeadAtomToNegBlits = new java.util.HashMap[Eli, Array[Eli]]() // for non-tight ASP only

  var negBlitToPosBodyElis = new java.util.HashMap[Eli /*negative blit*/ , Array[Eli]]() // for non-tight ASP only

  val clarkNogoods1: ArrayBuffer[Array[Eli]] = dimacsClauseNogoodsOpt.getOrElse {

    val rules = rulesOpt.get

    val (cngs1: ArrayBuffer[Array[Eli]], pHatomNegBlits: java.util.HashMap[Eli, Array[Eli]], bpbes: java.util.HashMap[Eli, Array[Eli]]) =
      computeClarkNogis(rules)

    posHeadAtomToNegBlits = pHatomNegBlits

    negBlitToPosBodyElis = bpbes

    val cngs = if (aspifOrDIMACSParserResult.directClauseNogoodsOpt.isDefined) {

      log("#extra nogoods (in addition to direct clause nogoods): " + cngs1.length)

      cngs1 ++ aspifOrDIMACSParserResult.directClauseNogoodsOpt.get // if we create the full set of nogoods (all rules, all heads...),
      // we can omit the "++ aspifOrDIMACSParserResult..." (I guess - check again!)

    } else cngs1

    cngs

  }

  val (clarkNogoods2: ArrayBuffer[Array[Eli]], removedNogoodsPerAtomOpt) = {

    val cns1R: ArrayBuffer[Array[Eli]] = clarkNogoods1

    val cns1: ArrayBuffer[Array[Eli]] = cns1R //.map(nogood => nogood /*.map(negateEli(_))*/      /*.sorted*/)

    println("#cns1 (K-org): " + cns1.length)

    println("L-org: " + cns1.map(_.length).sum)

    println("Original #variables: " + symbols.length)

    val (cns2: ArrayBuffer[Array[Eli]], removedNogoodsPerAtomOpt: Option[mutable.TreeMap[Eli /*atom eli*/ , ArrayBuffer[Array[Eli]]]]) =
      if (!variableElimConfig._1) (cns1, None) else {

        // TODO (improvement opportunities!):

        val removedNogis = new IntHashSet()

        val productPosNegLitsOrigCap = (cns1.length.toDouble * variableElimConfig._4).toInt

        val noOfResolventsOverheadCap = (cns1.length.toDouble * variableElimConfig._2).toInt

        val noOfOriginalLitsOverheadCap = (noOfAllElis.toDouble * variableElimConfig._3).toInt

        val eliToNogis = Array.fill[mutable.HashSet[Nogi]](noOfAllElis)(mutable.HashSet[Nogi] /*mutable.LinkedHashSet[Nogi]*/ ())

        var nogi = cns1.length - 1

        while (nogi >= 0) {

          val nogood = cns1(nogi)

          nogood.foreach(eliInNogood => eliToNogis(eliInNogood).add(nogi))

          nogi -= 1

        }

        var entry = false

        var maxElimIts = 1 // sometimes eliminating a variable (pos atom) leads to follow-up elimination opportunities, in which case > 1 should be set

        val elimPosAtoms = new IntHashSet() // NB: IntScatterSet.remove (hppc v. 8.1) doesn't seem to work properly?

        var pnNogood = Array.ofDim[Eli](10000)

        val removedNogoodsPerAtom = mutable.TreeMap[Eli /*atom eli*/ , ArrayBuffer[Array[Eli]]]()

        @inline def countNogoods = {

          if (false) {
            val finalNogis = new IntHashSet()

            val finalNogoods = ArrayBuffer[Set[Eli]]()

            eliToNogis.foreach(nogis => nogis.foreach(a => finalNogis.add(a)))

            finalNogis.forEach(a => finalNogoods.append(cns1(a.value).toSet))

            log("#nogoods: " + finalNogoods.length + "\n")

          }

        }

        do {

          entry = false

          var posEli = 0

          while (posEli < noOfPosAtomElis) {

            if (!elimPosAtoms.contains(posEli)) {

              val negPosEli = negatePosEli(posEli)

              val resolvents = new ObjectArrayList[Array[Eli]]() //new mutable.ArrayBuilder.ofRef[Array[Eli]] ()

              var resolventsL = 0

              var pNogiIt = 0

              var resCount = 0

              val nogisWithPosEli = eliToNogis(posEli).toArray

              val nogisWithNegPosEli = eliToNogis(negPosEli).toArray

              var pncLits = 0

              var resLits = 0

              @inline def ccbs = {

                var pIt = nogisWithPosEli.length - 1

                var nIt = nogisWithNegPosEli.length - 1

                val res = new IntHashSet()

                if (pIt * nIt < productPosNegLitsOrigCap)
                  while (pIt >= 0 /*pIndex >= 0*/ ) {
                    {

                      val pNogi: Nogi = nogisWithPosEli(pIt)

                      if (true /*!removedNogis.contains(pNogi)*/ ) {

                        nIt = nogisWithNegPosEli.length - 1

                        while (nIt >= 0) {
                          {

                            val nNogi: Nogi = nogisWithNegPosEli(nIt)

                            if (true /*!removedNogis.contains(nNogi)*/ ) {

                              {

                                val pNogood: Array[Eli] = cns1(pNogi)

                                val nNogood: Array[Eli] = cns1(nNogi)

                                res.clear()

                                //res.sizeHint(pNogood.length + nNogood.length - 2)

                                pncLits += nNogood.length + pNogood.length

                                var ik = pNogood.length - 1

                                var jk = nNogood.length - 1

                                if (ik == 1 && jk == 1) {

                                  val res = Array.ofDim[Eli](2)

                                  if (pNogood(0) == posEli)
                                    res(0) = pNogood(1)
                                  else
                                    res(0) = pNogood(0)

                                  if (nNogood(0) == negPosEli)
                                    res(1) = nNogood(1)
                                  else
                                    res(1) = nNogood(0)

                                  if (res(0) != negateEli(res(1))) {

                                    resLits += res.size

                                    resolvents.add(res)

                                  }

                                } else {


                                  var isTaut = false

                                  while (ik >= 0) {

                                    val lit = pNogood(ik)

                                    if (lit != posEli)
                                      res.add(lit)

                                    ik -= 1

                                  }

                                  while (jk >= 0 && !isTaut) {

                                    val lit = nNogood(jk)

                                    if (res.contains(negateEli(lit))) {

                                      isTaut = true

                                    } else if (lit != negPosEli /*&& lit != posEli*/ )
                                      res.add(lit)

                                    jk -= 1

                                  }


                                  if (!isTaut) {

                                    resLits += res.size

                                    resolvents.add(res.toArray)

                                  }
                                }

                              }

                            }

                          }

                          nIt -= 1

                        }

                      }

                    }

                    pIt -= 1

                  } else pncLits = -1

              }

              ccbs

              @inline def adc1 = {

                val rmv = ArrayBuffer[Array[Eli]]()

                @inline def rmNogood(nogi: Nogi) = {

                  removedNogis.add(nogi)

                  rmv.append(cns1(nogi))

                  eliToNogis.foreach { case nogis: mutable.HashSet[Nogi] => {

                    nogis.remove(nogi)

                    //assert(!nogis.contains(nogi))

                  }
                  }

                }

                nogisWithPosEli.foreach(a => {

                  rmNogood(a)

                })

                nogisWithNegPosEli.foreach(a => {

                  rmNogood(a)

                })

                removedNogoodsPerAtom.put(posEli, rmv)

                //println("  -Eliminated positive eli (variable) " + posEli + "  [negated: " + negatePosEli(posEli) + "]")

                countNogoods

              }

              val resolventsA = resolvents

              @inline def adc2 = {

                resolventsA.forEach { a => {

                  val resolvent = a.value

                  val newNogi = cns1.length

                  val resolventA = resolvent

                  cns1.append(resolventA)

                  var k = resolventA.length - 1

                  while (k >= 0) {

                    val eli = resolventA(k)

                    eliToNogis(eli).add(newNogi)

                    k -= 1

                  }

                  //}

                }

                }

              }

              val oldS = pncLits

              val newS = resLits

              if (resolventsA.size - (nogisWithPosEli.length + nogisWithNegPosEli.length) <= noOfResolventsOverheadCap &&
                (newS - oldS <= noOfOriginalLitsOverheadCap) && pncLits != -1) {

                adc1

                adc2

                entry = true

                elimPosAtoms.add(posEli)

                countNogoods

              }

            }

            posEli += 1

          }

          maxElimIts -= 1

        } while (entry && maxElimIts > 0)

        val finalNogis = new IntHashSet()

        val finalNogoods = ArrayBuffer[Array[Eli]]()

        eliToNogis.foreach(nogis => nogis.foreach(a => finalNogis.add(a)))

        finalNogis.forEach(a => finalNogoods.append(cns1(a.value)))

        (finalNogoods, Some(removedNogoodsPerAtom))

      }

    log("#cns2: " + cns2.length)

    val cns3 = if (variableElimConfig._5 && removedNogoodsPerAtomOpt.isDefined) {

      assert(satMode) // TODO: make work with ASP (see "posHeadAtomToNegBlits =" below) or generatePseudoRulesForNogoodsForSATMode

      println("Removing eliminated elis...")

      val removedPosElis = removedNogoodsPerAtomOpt.get.keys.toSet

      val eliChangeMap = mutable.HashMap[Eli, Eli]()

      var offset = 0

      (0 to noOfAllElis).foreach(oldEli => {

        if (isPosEli(oldEli) && removedPosElis.contains(oldEli) || isNegEli(oldEli) && removedPosElis.contains(negateNegEli(oldEli)))
          offset += 1
        else {

          eliChangeMap.update(oldEli, oldEli - offset)

        }
      })

      val r = cns2.map(nogood => nogood.map { oldEli => {

        assert(!removedPosElis.contains(oldEli))

        val newEli = if (isPosEli(oldEli)) {

          assert(!removedPosElis.contains(oldEli))

          eliChangeMap(oldEli)

        }
        else {

          assert(!removedPosElis.contains(negateNegEli(oldEli)))

          eliChangeMap(oldEli)

        }

        newEli
      }
      })

      symbols = symbolsWithIndex.filterNot { case (_, index) => removedPosElis.contains(index) }.map(_._1)

      assert(noOfPosBlits == 0)

      setFoundStructures

      //    posHeadAtomToNegBlits = pHatomNegBlits // TODO
      //
      //    negBlitToPosBodyElis = bpbes  // TODO

      log("Removed pos elis: " + removedPosElis.size)

      log("#variables:" + symbols.length)

      r

    } else cns2

    if (debug) {

      log("\nNogoods from Clark's Completion:\n")

      cns3.foreach((nogood: Array[Eli]) => {

        log(" " + nogood.map(eli => if (!isBlit(eli)) (if (isNegEli(eli)) "not " + symbols(negateEli(eli)) else symbols(eli)) else (if (isNegEli(eli)) "not " + "bodyeli" + negateEli(eli) else "bodyeli" + eli)).mkString(","))


      })

      log("\n-------------------\n")

      log("\nNogoods from Clark's Completion (as eli seqs):\n")

      cns3.foreach((nogood: Array[Eli]) => {

        log(" " + nogood.mkString(","))


      })

    }

    (cns3, removedNogoodsPerAtomOpt)

  }

  //println("#clarkNogoods1: " + clarkNogoods1.length)

  val clarkNogoods = clarkNogoods2 //.filterNot(nogood1 => clarkNogoods1.exists(nogood2 => nogood2.toSet.subsetOf(nogood1.toSet)))

  log("final #clarkNogoods: " + clarkNogoods.length)

  val dependencyGraph: IntObjectHashMap[List[Eli]] = if (satMode) new IntObjectHashMap[List[Eli]]() else rulesOpt.map(rules =>
    computeDependencyGraph(rules, noOfPosAtomElis)).getOrElse(new IntObjectHashMap[List[Eli]]())

  val progIsTight: Boolean = if (satMode) true else isAcyclic(dependencyGraph)

  if (!satMode) (if (progIsTight) println("Program is tight") else println("Program is not tight"))

  val costFctsInnerWithPossMeasuredElis = ArrayBuffer[(DifferentialFunction[DoubleReal], Eli /*measured*/ )]()

  val nablasInner /*partial derivatives of the inner cost functions*/ : Array[DifferentialFunction[DoubleReal]] =
    Array.fill[DifferentialFunction[DoubleReal]](symbols.length /*if we could place
          the uncertain atoms at the beginning of symbols, we could keep this array smaller, but this would require costly re-ordering operations
          in aspifParse() */)(null.asInstanceOf[DifferentialFunction[DoubleReal]])

  val dFFactory = new diff.DifferentialFunctionFactoryStasp()

  val parameterAtomVarForParamAtomEli_forPartDerivCompl = mutable.HashMap[Int, Variable[DoubleReal]]()

  val symbolToEli: Predef.Map[String, Eli] = symbols.zipWithIndex.toMap

  val parameterAtomsElis0 /*(from  the "pats" line)*/ : Array[Eli] = costsOpt.map(_.parameterAtomsSeq).map(pmasg =>
    pmasg.map(pred => symbolToEli(pred))).getOrElse(Array[Eli]())

  @inline def measuredAtomNameInCostFnToSymbol(n: String): String = if (satMode) n.stripPrefix("v") else n

  @inline def translateDiffFunMeasuredAtomIndex2PosEli(index: Int): Eli = symbolToEli(measuredAtomNameInCostFnToSymbol(costsOpt.get.measuredAtomsSeq(index)))

  val measuredAtomsElis /*(from within the cost functions)*/ : Array[Eli] = costsOpt.map(_.measuredAtomsSeq).map(_.map(vn => symbolToEli(measuredAtomNameInCostFnToSymbol(vn)))).getOrElse(Array[Eli]())

  // TODO: no current use for measured atoms (since this version doesn't support, e.g., cost backtracking), we simply assume here that
  // they are identical to the parameter atoms.

  setCostFctsInner

  def setCostFctsInner = {

    costsOpt.foreach(inputDataCostFunBased => {

      inputDataCostFunBased.innerCostExpressionInstances.foreach(costFunInner => {

        var possibleMeasuredEli = -1

        @inline def translateMeasuredAtomIndices(fn: DifferentialFunction[DoubleReal], noPhi: Boolean): DifferentialFunction[DoubleReal] = {
          // If we've generated the differentiable functions outside NablaSAT,
          // then the index in phi(index) is originally not an atom eli but an index within inputDataCostFunBasedOpt.get.measuredAtomsSeqSorted

          def setViaReflection(ref: AnyRef, fieldName: String, value: AnyRef) = {

            try {

              val f = ref.getClass.getSuperclass.getDeclaredField(fieldName)

              f.setAccessible(true)

              f.set(ref, value.asInstanceOf[AnyRef])

            }

          }

          if (fn.toString.startsWith("phi(")) {

            val eli = translateDiffFunMeasuredAtomIndex2PosEli(fn.asInstanceOf[AbstractUnaryFunction[DoubleReal]].arg().getReal.toInt)

            if (possibleMeasuredEli == -1)
              possibleMeasuredEli = eli
            else
              possibleMeasuredEli = -1

            val varName = if (noPhi) "freqx" + eli + "_" else "ua"

            val translatedArg = dFFactory.`var`(varName /*TODO: "ua" is hardcoded in various places*/ ,
              new DoubleReal(if (noPhi) -1d /*dummy,  will later be updated with measured frequency*/ else eli.toDouble))

            if (noPhi) {

              parameterAtomVarForParamAtomEli_forPartDerivCompl.put(eli, translatedArg)

              translatedArg // we replace the phi(atom) with a new variable freqx<Eli>_, e.g., freqx726_

            } else {

              setViaReflection(fn.asInstanceOf[AbstractUnaryFunction[DoubleReal]], "m_x", translatedArg)

              fn

            }

          } else if (fn.isInstanceOf[AbstractUnaryFunction[DoubleReal]]) {

            setViaReflection(fn.asInstanceOf[AbstractUnaryFunction[DoubleReal]], "m_x", translateMeasuredAtomIndices(fn.asInstanceOf[AbstractUnaryFunction[DoubleReal]].arg(), noPhi))

            fn

          } else if (fn.isInstanceOf[AbstractBinaryFunction[DoubleReal]]) {

            setViaReflection(fn.asInstanceOf[AbstractBinaryFunction[DoubleReal]], "m_x1", translateMeasuredAtomIndices(fn.asInstanceOf[AbstractBinaryFunction[DoubleReal]].larg(), noPhi))

            setViaReflection(fn.asInstanceOf[AbstractBinaryFunction[DoubleReal]], "m_x2", translateMeasuredAtomIndices(fn.asInstanceOf[AbstractBinaryFunction[DoubleReal]].rarg(), noPhi))

            fn

          } else
            fn

        }

        log("Original costFunInner (prior argument index->eli translation): " + costFunInner)

        val costFunInnerWithElis: DifferentialFunction[DoubleReal] = translateMeasuredAtomIndices(costFunInner, noPhi = true /*partDerivComplete*/)

        costFctsInnerWithPossMeasuredElis.append((costFunInnerWithElis, possibleMeasuredEli))

        log("Translated costFctsInner(measuredAtomEli): " + costFunInnerWithElis)

      })

    })

  }

  log("\npreptimer 2.1: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

  @inline def findInnerCostFunForParameterAtom(parameterAtomEli: Eli): Option[DifferentialFunction[DoubleReal]] = {

    val fOpt = costFctsInnerWithPossMeasuredElis.find(_._2 == parameterAtomEli)

    if (fOpt.isDefined)
      Some(fOpt.get._1)
    else
      None

  }

  log("\npreptimer 3: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

  val parameterAtomsElis = parameterAtomsElis0.filter(parameterAtomVarForParamAtomEli_forPartDerivCompl.contains(_))
  // ^the above ensures we only keep parameter atoms which occur as measured atoms in cost formulas (TODO: remove as soon as
  // delSAT supports disjoint param vs. measured)

  val innerCostFunForParamAtomEli = if (ignoreParamVariables) mutable.Map[Eli, Option[DifferentialFunction[DoubleReal]]]() else
    mutable.HashMap[Eli, Option[DifferentialFunction[DoubleReal]]]().++(parameterAtomsElis.map(eli => {

      eli -> findInnerCostFunForParameterAtom(eli)

    }).toMap)

  log("\npreptimer 4: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

  val costFctsInner = costFctsInnerWithPossMeasuredElis.unzip._1

  val n = dFFactory.`val`(new DoubleReal(costFctsInner.length.toDouble))

  val totalCostFun_forPartDerivCompl: DifferentialFunction[DoubleReal] = if (costFctsInner.isEmpty) dFFactory.`val`(new DoubleReal(-1 /*dummy*/)) else
    costFctsInner.reduceLeft((reduct: DifferentialFunction[DoubleReal], addendum: DifferentialFunction[DoubleReal])
    => reduct.plus(addendum)).div(n)

  if (!ignoreParamVariables)
    parameterAtomsElis.foreach(parameterAtomEli => { // this probably only makes sense if parameter atoms == measured atoms...!

      val parameterAtomVar: Variable[DoubleReal] = parameterAtomVarForParamAtomEli_forPartDerivCompl(parameterAtomEli)

      if (partDerivComplete) { // see M. Nickles: PLP'18 paper; use with non-MSE cost functions (more general but slower)

        nablasInner(parameterAtomEli) = totalCostFun_forPartDerivCompl.diff(parameterAtomVar)

      } else { // faster, less general. For simple MSE-style (and some others?) cost functions. See ILP'18 paper.

        val innerCostFun: DifferentialFunction[DoubleReal] = innerCostFunForParamAtomEli /*findInnerCostFunForParameterAtom*/ (parameterAtomEli).getOrElse {
          assert(false, "Inner cost functions invalid for selected type of differentiation. Try with command line argument\n --solverarg \"partDerivComplete\" \"true\"");
          costFctsInner(0)
        }

        val indexOfPwPr = /*translatePosEli2DiffUncertainAtomIndex*/ (parameterAtomEli)

        nablasInner(parameterAtomEli) = innerCostFun.diff(parameterAtomVar)

      }

      log("nablasInner for parameter atom " + /*symbols*/ (parameterAtomEli) + ": " + nablasInner(parameterAtomEli))

    })

  log("\npreptimer 5: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

  val parameterAtomsElisSet: Set[Eli] = parameterAtomsElis.toSet

  val parameterLiteralElis: Array[Eli] = parameterAtomsElis ++ parameterAtomsElis.map(negatePosEli(_))

  val deficitOrdering2: Ordering[Integer /*actually a parameter eli*/ ] =
    Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {

      // Assumes that in a step directly preceding the re-sorting, the variables in the nablaInner have been
      // updated to measuredAtomEliToStatisticalFreq!

      val deficit =
        (if (isPosAtomEli(parameterLiteralEli))
          nablasInner(parameterLiteralEli).getReal
        else
          -nablasInner(negateNegEli(parameterLiteralEli)).getReal) + 1d

      deficit

      //Math.signum(deficit)  // without prioritization of most "needy" parameter literals

    })

  var deficitOrderedUncertainLiterals = parameterLiteralElis.map(new Integer(_))

  var measuredAtomEliToStatisticalFreq: Array[Double] = Array.ofDim[Double](symbols.length)

  @inline def update_parameterAtomVarForParamEli_forPartDerivCompl: Unit = {

    // we update the values of the parameter variables in the partial derivatives with the latest measured frequencies:

    parameterAtomsElis.foreach(paramAtomEli => {

      val freq = measuredAtomEliToStatisticalFreq(paramAtomEli) // so this only works if measured = parameter atoms (but we distinguish them,
      // for future extensions, e.g., with the cost-backtracking algo from the ILP'18 paper)

      parameterAtomVarForParamAtomEli_forPartDerivCompl(paramAtomEli).set(new DoubleReal(freq))

    })

  }

  update_parameterAtomVarForParamEli_forPartDerivCompl

  println("\nPreparation time: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

  def computeClarkNogis(rules: ArrayBuffer[Rule]): (ArrayBuffer[Array[Eli]], java.util.HashMap[Eli, Array[Eli]], java.util.HashMap[Eli, Array[Eli]]) = {

    // Follows (with a few minor differences) https://www.cs.uni-potsdam.de/wv/pdfformat/gekanesc07a.pdf

    // NB: the following algorithm assumes that all rules are normal. E.g., :- integrity constraints are not allowed (need
    // to be preprocessed, see AspifParser).

    val exclEmptyBodyInDeltaAtoms = false // must be false (true for debugging only)

    val thresholdForSymbolsPar = 1000000

    val thresholdForRulesPar = 1000000

    val noOfThreads = 4

    val createFalsNgs: Boolean = false // deprecated

    val rulesWoConstr = if (!sharedDefs.specialConstrRuleNogoods) rules else /*we create special nogoods later for the omitted ones: */
      rules.filterNot(rule => isPosEli(rule.headAtomsElis.head) && ASPIOutils.isFalsAuxAtom(symbols(rule.headAtomsElis.head)))

    val noOfThreadsNg = if (rulesWoConstr.length < thresholdForRulesPar) 1 else noOfThreads

    val rulesPartitioning: Iterator[ArrayBuffer[Rule]] = if (rulesWoConstr.isEmpty) Iterator(ArrayBuffer[Rule]()) else rulesWoConstr.grouped(if (noOfThreadsNg == 1 || rulesWoConstr.length < noOfThreadsNg - 1) rulesWoConstr.length else rulesWoConstr.length / (noOfThreadsNg - 1))

    val negBlitToPosBodyElis: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    val posHeadAtomToNegBlits: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // ^ we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    println("\npreptimer0: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

    def deltaBetaPartComp(rulesPart: ArrayBuffer[Rule]) = { // generate body nogoods

      val deltaBetaPart = mutable.ArrayBuffer[Array[Eli]]()

      //deltaBetaPart.sizeHint(rulesWoConstr.length * 5 + 1000)

      var ri = 0

      val rpl = rulesPart.length

      while (ri < rpl) {

        val rule = rulesPart(ri)

        val bpos: Array[Eli] = rule.bodyPosAtomsElis

        val bneg: Array[Eli] = rule.bodyNegAtomsElis

        val bNeg = negatePosEli(rule.posBodyEli)

        val s1: Array[Eli] = Array.ofDim[Eli](bpos.length + bneg.length + 1)

        bpos.copyToArray(s1, 0)

        bneg.copyToArray(s1, bpos.length)

        s1(s1.length - 1) = bNeg

        deltaBetaPart.append(s1) // δ(β)

        negBlitToPosBodyElis.put(bNeg, bpos)

        val bPos = rule.posBodyEli // the blit of the rule

        val s2pos: Array[Array[Eli]] = bpos.map(eli => Array(bPos, negatePosEli(eli)))

        deltaBetaPart.appendAll(s2pos) // Δ(β)

        val s2neg: Array[Array[Eli]] = bneg.map(eli => Array(bPos, negateNegEli(eli)))

        deltaBetaPart.appendAll(s2neg) // Δ(β)

        ri += 1

      }

      log("\npreptimer1: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

      deltaBetaPart

    }

    def deltaAtomsComp(omit: Boolean): mutable.ArrayBuffer[Array[Eli]] = { // generate head/atom-related nogoods

      val deltaAtoms = mutable.ArrayBuffer[Array[Eli]]()

      if (!omit) {

        //deltaAtoms.sizeHint(symbols.length * 5 + 1000)

        log("\npreptimer2a: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

        val rulesGroupedByTheirHeadEli = Array.fill[ArrayBuffer[Rule]](noOfAllElis)(ArrayBuffer[Rule]())

        var rwci = 0

        val rwcl = rulesWoConstr.length

        while (rwci < rwcl) {

          val rule = rulesWoConstr(rwci)

          val h = rule.headAtomsElis.headOption.getOrElse(-1)

          //assert(h >= 0)

          rulesGroupedByTheirHeadEli(h).append(rule)

          rwci += 1

        }

        log("\npreptimer2b: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

        val zeroToSymLen = (0 until noOfPosAtomElis) ++ (posNegEliBoundary until posNegEliBoundary + noOfPosAtomElis)
        // ^ all positive and negative literals except blits. Note that negative head lits should not (yet) occur in ASP mode, these
        // are only generated in pseudo-rules in SAT-mode.

        (if (zeroToSymLen.size > thresholdForSymbolsPar) zeroToSymLen.par else zeroToSymLen).flatMap { atomEli_p => {

          // TODO: We should optionally treat #external atoms here specially, even if they don't occur in any rules, in which case nogoods are generated for them to ensure they are never true.

          val bodiesOfp: ArrayBuffer[Rule] = rulesGroupedByTheirHeadEli(atomEli_p)

          val s1s2 = ArrayBuffer[Array[Eli]]()

          if (!satMode || !bodiesOfp.isEmpty) {

            if (bodiesOfp.isEmpty && isPosEli(atomEli_p) && !symbols(atomEli_p).startsWith(ASPIOutils.auxPredPrefixBase))
              stomp(-5005, symbols(atomEli_p))


            s1s2.sizeHint(bodiesOfp.length + 1)

            if (!bodiesOfp.isEmpty) {

              val negHeadAtomEli: Eli = negateEli(atomEli_p)

              bodiesOfp.foreach(rule => { // Δ(p)

                s1s2.append(if (exclEmptyBodyInDeltaAtoms && (/*(rule.bodyPosAtomsElis.isEmpty && rule.bodyNegAtomsElis.isEmpty)*/
                  rule.posBodyEli == emptyBodyBlit)) Array(negHeadAtomEli) else
                  Array(negHeadAtomEli, rule.posBodyEli))

              })

            }

            // TODO:  handle #external atoms here (currently ignored / treated as undefined unless defined in some rule):
            if (((bodiesOfp.length > 1 || bodiesOfp.length == 1 && bodiesOfp.head.posBodyEli != emptyBodyBlit))) { // δ(p)
              // ^ in satMode, this branch is only allowed if we create _all_ possible pseudo-rules (for all clauses and heads),
              // otherwise the following can lead to wrong UNSAT:

              val s2NogoodBuffer = Array.ofDim[Eli](bodiesOfp.length + 1)

              var s2i = 0

              bodiesOfp.foreach(rule => { // ? note: if we do this even if bodiesOfp is empty, which creates false-enforcing nogoods for undefined symbols

                s2NogoodBuffer(s2i) = negatePosEli(rule.posBodyEli)

                s2i += 1

              })

              s2NogoodBuffer(s2i) = atomEli_p

              posHeadAtomToNegBlits.put(atomEli_p, s2NogoodBuffer.slice(0, s2i))

              s1s2.append(s2NogoodBuffer)

            }

            Some(s1s2) //.distinct

          } else
            None

        }
        }.seq.foreach(deltaAtoms.appendAll(_))

        log("\npreptimer2: " + (System.nanoTime() - timerPrepNs) / 1000000 + " ms\n")

      }

      deltaAtoms

    }

    val deltaClark: mutable.ArrayBuffer[Array[Eli]] = if (noOfThreadsNg == 1) {

      val rulesOnlyPart = rulesPartitioning.next()

      assert(rulesOnlyPart.length == rulesWoConstr.length)

      deltaBetaPartComp(rulesOnlyPart) ++ deltaAtomsComp(omitAtomNogoods)

    } else {

      implicit val executor = scala.concurrent.ExecutionContext.global

      val deltaBetaFutures: Iterator[Future[ArrayBuffer[Array[Eli]]]] = rulesPartitioning.map((rulesPart: ArrayBuffer[Rule]) => Future {

        deltaBetaPartComp(rulesPart)

      }(executor))

      val deltaAtomsFuture = Future {

        deltaAtomsComp(omitAtomNogoods)

      }(executor)

      val deltas: ArrayBuffer[ArrayBuffer[Array[Eli]]] = Await.result(Future.sequence(Seq(deltaAtomsFuture) ++ deltaBetaFutures), Duration.Inf).to[ArrayBuffer]

      deltas.flatten

    }

    val falsNogoods: ArrayBuffer[Array[Eli]] = if (createFalsNgs)
      symbolsWithIndex.filter(si => ASPIOutils.isFalsAuxAtom(si._1)).map(x => Array(x._2)).to[ArrayBuffer]
    else if (!sharedDefs.specialConstrRuleNogoods) ArrayBuffer[Array[Eli]]() else {

      // we add special nogoods for rules which have been (elsewhere) resulted from constraints :- b1, b2, ...

      val contraintRules = rules.filter(rule => isPosAtomEli(rule.headAtomsElis.head) && ASPIOutils.isFalsAuxAtom(symbols(rule.headAtomsElis.head)))

      contraintRules.map(rule => rule.bodyPosAtomsElis ++ rule.bodyNegAtomsElis.filterNot(_ == negateEli(rule.headAtomsElis.head)))

    }

    if (delSAT.showProgressStats) {

      System.out.println("# special constraint rule nogoods = " + falsNogoods.length)

    }

    val r = deltaClark ++ falsNogoods

    (r, posHeadAtomToNegBlits, negBlitToPosBodyElis)

  }

  def computeLeastHerbrandDefClauses(posDefClauseProg: Seq[Rule]): IntOpenHashSet = {

    var m = new IntOpenHashSet()

    var conv = false

    @inline def tp = {

      posDefClauseProg.foreach((rule: Rule) => {

        if (rule.bodyPosAtomsElis.forall(m.contains(_)))
          m.add(rule.headAtomsElis.headOption.getOrElse(-1))

      })

    }

    while (!conv) { // iterative fixpoint construction of least model

      val oldSize = m.size

      tp

      conv = m.size == oldSize

    }

    m

  }

  def checkASPWithEliRules(modelCandidate: (Array[Eli], IntOpenHashSet), ruless: ArrayBuffer[Rule]): (Boolean, Array[Eli]) = {

    val rules = ruless.filter(r => !(r.posBodyEli == emptyBodyBlit && r.headAtomsElis.isEmpty && r.bodyNegAtomsElis.isEmpty) /*<- dummy rules " :- "*/)

    val r1: Seq[Rule] = rules.filterNot {
      _.bodyNegAtomsElis.exists(negEli /* modelCandidate contains positive atomic elis only, so we need to check for negated negEli: */ => {

        val x = negateNegEli(negEli)

        modelCandidate._2.contains(x)

      }
      )
    }

    val reduct: Seq[Rule] = r1.map(r => new Rule(headAtomsElis = r.headAtomsElis,
      bodyPosAtomsElis = r.bodyPosAtomsElis, bodyNegAtomsElis = Array[Eli](), posBodyEli = -1)) // Gelfond-Lifschitz reduct

    val lhm = computeLeastHerbrandDefClauses(reduct)

    val isAS =
      if (lhm.contains(-1 /*i.e., false, from a ':- ...' constraint */))
        (false, modelCandidate._1)
      else {

        val isStableModel = modelCandidate._2.equals(lhm)

        // Iff we were guaranteed that modelCandidate is already a supported model, it was
        // sufficient to say isStableModel <=> modelCandidate.--(lhm).isEmpty (see revisedASSAT paper).

        // Make sure to use the revised ASSAT paper (http://www.cs.ust.hk/~flin/papers/assat-aij-revised.pdf), the original paper
        // contains a severe typo.

        (isStableModel, if (isStableModel) Array[Eli]() else {

          val remainder: Array[Eli] = modelCandidate._1.filterNot(lhm.contains(_))

          //val invRemainder = lhm.filterNot(modelCandidate.contains(_))

          //log("invRemainder: \n" + invRemainder.map(symbols(_)).mkString(","))

          remainder

        })

      }

    isAS

  }

  def computeDependencyGraph(rules: ArrayBuffer[Rule], noOfAllPosAtomElis: Int): IntObjectHashMap[List[Eli]] = {

    var graphInit = new IntObjectHashMap[List[Eli]]()

    var jj = 0

    while (jj < rules.length) {

      val rule = rules(jj)

      if (!rule.headAtomsElis.isEmpty) {

        val headEli = rule.headAtomsElis.head

        assert(isPosEli(headEli), "Error: only normal rules with positive head literal supported")

        val successorNodes: Array[Eli] = rule.bodyPosAtomsElis

        val succsOfPosHeadEli = {

          val assocs = graphInit.get(headEli)

          if (assocs == null) {

            graphInit.put(headEli, List[Eli]())

            List[Eli]()

          } else
            assocs

        }

        successorNodes.foreach(succEli => {

          graphInit.put(headEli, succsOfPosHeadEli.:+(succEli))

        })
      }

      jj += 1

    }

    graphInit

  }

  @tailrec final def isAcyclic(depGraph: IntObjectHashMap[List[Eli]]): Boolean = {

    depGraph.isEmpty || {

      val leaveElisB = new mutable.ArrayBuilder.ofInt

      val nonLeaveGraphPart = ArrayBuffer[(Eli, List[Eli])]()

      val graphEntries: IntObjectHashMap[List[Eli]]#KeysContainer = depGraph.keys()

      graphEntries.forEach(key => {

        val v: List[Eli] = depGraph.get(key.value)

        if (v.isEmpty)
          leaveElisB.+=(key.value)
        else
          nonLeaveGraphPart.append((key.value, v))

      })

      val leaveElis = leaveElisB.result()

      !leaveElis.isEmpty && {

        val strippedGraph = new IntObjectHashMap[List[Eli]]()

        nonLeaveGraphPart.foreach((keyValues: (Eli, List[Eli])) => {

          strippedGraph.put(keyValues._1, keyValues._2.filterNot((eli: Eli) => leaveElis.contains(eli)))

        })

        isAcyclic(strippedGraph)

      }

    }

  }

}
