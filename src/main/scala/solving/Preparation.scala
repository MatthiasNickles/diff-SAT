/**
  * DelSAT
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE
  *
  */

package solving

import aspIOutils._

import com.accelad.math.nilgiri.DoubleReal

import com.accelad.math.nilgiri.autodiff.{AbstractBinaryFunction, AbstractUnaryFunction, DifferentialFunction, Variable}

import commandline.delSAT
import commandline.delSAT._

import it.unimi.dsi.fastutil.ints.{Int2ObjectOpenHashMap, IntSet}
import it.unimi.dsi.fastutil.objects.ObjectArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import diff.UncertainAtomsSeprt

import sharedDefs._

import sun.misc.Contended

import utils.{FloatArrayUnsafe, IntArrayUnsafe}

import scala.annotation.tailrec

import scala.collection.{Iterator, Seq, mutable}
import scala.collection.mutable.ArrayBuffer

import scala.concurrent.{Await, Future}
import scala.concurrent.duration.Duration

/**
  * @author Matthias Nickles
  *
  */
class Preparation(val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult, costsOpt: Option[UncertainAtomsSeprt],
                  satModeR: Boolean, omitAtomNogoods: Boolean) {

  assert(!omitAtomNogoods)

  val satMode = satModeR

  val timerPrepNs = System.nanoTime()

  val rulesOpt: Option[ArrayBuffer[Rule]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.left.toOption

  val dimacsClauseNogoodsOpt: Option[Array[ArrayEliUnsafe]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.right.toOption

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

  val clarkNogoods1: Array[ArrayEliUnsafe] = dimacsClauseNogoodsOpt.getOrElse {

    val rules = rulesOpt.get

    val (cngs1: Array[ArrayEliUnsafe], pHatomNegBlits: java.util.HashMap[Eli, Array[Eli]], bpbes: java.util.HashMap[Eli, Array[Eli]]) =
      computeClarkNogis(rules)

    posHeadAtomToNegBlits = pHatomNegBlits

    negBlitToPosBodyElis = bpbes

    val cngs = if (aspifOrDIMACSParserResult.directClauseNogoodsOpt.isDefined) {

      if (verbose)
        println("#extra nogoods from pseudo-rules (in addition to direct clauses nogoods): " + cngs1.length)

      aspifOrDIMACSParserResult.directClauseNogoodsOpt.get ++ cngs1

    } else cngs1

    cngs

  }

  val (clarkNogoods2: Array[ArrayEliUnsafe], removedNogoodsPerAtomOpt) = {

    val cns1: ArrayBuffer[ArrayEliUnsafe] = clarkNogoods1.to[ArrayBuffer]

    lazy val lorgno = cns1.map(_.size()).sum

    lazy val oldN = symbols.length

    if (verbose && variableOrNogoodElimConfig._1) {

      println("K-org (clauses): " + cns1.length) // original #clauses

      println("L-org (literals): " + lorgno) // original #literals (i.e. elis in our case)

      println("N-org (variables): " + oldN) // original #symbols (variables)

    }

    val startTimeVarElim = System.nanoTime()

    val (cns2: ArrayBuffer[ArrayEliUnsafe], removedNogoodsPerAtomOpt: Option[mutable.TreeMap[Eli /*atom eli*/ , ArrayBuffer[ArrayEliUnsafe]]]) =
      if (!variableOrNogoodElimConfig._1) (cns1, None) else { // static variable elimination

        // TODO (improvement opportunities):

        val removedNogis = new IntOpenHashSet()

        val productPosNegLitsOrigCap = (Math.sqrt(cns1.length.toDouble) * variableOrNogoodElimConfig._4).toInt

        val noOfResolventsOverheadCap = (cns1.length.toDouble * variableOrNogoodElimConfig._2).toInt

        val noOfOriginalLitsOverheadCap = (noOfAllElis.toDouble * variableOrNogoodElimConfig._3).toInt

        val eliToNogisTemp = Array.fill[IntOpenHashSet](noOfAllElis)(new IntOpenHashSet /*mutable.LinkedHashSet[Nogi]*/ ())

        var nogi = cns1.length - 1

        while (nogi >= 0) {

          val nogood: ArrayEliUnsafe = cns1(nogi)

          var k = nogood.size() - 1

          while (k >= 0) {

            eliToNogisTemp(nogood.get(k)).add(nogi)

            k -= 1

          }

          nogi -= 1

        }

        var entry = false

        var maxElimIts = 1 // sometimes eliminating a variable (pos atom) leads to follow-up elimination opportunities, in which case > 1 should be set

        val elimPosAtoms = new IntOpenHashSet()

        var pnNogood = Array.ofDim[Eli](10000)

        val removedNogoodsPerAtom = mutable.TreeMap[Eli /*atom eli*/ , ArrayBuffer[ArrayEliUnsafe]]()

        do {

          entry = false

          var posEli = 0

          while (posEli < noOfPosAtomElis) {

            if (!elimPosAtoms.contains(posEli)) {

              val negPosEli = negatePosEli(posEli)

              val resolvents = new ObjectArrayList[ArrayEliUnsafe]()

              var resolventsL = 0

              var pNogiIt = 0

              var resCount = 0

              val nogisWithPosEli = eliToNogisTemp(posEli).toIntArray

              val nogisWithNegPosEli = eliToNogisTemp(negPosEli).toIntArray

              var pncLits = 0

              var resLits = 0

              @inline def ccbs = {

                var pIt = nogisWithPosEli.length - 1

                var nIt = nogisWithNegPosEli.length - 1

                val res = new IntOpenHashSet()

                if (pIt * nIt < productPosNegLitsOrigCap)
                  while (pIt >= 0) {
                    {

                      val pNogi: Nogi = nogisWithPosEli(pIt)

                      if (!removedNogis.contains(pNogi)) {

                        nIt = nogisWithNegPosEli.length - 1

                        while (nIt >= 0) {
                          {

                            val nNogi: Nogi = nogisWithNegPosEli(nIt)

                            if (!removedNogis.contains(nNogi)) {

                              val pNogood: ArrayEliUnsafe = cns1(pNogi)

                              val nNogood: ArrayEliUnsafe = cns1(nNogi)

                              res.clear()

                              //res.sizeHint(pNogood.length + nNogood.length - 2)

                              pncLits += /*(nNogood.toArray ++ pNogood.toArray).distinct.length*/ nNogood.size() + pNogood.size()

                              var ik = pNogood.size() - 1

                              var jk = nNogood.size() - 1

                              if (ik == 1 && jk == 1) {

                                val res = Array.ofDim[Eli](2)

                                if (pNogood.get(0) == posEli)
                                  res(0) = pNogood.get(1)
                                else
                                  res(0) = pNogood.get(0)

                                if (nNogood.get(0) == negPosEli)
                                  res(1) = nNogood.get(1)
                                else
                                  res(1) = nNogood.get(0)

                                if (res(0) != negateEli(res(1))) {

                                  resLits += res.size

                                  resolvents.add(new ArrayEliUnsafe(res))

                                }

                              } else {

                                var isTaut = false

                                while (ik >= 0) {

                                  val lit = pNogood.get(ik)

                                  if (lit != posEli) {

                                    res.add(lit)

                                    resLits += 1

                                  }

                                  ik -= 1

                                }

                                while (jk >= 0 && !isTaut) {

                                  val lit = nNogood.get(jk)

                                  if (res.contains(negateEli(lit))) {

                                    isTaut = true

                                  } else if (lit != negPosEli) {

                                    res.add(lit)

                                    resLits += 1

                                  }

                                  jk -= 1

                                }

                                if (!isTaut) {

                                  //resLits += res.size

                                  resolvents.add(new ArrayEliUnsafe(res.toIntArray))

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

                val rmv = ArrayBuffer[ArrayEliUnsafe]()

                @inline def rmNogood(nogi: Nogi) = {

                  removedNogis.add(nogi)

                  rmv.append(cns1(nogi))

                }

                nogisWithPosEli.foreach(a => {

                  rmNogood(a)

                })

                nogisWithNegPosEli.foreach(a => {

                  rmNogood(a)

                })

                removedNogoodsPerAtom.put(posEli, rmv)

                //println("  -Eliminated positive eli (variable) " + eli + "  [negated: " + negatePosEli(eli) + "]")

              }

              val resolventsA: ObjectArrayList[ArrayEliUnsafe] = resolvents

              @inline def adc2 = {

                resolventsA.forEach { a /*: ObjectCursor[ArrayEliUnsafe]*/ => {

                  val resolvent = a //.value

                  val newNogi = cns1.length

                  val resolventA = resolvent

                  cns1.append(resolventA)

                  var k = resolventA.size - 1

                  while (k >= 0) {

                    eliToNogisTemp(resolventA.get(k)).add(newNogi)

                    k -= 1

                  }

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

              }

            }

            posEli += 1

          }

          maxElimIts -= 1

        } while (entry && maxElimIts > 0)

        val finalNogis = new mutable.HashSet[Eli]()

        val finalNogoods = ArrayBuffer[ArrayEliUnsafe]()

        eliToNogisTemp.foreach(nogis => nogis.toIntArray.foreach(a => if (!removedNogis.contains(a)) finalNogis.add(a)))

        finalNogis.foreach { a: Eli => finalNogoods.append(cns1(a /*.value*/)) }

        (finalNogoods, Some(removedNogoodsPerAtom))

      }

    val cns3: ArrayBuffer[ArrayEliUnsafe] = if (variableOrNogoodElimConfig._5 && removedNogoodsPerAtomOpt.isDefined) {

      assert(satMode) // TODO: make work with ASP (see "posHeadAtomToNegBlits =" below) or generatePseudoRulesForNogoodsForSATMode

      log("Removing eliminated elis...")

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

      val r = cns2.map(nogood => {

        val updatedNogood = new ArrayEliUnsafe(nogood.size())

        var i = 0

        while (i < nogood.size()) {

          val oldEli = nogood.get(i)

          assert(!removedPosElis.contains(oldEli))

          val newEli = if (isPosEli(oldEli)) {

            assert(!removedPosElis.contains(oldEli))

            eliChangeMap(oldEli)

          }
          else {

            assert(!removedPosElis.contains(negateNegEli(oldEli)))

            eliChangeMap(oldEli)

          }

          updatedNogood.update(i, newEli)

          i += 1

        }

        updatedNogood

      }

      )

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

    if (verbose && variableOrNogoodElimConfig._1) {

      println("Time variable elimination: " + timerToElapsedMs(startTimeVarElim) + "ms")

      println("K (clauses) after elimination: " + cns3.length + " (" + (cns3.length - cns1.length).toFloat / cns1.length.toFloat * 100f + "%)")

      val l = cns3.map(_.size()).sum

      println("L (literals) after elimination: " + l + " (" + (l - lorgno).toFloat / lorgno.toFloat * 100 + "%)")

      println("N (variables) after elimination: " + symbols.length + "(" + (symbols.length - oldN).toFloat / oldN.toFloat * 100f + "%)")
      if (!variableOrNogoodElimConfig._5) println("  (note: material variable elimination is off)")

    }

    (cns3.toArray, removedNogoodsPerAtomOpt)

  }

  //@Contended
  val clarkNogoods: Array[ArrayEliUnsafe] = if (!initCleanUpSortClarkNogoods) clarkNogoods2 else {

    clarkNogoods2.foreach(

      ng => {

        ng.distinctSorted

        ng.isSorted = true

      })

    //val noVarOccurrences = Array.ofDim[Int](noOfAllElis)

    //clarkNogoods2.foreach(_.toArray().foreach(noVarOccurrences(_) += 1))

    val r = clarkNogoods2.distinct //.sortBy(-_.size_)

    //val r = clarkNogoods2.distinct.sortBy(ng => ng.toArray().map(noVarOccurrences(_)).sum)

    /*val r = clarkNogoods2.distinct.map(ngus => {

      val ng = ngus.toArray

      new ArrayEliUnsafe(util.Random.shuffle(ng.toVector).toArray)

    })*/

    r.foreach(

      ng => {

        ng.isSorted = false

      })

    if (verbose) {

      println("#initial nogoods before cleanup: " + clarkNogoods2.length)

      println("   after cleanup: " + r.length)

    }

    r

  }

  val dependencyGraph: Int2ObjectOpenHashMap[List[Eli]] = if (satMode) new Int2ObjectOpenHashMap[List[Eli]]() else rulesOpt.map(rules =>
    computeDependencyGraph(rules, noOfPosAtomElis)).getOrElse(new Int2ObjectOpenHashMap[List[Eli]]())

  val progIsTight: Boolean = if (satMode) true else isAcyclic(dependencyGraph)

  if (!satMode) (if (progIsTight && verbose) println("\nProgram is tight") else if (verbose) println("\nProgram is not tight"))

  //@Contended
  val costFctsInnerWithPossMeasuredElis = mutable.HashMap[Eli, DifferentialFunction[DoubleReal]]() //ArrayBuffer[(DifferentialFunction[DoubleReal], Eli /*measured*/ )]()
  //Note ^: the mapping eli->innerCost is needed only for the simplified MSE case (where we use simplified derivation formulas, see further below)

  //@Contended
  val nablasInner /*partial derivatives of the inner cost functions*/ : Array[DifferentialFunction[DoubleReal]] =
    Array.fill[DifferentialFunction[DoubleReal]](symbols.length /*if we could place
          the uncertain atoms at the beginning of symbols, we could keep this array smaller, but this would require costly re-ordering operations
          in aspifParse() */)(null.asInstanceOf[DifferentialFunction[DoubleReal]])

  val dFFactory = new diff.DifferentialFunctionFactoryStasp()

  val parameterAtomVarForParamAtomEli_forPartDerivCompl = mutable.HashMap[Int, Variable[DoubleReal]]()

  //@Contended
  val symbolToEli: Predef.Map[String, Eli] = symbols.zipWithIndex.toMap

  val parameterAtomsElis0 /*(from  the "pats" line)*/ : Array[Eli] = costsOpt.map(_.parameterAtomsSeq).map(pmasg =>
    pmasg.map(pred => symbolToEli(pred))).getOrElse(Array[Eli]())

  @inline def measuredAtomNameInCostFnToSymbol(n: String): String = if (satMode) n.stripPrefix("v") else n

  @inline def translateDiffFunMeasuredAtomIndex2PosEli(index: Int): Eli = symbolToEli(measuredAtomNameInCostFnToSymbol(costsOpt.get.measuredAtomsSeq(index)))

  val measuredAtomsElis /*(from within the cost functions)*/ : Array[Eli] = costsOpt.map(_.measuredAtomsSeq).map(_.map(vn => symbolToEli(measuredAtomNameInCostFnToSymbol(vn)))).getOrElse(Array[Eli]())

  // TODO: no current use for measured atoms yet (since this version doesn't support, e.g., cost backtracking), we simply assume here that
  // they are identical with the parameter atoms.

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

        costFctsInnerWithPossMeasuredElis.put(possibleMeasuredEli, costFunInnerWithElis) //Note: the mapping eli->innerCost is needed
        // only for the simplified MSE case (where we use simplified derivation formulas, see further below)

        log("Translated costFctsInner(measuredAtomEli): " + costFunInnerWithElis)

      })

    })

  }

  log("\npreptimer 2.1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  @inline def findInnerCostFunForParameterAtom(parameterAtomEli: Eli): Option[DifferentialFunction[DoubleReal]] = {

    costFctsInnerWithPossMeasuredElis.get(parameterAtomEli) //costFctsInnerWithPossMeasuredElis.find(_._2 == parameterAtomEli)

  }

  log("\npreptimer 3: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val parameterAtomsElis = parameterAtomsElis0.filter(parameterAtomVarForParamAtomEli_forPartDerivCompl.contains(_))
  // ^the above ensures we only keep parameter atoms which occur as measured atoms in cost formulas (TODO: remove as soon as
  // delSAT supports disjoint param vs. measured)

  val innerCostFunForParamAtomEli = if (ignoreParamVariables || partDerivComplete) mutable.Map[Eli, Option[DifferentialFunction[DoubleReal]]]() else
    mutable.HashMap[Eli, Option[DifferentialFunction[DoubleReal]]]().++(parameterAtomsElis.map(eli => {

      eli -> findInnerCostFunForParameterAtom(eli)

    }).toMap)

  log("\npreptimer 4: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  @Contended
  val costFctsInner = costFctsInnerWithPossMeasuredElis.values.toArray //costFctsInnerWithPossMeasuredElis.unzip._1

  val n = dFFactory.`val`(new DoubleReal(costFctsInner.length.toDouble))

  val totalCostFun_forPartDerivCompl: DifferentialFunction[DoubleReal] = if (costFctsInner.isEmpty) dFFactory.`val`(new DoubleReal(-1 /*dummy*/)) else
    costFctsInner.reduceLeft((reduct: DifferentialFunction[DoubleReal], addendum: DifferentialFunction[DoubleReal])
    => reduct.plus(addendum)).div(n)

  if (!ignoreParamVariables)
    parameterAtomsElis.foreach(parameterAtomEli => { // this probably only makes sense if parameter atoms == measured atoms...!

      val parameterAtomVar: Variable[DoubleReal] = parameterAtomVarForParamAtomEli_forPartDerivCompl(parameterAtomEli)

      if (partDerivComplete) { // see M. Nickles: PLP'18 paper; use with non-MSE cost functions (more general but slower)

        nablasInner(parameterAtomEli) = totalCostFun_forPartDerivCompl.diff(parameterAtomVar)

      } else { // faster, less general. For simple MSE-style (and some others?) cost functions. See M. Nickles: ILP'18 paper.

        val innerCostFun: DifferentialFunction[DoubleReal] = innerCostFunForParamAtomEli /*findInnerCostFunForParameterAtom*/ (parameterAtomEli).getOrElse {

          stomp(-5003)

          costFctsInner(0)

        }

        nablasInner(parameterAtomEli) = innerCostFun.diff(parameterAtomVar)

      }

      log("nablasInner for parameter atom " + /*symbols*/ (parameterAtomEli) + ": " + nablasInner(parameterAtomEli))

    })

  log("\npreptimer 5: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val parameterAtomsElisSet: Set[Eli] = parameterAtomsElis.toSet

  //@Contended
  val parameterLiteralElis: Array[Eli] = parameterAtomsElis ++ parameterAtomsElis.map(negatePosEli(_))

  @inline def deficitByDeriv(parameterLiteralEli: Eli): Double = {

    // Assumes that in a step directly preceding the re-sorting, the variables in the nablaInner have been
    // updated to measuredAtomEliToStatisticalFreq!

    (if (isPosAtomEli(parameterLiteralEli))
      nablasInner(parameterLiteralEli).getReal
    else
      -nablasInner(negateNegEli(parameterLiteralEli)).getReal)

  }

  val deficitOrdering: Ordering[Integer /*actually a parameter eli*/ ] =
    Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {

      deficitByDeriv(parameterLiteralEli)

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

  val ruliformNogiToNegBlits = new Int2ObjectOpenHashMap[Array[Eli /*negative blit*/ ]]() // only needed for non-tight ASP programs

  val eliToNogisBuilder = Array.fill(noOfAllElis)(new mutable.ArrayBuilder.ofInt)

  val eliToNogisClark: Array[ArrayValExtensibleIntUnsafe] = Array.ofDim[ArrayValExtensibleIntUnsafe](noOfAllElis) // per each eli, all nogis which contain that eli

  var nogj = 0

  val cnl = clarkNogoods.length

  while (nogj < cnl) {

    val clarkNogood: Array[Eli] = clarkNogoods(nogj).toArray

    if (!progIsTight) {

      val posAtoms = clarkNogood.filter(isPosAtomEli(_))

      if (posAtoms.length == 1) {

        val ruleHeadAtom = posAtoms.head

        val negBlitsForHead: Array[Eli] = posHeadAtomToNegBlits.get(ruleHeadAtom)

        if (negBlitsForHead != null)
          ruliformNogiToNegBlits.put(nogj, negBlitsForHead)

      }

    }

    clarkNogood.foreach(eliInNogood => {

      eliToNogisBuilder(eliInNogood).+=(nogj)

    })

    nogj += 1

  }

  var elk = 0

  while (elk < noOfAllElis) {

    eliToNogisClark(elk) = new ArrayValExtensibleIntUnsafe(eliToNogisBuilder(elk).result())

    elk += 1

  }

  @Contended
  var absEliActiv = new FloatArrayUnsafe(noOfPosElis, true) //new ArrayEliUnsafe(noOfPosElis) // similar to BerkMin's var_activity; must be global (and yes, we are accessing this sometimes without synchronization)

  val elisArrangedR: Array[Eli] = if (freeEliSearchConfigsP.contains(7)) (0 until noOfAllElis).toArray else Array[Int]()

  if (delSAT.verbose)
    println("\nPreparation time: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  def computeClarkNogis(rules: ArrayBuffer[Rule]): (Array[ArrayEliUnsafe], java.util.HashMap[Eli, Array[Eli]], java.util.HashMap[Eli, Array[Eli]]) = {

    // Nogood generation follows (with a few minor differences) https://www.cs.uni-potsdam.de/wv/pdfformat/gekanesc07a.pdf

    // NB: the following algorithm assumes that all rules are normal. E.g., :- integrity constraints are not allowed (need
    // to be preprocessed, see AspifParser).

    // NB: in SATmode, we can end up in this method only with experimental flag generatePseudoRulesForNogoodsForSATMode = true,
    // otherwise in SAT mode all nogoods have already been generated entirely from the CNF clauses.

    val exclEmptyBodyInDeltaAtoms = resolveFactsInitially // true simplifies nogoods from empty bodies, but without prior resolution during solving it can also increase solving time (simpler != easier)

    val test = false // must be false (true for debugging purposes only)

    val thresholdForSymbolsPar = 1000000

    val thresholdForRulesPar = 1000000

    val noOfThreads = 4

    @deprecated val createFalsNgs: Boolean = false

    val specialConstrRuleNogoods: Boolean = false // TODO: must be false (true doesn't work yet); if true, we create an alternative form of nogoods for :- constraints (see code)

    val rulesWoConstr = if (!specialConstrRuleNogoods) rules else /*we create special nogoods later for the omitted ones: */
      rules.filterNot(rule => isPosEli(rule.headAtomsElis.head) && isFalsAuxAtom(symbols(rule.headAtomsElis.head)))

    val noOfThreadsNg = if (rulesWoConstr.length < thresholdForRulesPar) 1 else noOfThreads

    val rulesPartitioning: Iterator[ArrayBuffer[Rule]] = if (rulesWoConstr.isEmpty) Iterator(ArrayBuffer[Rule]()) else rulesWoConstr.grouped(if (noOfThreadsNg == 1 || rulesWoConstr.length < noOfThreadsNg - 1) rulesWoConstr.length else rulesWoConstr.length / (noOfThreadsNg - 1))

    val negBlitToPosBodyElis: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    val posHeadAtomToNegBlits: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // ^ we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    log("\npreptimer0: " + timerToElapsedMs(timerPrepNs) + " ms\n")

    def deltaBetaPartComp(rulesPart: ArrayBuffer[Rule]): ArrayBuffer[ArrayEliUnsafe] = { // generate body nogoods

      val deltaBetaPart = mutable.ArrayBuffer[ArrayEliUnsafe]()

      //deltaBetaPart.sizeHint(rulesWoConstr.length * 5 + 1000)

      var ri = 0

      val rpl = rulesPart.length

      while (ri < rpl) {

        val rule = rulesPart(ri)

        val bpos: Array[Eli] = rule.bodyPosAtomsElis

        val bneg: Array[Eli] = rule.bodyNegAtomsElis

        if (!test || bpos.length > 0 || bneg.length > 0) {

          val blit = rule.blit // the blit of the rule. NB: if omitSingletonBlits, this is an ordinary (non body) eli if there's just one body literal

          val blitNegated = negateEli(blit)

          val s1: Array[Eli] = Array.ofDim[Eli](bpos.length + bneg.length + 1)

          bpos.copyToArray(s1, 0)

          bneg.copyToArray(s1, bpos.length)

          s1(s1.length - 1) = blitNegated

          deltaBetaPart.append(new ArrayEliUnsafe(s1)) // δ(β)

          negBlitToPosBodyElis.put(blitNegated, bpos)

          val s2pos: Array[ArrayEliUnsafe] = bpos.map(eli => new ArrayEliUnsafe(Array(blit, negatePosEli(eli))))

          deltaBetaPart.appendAll(s2pos) // Δ(β)

          val s2neg: Array[ArrayEliUnsafe] = bneg.map(eli => new ArrayEliUnsafe(Array(blit, negateNegEli(eli))))

          deltaBetaPart.appendAll(s2neg) // Δ(β)

        }

        ri += 1

      }

      log("\npreptimer1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

      deltaBetaPart

    }

    def deltaAtomsComp(omit: Boolean): mutable.ArrayBuffer[ArrayEliUnsafe] = { // generate head/atom-related nogoods

      val deltaAtoms = mutable.ArrayBuffer[ArrayEliUnsafe]()

      if (!omit) {

        //deltaAtoms.sizeHint(symbols.length * 5 + 1000)

        log("\npreptimer2a: " + timerToElapsedMs(timerPrepNs) + " ms\n")

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

        log("\npreptimer2b: " + timerToElapsedMs(timerPrepNs) + " ms\n")

        val zeroToSymLen = (0 until noOfPosAtomElis) ++ (posNegEliBoundary until posNegEliBoundary + noOfPosAtomElis)
        // ^ all positive and negative literals except blits. Note that negative head lits should not (yet) occur in ASP mode, these
        // are only generated in pseudo-rules in SAT-mode.

        (if (zeroToSymLen.size > thresholdForSymbolsPar) zeroToSymLen.par else zeroToSymLen).flatMap { atomEli_p => {

          // TODO: We should optionally treat #external atoms here specially, even if they don't occur in any rules, in which case nogoods are generated for them to ensure they are never true.

          val bodiesOfp: ArrayBuffer[Rule] = rulesGroupedByTheirHeadEli(atomEli_p) // NB: this also includes empty bodies!

          val s1s2 = ArrayBuffer[ArrayEliUnsafe]()

          var isFact = false

          if (!satMode /*see above*/ || !bodiesOfp.isEmpty) {

            if (bodiesOfp.isEmpty && isPosEli(atomEli_p) && !symbols(atomEli_p).startsWith(auxPredPrefixBase))
              stomp(-5005, symbols(atomEli_p))

            s1s2.sizeHint(bodiesOfp.length + 1)

            if (!bodiesOfp.isEmpty) {

              val negHeadAtomEli: Eli = negateEli(atomEli_p)

              bodiesOfp.foreach(rule => { // Δ(p)

                s1s2.append(if (exclEmptyBodyInDeltaAtoms && (
                  rule.blit == emptyBodyBlit) || isFact) {

                  isFact = true

                  new IntArrayUnsafe(Array(negHeadAtomEli))

                } else
                  new IntArrayUnsafe(Array(negHeadAtomEli, rule.blit)))

              })

            }

            // TODO:  handle #external atoms here (currently ignored / treated as undefined unless defined by some rule):
            if (((bodiesOfp.length > 1 || bodiesOfp.length == 1 && bodiesOfp.head.blit != emptyBodyBlit))) { // δ(p)
              // (^ in satMode (which normally doesn't use this method anyway, see above), this branch is only allowed if we
              // create _all_ possible pseudo-rules (for all clauses and heads), otherwise the following can lead to wrong UNSAT:)

              val s2NogoodBuffer = new IntArrayUnsafe(bodiesOfp.length + 1) //Array.ofDim[Eli](bodiesOfp.length + 1)

              var s2i = 0

              bodiesOfp.foreach(rule => { // ? note: if we do this even if bodiesOfp is empty, which creates false-enforcing nogoods for undefined symbols

                s2NogoodBuffer.update(s2i, negateEli(rule.blit))

                s2i += 1

              })

              s2NogoodBuffer(s2i) = atomEli_p

              posHeadAtomToNegBlits.put(atomEli_p, s2NogoodBuffer.toArray(0, s2i))

              s1s2.append(s2NogoodBuffer)

            }

            Some(s1s2) //.distinct

          } else
            None

        }
        }.seq.foreach(deltaAtoms.appendAll(_))

        log("\npreptimer2: " + timerToElapsedMs(timerPrepNs) + " ms\n")

      }

      deltaAtoms

    }

    val deltaClark: mutable.ArrayBuffer[ArrayEliUnsafe] = if (noOfThreadsNg == 1) {

      val rulesOnlyPart = rulesPartitioning.next()

      assert(rulesOnlyPart.length == rulesWoConstr.length)

      deltaBetaPartComp(rulesOnlyPart) ++ deltaAtomsComp(omitAtomNogoods)

    } else {

      implicit val executor = scala.concurrent.ExecutionContext.global

      val deltaBetaFutures: Iterator[Future[ArrayBuffer[ArrayEliUnsafe]]] = rulesPartitioning.map((rulesPart: ArrayBuffer[Rule]) => Future {

        deltaBetaPartComp(rulesPart)

      }(executor))

      val deltaAtomsFuture = Future {

        deltaAtomsComp(omitAtomNogoods)

      }(executor)

      val deltas: ArrayBuffer[ArrayBuffer[ArrayEliUnsafe]] = Await.result(Future.sequence(Seq(deltaAtomsFuture) ++ deltaBetaFutures), Duration.Inf).to[ArrayBuffer]

      deltas.flatten

    }

    val falsNogoods: ArrayBuffer[ArrayEliUnsafe] = if (createFalsNgs)
      symbolsWithIndex.filter(si => isFalsAuxAtom(si._1)).map(x => new ArrayEliUnsafe(Array(x._2))).to[ArrayBuffer]
    else if (!specialConstrRuleNogoods) ArrayBuffer[ArrayEliUnsafe]() else {

      // we add special nogoods for rules which have been (elsewhere) resulted from constraints :- b1, b2, ...

      val contraintRules = rules.filter(rule => isPosAtomEli(rule.headAtomsElis.head) && isFalsAuxAtom(symbols(rule.headAtomsElis.head)))

      contraintRules.map(rule => new ArrayEliUnsafe(rule.bodyPosAtomsElis ++ rule.bodyNegAtomsElis.filterNot(_ == negateEli(rule.headAtomsElis.head))))

    }

    log("# special constraint rule nogoods = " + falsNogoods.length)

    val r = deltaClark ++ falsNogoods

    (r.toArray, posHeadAtomToNegBlits, negBlitToPosBodyElis)

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

    val rules = ruless.filter(r => !(r.blit == emptyBodyBlit && r.headAtomsElis.isEmpty && r.bodyNegAtomsElis.isEmpty) /*<- dummy rules " :- "*/)

    val r1: Seq[Rule] = rules.filterNot {
      _.bodyNegAtomsElis.exists(negEli /* modelCandidate contains positive atomic elis only, so we need to check for negated negEli: */ => {

        val x = negateNegEli(negEli)

        modelCandidate._2.contains(x)

      }
      )
    }

    val reduct: Seq[Rule] = r1.map(r => new Rule(headAtomsElis = r.headAtomsElis,
      bodyPosAtomsElis = r.bodyPosAtomsElis, bodyNegAtomsElis = Array[Eli](), blit = -1)) // Gelfond-Lifschitz reduct

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

  def computeDependencyGraph(rules: ArrayBuffer[Rule], noOfAllPosAtomElis: Int): Int2ObjectOpenHashMap[List[Eli]] = {

    var graphInit = new Int2ObjectOpenHashMap[List[Eli]]()

    var jj = 0

    while (jj < rules.length) {

      val rule = rules(jj)

      if (!rule.headAtomsElis.isEmpty) {

        val headEli = rule.headAtomsElis.head

        if (!isPosEli(headEli))
          stomp(-5004, rule.toString)

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

  @tailrec final def isAcyclic(depGraph: Int2ObjectOpenHashMap[List[Eli]]): Boolean = {

    depGraph.isEmpty || {

      val leaveElisB = new mutable.ArrayBuilder.ofInt

      val nonLeaveGraphPart = ArrayBuffer[(Eli, List[Eli])]()

      val graphEntries: IntSet /*: Int2ObjectOpenHashMap[List[Eli]]#KeysContainer*/ = depGraph.keySet()

      val graphEntriesIterator = graphEntries.iterator()

      while (graphEntriesIterator.hasNext()) {

        val key = graphEntriesIterator.nextInt()

        val v: List[Eli] = depGraph.get(key)

        if (v.isEmpty)
          leaveElisB.+=(key)
        else
          nonLeaveGraphPart.append((key, v))

      }

      val leaveElis = leaveElisB.result()

      !leaveElis.isEmpty && {

        val strippedGraph = new Int2ObjectOpenHashMap[List[Eli]]()

        nonLeaveGraphPart.foreach((keyValues: (Eli, List[Eli])) => {

          strippedGraph.put(keyValues._1, keyValues._2.filterNot((eli: Eli) => leaveElis.contains(eli)))

        })

        isAcyclic(strippedGraph)

      }

    }

  }

}
