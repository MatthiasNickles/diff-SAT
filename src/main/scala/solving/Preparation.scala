/**
  * delSAT
  *
  * Copyright (c) 2018,2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package solving

import java.io.PrintWriter
import java.util

import aspIOutils._
import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, PolynomialTerm, Sum, Variable}
import commandlineDelSAT.delSAT
import commandlineDelSAT.delSAT._
import diff.UncertainAtomsSeprt
import it.unimi.dsi.fastutil.ints.{Int2ObjectMap, Int2ObjectOpenHashMap, IntOpenHashSet, IntSet}
import it.unimi.dsi.fastutil.objects.ObjectArrayList

import sharedDefs._
import utils.IntArrayUnsafeS

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Iterator, Seq, mutable}
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}

/**
  * Various preparation steps before actual solving and sampling starts.
  *
  * @author Matthias Nickles
  *
  */
class Preparation(val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult,
                  val costsOpt: Option[UncertainAtomsSeprt],
                  satModeR: Boolean,
                  omitAtomNogoods: Boolean /*for testing purposes only*/) {

  assert(!omitAtomNogoods)

  var posNegEliBoundary: Int = -1

  var noOfAllElis: Int = -1

  var noOfPosElis: Int = -1

  var assgnmFullSize: Int = -1

  val satMode = satModeR

  val timerPrepNs = System.nanoTime()

  val rulesOpt: Option[ArrayBuffer[Rule]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.left.toOption

  val dimacsClauseNogoodsOpt: Option[Array[IntArrayUnsafeS]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.right.toOption

  var symbols = aspifOrDIMACSParserResult.symbols

  var symbolsWithIndex: Array[(String, Int)] = null.asInstanceOf[Array[(String, Int)]]

  var noOfPosAtomElis: Int = -1

  var noOfPosBlits: Int = aspifOrDIMACSParserResult.noOfPosBlits

  var posNegEliBoundaryM1: Int = -1

  var emptyBodyBlit: Eli = aspifOrDIMACSParserResult.emptyBodyBlit

  var noOfAllElisM1 = -1

  def setFoundStructures = {

    symbolsWithIndex = symbols.zipWithIndex

    noOfPosAtomElis = symbols.length

    posNegEliBoundary = noOfPosAtomElis + noOfPosBlits // benefit of this literal representation: we can use elis directly (without offset) as indices into arrays

    noOfAllElis = posNegEliBoundary * 2

    noOfAllElisM1 = (1 << binLog(noOfAllElis)) - 1

    posNegEliBoundaryM1 = (1 << binLog(posNegEliBoundary)) - 1

    assgnmFullSize = posNegEliBoundary

    assert(assgnmFullSize == noOfAllElis / 2)

    noOfPosElis = assgnmFullSize

  }

  setFoundStructures

  @inline def isPosAtomEli(eli: Eli): Boolean = eli < noOfPosAtomElis

  @inline def isPosEli(eli: Eli): Boolean = eli < posNegEliBoundary

  @inline def isNegEli(eli: Eli): Boolean = eli >= posNegEliBoundary

  @inline def negateEli(eli: Eli): Eli = {

    if (eli < posNegEliBoundary)
      eli + posNegEliBoundary
    else
      eli - posNegEliBoundary

  }

  @inline def negatePosEli(eli: Eli): Eli = eli + posNegEliBoundary

  @inline def negateNegEli(eli: Eli): Eli = eli - posNegEliBoundary

  @inline def toAbsEli(eli: Eli): Eli = {

    if (eli < posNegEliBoundary)
      eli
    else
      eli - posNegEliBoundary

  }

  @inline def isFactEli(eli: Eli): Boolean = eli < noOfPosAtomElis || eli >= posNegEliBoundary && eli < posNegEliBoundary + noOfPosAtomElis

  @inline def isBlit(eli: Eli): Boolean = !isFactEli(eli)

  var posHeadAtomToNegBlits = new java.util.HashMap[Eli, Array[Eli]]() // for non-tight ASP only

  var negBlitToPosBodyElis = new java.util.HashMap[Eli /*negative blit*/ , Array[Eli]]() // for non-tight ASP only

  val clarkNogoods1: Array[IntArrayUnsafeS] = dimacsClauseNogoodsOpt.getOrElse {

    val rules = rulesOpt.get

    val (cngs1: Array[IntArrayUnsafeS], pHatomNegBlits: java.util.HashMap[Eli, Array[Eli]], bpbes: java.util.HashMap[Eli, Array[Eli]]) =
      computeClarkNogis(rules)

    posHeadAtomToNegBlits = pHatomNegBlits

    negBlitToPosBodyElis = bpbes

    val cngs2 = if (aspifOrDIMACSParserResult.directClauseNogoodsOpt.isDefined) {

      if (verbose)
        println("#extra nogoods from pseudo-rules (in addition to direct clauses nogoods): " + cngs1.length)

      aspifOrDIMACSParserResult.directClauseNogoodsOpt.get ++ cngs1

    } else cngs1

    val cngs3 = cngs2 ++ aspifOrDIMACSParserResult.assumptionElis.map(aEli =>
      new IntArrayUnsafeS(Array(negateEli(aEli)), aligned = false) // if aEli is positive, this corresponds to constraint
      // :- not aEli.
      // if aEli is a negative literal, this corresponds to :- negate(aEli), i.e., the same.

    )

    cngs3

  }

  val (clarkNogoods2: Array[IntArrayUnsafeS], removedNogoodsPerAtomOpt) = {

    val cns1: ArrayBuffer[IntArrayUnsafeS] = clarkNogoods1.to[ArrayBuffer]

    lazy val lorgno = cns1.map(_.size()).sum

    lazy val oldN = symbols.length

    if (verbose && variableOrNogoodElimConfig._1) {

      println("K-org (clauses): " + cns1.length) // original #clauses

      println("L-org (literals, with duplicates): " + lorgno) // original #literals (toAbsEli.e. elis in our case)

      println("N-org (variables): " + oldN) // original #symbols (variables)

    }

    val startTimeVarElim = System.nanoTime()

    val (cns2: ArrayBuffer[IntArrayUnsafeS], removedNogoodsPerAtomOpt: Option[mutable.TreeMap[Eli /*atom eli (variable)*/ , ArrayBuffer[IntArrayUnsafeS]]]) =
      if (!variableOrNogoodElimConfig._1) (cns1, None) else { // static variable elimination

        // TODO (improvement opportunities):

        val removedNogis = new IntOpenHashSet()

        val productPosNegLitsOrigCap = (Math.sqrt(cns1.length.toDouble) * variableOrNogoodElimConfig._4).toInt

        val noOfResolventsOverheadCap = (cns1.length.toDouble * variableOrNogoodElimConfig._2).toInt

        val noOfOriginalLitsOverheadCap = (noOfAllElis.toDouble * variableOrNogoodElimConfig._3).toInt

        val eliToNogisTemp = Array.fill[IntOpenHashSet](noOfAllElis)(new IntOpenHashSet())

        var nogi = cns1.length - 1

        while (nogi >= 0) {

          val nogood: IntArrayUnsafeS = cns1(nogi)

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

        //var pnNogood = Array.ofDim[Eli](8192)

        val removedNogoodsPerAtom = mutable.TreeMap[Eli /*atom eli*/ , ArrayBuffer[IntArrayUnsafeS]]()

        do {

          entry = false

          var posEli = 0

          while (posEli < noOfPosAtomElis) {

            if (!elimPosAtoms.contains(posEli)) {

              val negPosEli = negatePosEli(posEli)

              val resolvents = new ObjectArrayList[IntArrayUnsafeS]()

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

                              val pNogood: IntArrayUnsafeS = cns1(pNogi)

                              val nNogood: IntArrayUnsafeS = cns1(nNogi)

                              res.clear()

                              //sampledModels.sizeHint(pNogood.length + nNogood.length - 2)

                              pncLits += nNogood.size() + pNogood.size()

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

                                  resolvents.add(new IntArrayUnsafeS(res, aligned = false))

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

                                  //resLits += sampledModels.size

                                  resolvents.add(new IntArrayUnsafeS(res.toIntArray, aligned = false))

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

                val rmv = ArrayBuffer[IntArrayUnsafeS]()

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

              }

              val resolventsA: ObjectArrayList[IntArrayUnsafeS] = resolvents

              @inline def adc2 = {

                resolventsA.forEach { a /*: ObjectCursor[IntArrayUnsafeS]*/ => {

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

        val finalNogis = new IntOpenHashSet()

        val finalNogoods = ArrayBuffer[IntArrayUnsafeS]()

        eliToNogisTemp.foreach(nogis => nogis.toIntArray.foreach(a => if (!removedNogis.contains(a)) finalNogis.add(a)))

        val fni = finalNogis.iterator

        while (fni.hasNext)
          finalNogoods.append(cns1(fni.nextInt()))

        (finalNogoods, Some(removedNogoodsPerAtom))

      }

    val cns3: ArrayBuffer[IntArrayUnsafeS] = if (variableOrNogoodElimConfig._5 && removedNogoodsPerAtomOpt.isDefined) {

      assert(satMode) // TODO: make work with ASP (see "posHeadAtomToNegBlits =" below) or generatePseudoRulesForNogoodsForSATMode

      if (!satMode) {

        stomp(-5006)

      }

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

        val updatedNogood = new IntArrayUnsafeS(nogood.size(), aligned = false)

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

      val kDiff = cns3.length - cns1.length

      println("K (clauses) after elimination stage: " + cns3.length + " (" + (if (kDiff > 0) "+" else "") + kDiff.toFloat / cns1.length.toFloat * 100f + "%)")

      val l = cns3.map(_.size()).sum

      val lDiff = l - lorgno

      println("L (literals) after elimination stage: " + l + " (" + (if (lDiff > 0) "+" else "") + lDiff.toFloat / lorgno.toFloat * 100 + "%)")

      val nDiff = symbols.length - oldN

      println("N (variables) after elimination stage: " + symbols.length + " (" + (if (nDiff > 0) "+" else "") + nDiff.toFloat / oldN.toFloat * 100f + "%)")
      if (!variableOrNogoodElimConfig._5) println("  (note: material variable elimination is off)")

    }

    (cns3.toArray, removedNogoodsPerAtomOpt)

  }

  val clarkNogoods: Array[IntArrayUnsafeS] = if (!initCleanUpArrangeClarkNogoods) clarkNogoods2 else {

    val ab = new mutable.ArrayBuilder.ofRef[IntArrayUnsafeS]

    val seen = new mutable.HashSet[IntArrayUnsafeS]()

    var isDifferent = false

    clarkNogoods2.foreach(

      ng => {

        ng.distinctSorted()

        ng.isSorted = true

        if (seen.add(ng))
          ab += ng
        else
          isDifferent = true

      })

    if (isDifferent)
      ab.result
    else
      clarkNogoods2

  }

  val positiveDependencyGraph: Int2ObjectOpenHashMap[List[Eli]] = if (satMode) new Int2ObjectOpenHashMap[List[Eli]]() else rulesOpt.map(rules => {

    if (debug) {

      println("Rules extracted from aspif:\n")

      println(rules.map(_.toString(this)).mkString("\n"))

      println("-----------\n")

    }

    computeDependencyGraph(rules, noOfPosAtomElis)

  }).getOrElse(new Int2ObjectOpenHashMap[List[Eli]]())

  val progIsTight: Boolean = if (satMode) true else isAcyclic(positiveDependencyGraph)

  if (!satMode) (if (progIsTight && verbose) println("\nProgram is tight") else if (verbose) println("\nProgram is not tight"))

  val displayDepGraph = false

  if (displayDepGraph) { // for debugging purposes

    val emitDepGraphPosNeg = true

    val reverseDepGraph = false

    val showEdgeLabels = true

    val showNotAsEdgeLabelOnly = true

    val showNegEdgesInRed = true

    assert(!satMode)

    val dependencyGraph: Int2ObjectOpenHashMap[List[Eli]] = rulesOpt.map(rules => {

      computeDependencyGraph(rules, noOfPosAtomElis, positiveDepGraph = false)

    }).getOrElse(new Int2ObjectOpenHashMap[List[Eli]]())

    val nodesForDot = ArrayBuffer[String]()

    val edgesForDot = ArrayBuffer[String]()

    def eliToStr(eli: Eli) = (if (isPosEli(eli)) symbols(eli) else "not " + symbols(negateNegEli(eli)))

    val nodesAsElis: IntSet = dependencyGraph.keySet

    val nit = nodesAsElis.iterator

    while (nit.hasNext) { // all rule heads (must be positive, negative heads should have already been translated away by this point)

      val nodeEli = nit.nextInt()

      assert(isPosEli(nodeEli), "Error: negative head elis in aspif not supported")

      val nodeStr = nodeEli.toString

      nodesForDot.append(nodeStr + " [label=\"" + symbols(nodeEli) + "\"]")

      println("Node added for eli: " + nodeStr)

    }

    val dges = dependencyGraph.int2ObjectEntrySet

    val dgesit = dges.iterator

    while (dgesit.hasNext) {

      val dge: Int2ObjectMap.Entry[List[Eli]] = dgesit.next()

      val parentNodeEli = dge.getIntKey

      println("parentNodeEli: " + parentNodeEli + "(" + symbols(parentNodeEli) + ")")

      print("   descendants: ")

      val descendantElis: Seq[Eli] = dge.getValue

      val deit = descendantElis.iterator

      while (deit.hasNext) {

        val descendantEli = deit.next()

        print(descendantEli + "(" + eliToStr(descendantEli) + "), ")

        val edgeStr = symbols(parentNodeEli) + (if (reverseDepGraph) "<-" else "->") + eliToStr(descendantEli)

        val edgeForDot = (if (reverseDepGraph) toAbsEli(descendantEli) + " -> " + parentNodeEli else parentNodeEli + " -> " + toAbsEli(descendantEli)) +
          (if (showEdgeLabels) " [label=\"" + (if (showNotAsEdgeLabelOnly) (if (isNegEli(descendantEli)) "not" else "") else edgeStr) + "\"]" else "") + (if (showNegEdgesInRed && isNegEli(descendantEli)) " [color=red]" else "")
        // NB: Mathematica doesn't show red color or other style attriibutes for edges imported from DOT (but parses these into Graph format!)

        edgesForDot.append(edgeForDot)

        //println("toAbsEli(descendantEli): " + toAbsEli(descendantEli))

      }

      println

    }

    if (emitDepGraphPosNeg) {

      println("Writing depGraphPosNeg to .dot file (open with, e.g., GraphViz)")

      val dotGraphStr = "digraph dependencyGraphPosNeg {\n" + nodesForDot.mkString("\n") + "\n" + edgesForDot.mkString("\n") + "\n}"

      new PrintWriter("depGraphPosNeg.dot") {

        write(dotGraphStr)

        close

      }

      sys.exit(0)

    }

    readChar()

    sys.exit(0)

  }

  val costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE = mutable.HashMap[Eli, DifferentialFunction[DoubleReal]]()
  // Note ^: this is needed only for the simplified (faster) approach where each partial derivative is computed from an inner cost
  // term, e.g., in case of MSE. I.e., with --solverarg "partDerivComplete" "false"

  val nablasInner /*partial derivatives of the inner cost functions wrt. parameter atoms (as freqx variables)*/ : Array[DifferentialFunction[DoubleReal]] =
    Array.fill[DifferentialFunction[DoubleReal]](symbols.length /*if we could place
          the uncertain atoms at the beginning of symbols, we could keep this array smaller, but this would require costly re-ordering operations
          in aspifParse() */)(null.asInstanceOf[DifferentialFunction[DoubleReal]])

  val dFFactory = new diff.DifferentialFunctionFactoryStasp()

  val eliToVariableInCostFunctions: mutable.Map[Eli, Variable[DoubleReal]] = costsOpt.map(_.eliToVariableInCostFunctions).getOrElse(mutable.HashMap[Int, Variable[DoubleReal]]())
  // ^ for each measured eli, the corresponding autodiff.Variable within the inner cost. We can only differentiate wrt. parameter elis which are contained in this map.

  val symbolToEli: Predef.Map[String, Eli] = if (aspifOrDIMACSParserResult.symbolToEliOpt.isDefined && aspifOrDIMACSParserResult.symbols.length == symbols.length && !variableOrNogoodElimConfig._5)
    aspifOrDIMACSParserResult.symbolToEliOpt.get
  else
    symbols.zipWithIndex.toMap

  val parameterAtomsElis0 /*(from  the "pats" line)*/ : Array[Eli] = costsOpt.map(_.parameterAtomsSeq).map(pmasg =>
    pmasg.map(pred => symbolToEli(pred))).getOrElse(Array[Eli]())

  @inline def measuredAtomNameInCostFnToSymbol(n: String): String = if (satMode) n.stripPrefix("v") else n.replaceAllLiterally(" ", "")

  val measuredAtomsElis /*(from within the cost functions)*/ : Array[Eli] = costsOpt.map(_.measuredAtomsSeq).map(_.map((vn: Pred) =>
    symbolToEli(measuredAtomNameInCostFnToSymbol(vn)))).getOrElse(Array[Eli]())

  // NB: if a measured atom isn't (and shouldn't be made) a parameter atom, e.g., for learning the weight of a hypothesis, we can't _directly_
  // differentiate the cost wrt. a parameter atom (that is, the variable which represents its frequency), we cannot
  // influence the cost _directly_ by adding/omitting parameter atoms in models (see switch useNumericalFiniteDifferences).
  // In that case, we might still be able to influence the cost (i.e., the measured atom frequencies) indirectly via the parameter atoms.
  // NB: In case of weight learning, the parameter atoms are the hypotheses whose weights
  // we are looking for, and the measured atoms are the learning examples whose weights we are maximizing by influencing the hypotheses weights.

  @deprecated val hypothesisParamTargetWeightVariables = ArrayBuffer[(Eli, /*current target weight of hypothesis:*/ Variable[DoubleReal])]()

  var costFctsInner: Array[DifferentialFunction[DoubleReal]] = costsOpt.map(co => Array.ofDim[DifferentialFunction[DoubleReal]](co.innerCostExpressionInstances.length)).getOrElse(Array[DifferentialFunction[DoubleReal]]()) // = costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE.values.toArray

  var cfi = 0

  setCostFctsInner

  def setCostFctsInner = {

    costsOpt.foreach((inputDataCostFunBased: UncertainAtomsSeprt) => {

      inputDataCostFunBased.innerCostExpressionInstances.foreach((costFunInner: DifferentialFunction[DoubleReal]) => {

        val cStr = costFunInner.toString

        costFctsInner(cfi) = costFunInner

        cfi += 1

        if (debug)
          println("\ncostFctsInner: " + costFunInner)

        val i = cStr.indexOf("freqx")

        if (i != -1) {

          val possibleMeasuredEli: Int = cStr.substring(i + 5).takeWhile(_ != '_').toInt

          costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE.put(possibleMeasuredEli, costFunInner)

          if (cStr.contains("wDf")) { // deprecated; remove after more tests

            val hypothesisMovingTargetWeightVar = costFunInner.asInstanceOf[PolynomialTerm[DoubleReal]].arg.asInstanceOf[Sum[DoubleReal]].larg.asInstanceOf[Variable[DoubleReal]]

            hypothesisParamTargetWeightVariables.append((possibleMeasuredEli, hypothesisMovingTargetWeightVar))

          }

        } else {

          stomp(-205, {

            costFunInner match {

              case pt: PolynomialTerm[DoubleReal] => {

                // toString of PolynomialTerm might be confusing as it omits *, so, e.g., 1*0.0^2 appears as 10.0^2, so we use this little hack:

                val scale = pt.getFormula(new util.ArrayList[Variable[DoubleReal]]()).drop(2).takeWhile(_ != '*').trim.toLong

                val exp = pt.getFormula(new util.ArrayList[Variable[DoubleReal]]()).dropRight(1).reverse.takeWhile(_ != ',').reverse.toInt

                scale + "(" + pt.arg + ")^" + exp

              }

              case t => t.toString

            }

          }) // this happens when a measured atom is undefined and f(ma) had been replaced with 0
          // However, by default we still retain this inner cost in the list of innerCosts (because the undefined atom has a defined frequency (0)).
          // Use switch ignoreCostsWithUndefMeasuredAtoms to omit such innerCosts (more precisely, we replace it with 0):

          if (ignoreCostsWithUndefMeasuredAtoms) {

            stomp(-208, costFctsInner(cfi - 1).toString)

            costFctsInner(cfi - 1) = (new diff.DifferentialFunctionFactoryStasp()).zero()

          }

        }

      })

    })

  }

  //log("\npreptimer 2.1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  @inline def findInnerCostFunForParameterAtom_ForPartDerivINCOMPLETE(parameterAtomEli: Eli): Option[DifferentialFunction[DoubleReal]] = {

    assert(!partDerivComplete) // works only with partDerivComplete=false

    costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE.get(parameterAtomEli) //costFctsInnerWithPossMeasuredElis.find(_._2 == parameterAtomEli)

  }

  log("\npreptimer 3: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  //@Contended
  val parameterAtomsElis = parameterAtomsElis0 //.filter(eliToVariableInCostFunctions.contains(_))

  val innerCostFunForParamAtomEli_ForPartDerivINCOMPLETE = if (ignoreParamVariablesR || partDerivComplete) mutable.Map[Eli, Option[DifferentialFunction[DoubleReal]]]() else
    mutable.HashMap[Eli, Option[DifferentialFunction[DoubleReal]]]().++(parameterAtomsElis.map(eli => {

      // NB: implicit assumption for !partDerivComplete is that measured atoms = parameter atoms

      eli -> findInnerCostFunForParameterAtom_ForPartDerivINCOMPLETE(eli)

    }).toMap)

  log("\npreptimer 4: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  //costFctsInner = costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE.values.toArray

  val n = dFFactory.`val`(new DoubleReal(costFctsInner.length.toDouble))

  val totalCostFun_forPartDerivCompl: DifferentialFunction[DoubleReal] = if (costFctsInner.isEmpty) dFFactory.`val`(new DoubleReal(-1 /*dummy*/)) else
    costFctsInner.reduceLeft((reduct: DifferentialFunction[DoubleReal], x: DifferentialFunction[DoubleReal])
    => {

      // /*reduct.mul(x)*/ reduct.plus(x)

      innerCostReductFun(reduct, x)

    }
    ).div(n)

  // We store the partial derivatives of the cost function(s) in nablasInner:
  if (!ignoreParamVariablesR && (!allowNumFiniteDiff || mixedScenario))
    parameterAtomsElis.foreach(parameterAtomEli => {

      if (eliToVariableInCostFunctions.contains(parameterAtomEli)) {

        val parameterAtomVar: Variable[DoubleReal] = eliToVariableInCostFunctions(parameterAtomEli)

        if (partDerivComplete) { // see M. Nickles: PLP'18 paper; use with non-MSE cost functions (more general but slower)

          nablasInner(parameterAtomEli) = totalCostFun_forPartDerivCompl.diff(parameterAtomVar)

        } else { // faster, less general. For simple MSE-style (and some others?) cost functions. See M. Nickles: ILP'18 paper.

          val innerCostFun: DifferentialFunction[DoubleReal] = innerCostFunForParamAtomEli_ForPartDerivINCOMPLETE(parameterAtomEli).getOrElse {

            if (!allowNumFiniteDiff)
              stomp(-5003) // we can arrive here also if there are no costs and the measured variables in eliToVariableInCostFunctions are
            // extracted from some _eval_ fact, so we make this just a warning and not an error.

            dFFactory.`val`(new DoubleReal(0d))

          }

          nablasInner(parameterAtomEli) = innerCostFun.diff(parameterAtomVar)

        }

        log("   part derivative wrt parameter atom " + symbols(parameterAtomEli) + ": " + nablasInner(parameterAtomEli))

      } else { // deprecated

        assert(false)

        null

      }

    })

  log("\npreptimer 5: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val parameterAtomsElisSet: Set[Eli] = parameterAtomsElis.toSet

  val parameterLiteralElisArray = parameterAtomsElis ++ parameterAtomsElis.map(negatePosEli(_))

  val parameterLiteralElis: IntArrayUnsafeS = new IntArrayUnsafeS(parameterLiteralElisArray, aligned = true)

  if (verbose) {

    println("Measured atoms (after adding parameter atoms not occurring in cost): " + measuredAtomsElis.map(symbols(_)).mkString(" "))

    println("Parameter atoms: " + parameterAtomsElisSet.map(symbols(_)).mkString(" "))

  }

  @inline def deficitByDeriv(parameterLiteralEli: Eli): Double = {

    // Assumes that in a step directly preceding the re-sorting, the freqx variables in the nablaInner have been
    // updated to measuredAtomEliToStatisticalFreq!

    val r = if (isPosAtomEli(parameterLiteralEli)) {

      if (nablasInner(parameterLiteralEli) != null) {

        nablasInner(parameterLiteralEli).getReal

      } else
        return Double.NaN //0d

    } else {

      if (nablasInner(negateNegEli(parameterLiteralEli)) != null)
        -nablasInner(negateNegEli(parameterLiteralEli)).getReal
      else
        return Double.NaN //0d

    }

    if (r.isNaN)
      0.5d - rngGlobal.nextDouble()
    else
      r

  }

  var deficitOrderedUncertainLiteralsForJava: Array[Integer] = parameterLiteralElisArray.map(new Integer(_))

  if (debug) {

    println("Parameter elis:")

    parameterLiteralElisArray.foreach(p => if (isPosEli(p)) println(p + " = " + symbols(p)) else println(p + " = not " + symbols(negateNegEli(p))))

  }

  if (shuffleRandomVariables)
    shuffleArray(deficitOrderedUncertainLiteralsForJava, new java.util.SplittableRandom())

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

  if (delSAT.verbose)
    println("\nPreparation time: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  def computeClarkNogis(rules: ArrayBuffer[Rule]): (Array[IntArrayUnsafeS], java.util.HashMap[Eli, Array[Eli]], java.util.HashMap[Eli, Array[Eli]]) = {

    // Nogood generation follows (with a few minor differences) https://www.cs.uni-potsdam.de/wv/pdfformat/gekanesc07a.pdf

    // NB: the following algorithm assumes that all rules are normal. E.g., :- integrity constraints are not allowed (need
    // to translated away during preprocessing/grounding of the original ASP program, see AspifParser).

    // NB: in SATmode, we can end up in this method only with experimental flag generatePseudoRulesForNogoodsForSATMode = true,
    // otherwise in SAT mode all nogoods have already been generated entirely from the CNF clauses.

    val exclEmptyBodyInDeltaAtoms = false // true simplifies nogoods from empty bodies, but without prior resolution during solving it can also increase solving time (simpler != faster)

    val test = false // must be false (true for current debugging purposes)

    val thresholdForSymbolsPar = 1000000

    val thresholdForRulesPar = 1000000

    val noOfThreads = (Runtime.getRuntime().availableProcessors() / 2).max(1)

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

    def deltaBetaPartComp(rulesPart: ArrayBuffer[Rule]): ArrayBuffer[IntArrayUnsafeS] = { // generate body nogoods

      val deltaBetaPart = mutable.ArrayBuffer[IntArrayUnsafeS]()

      //deltaBetaPart.sizeHint(rulesWoConstr.length * 5 + 1000)

      var ri = 0

      val rpl = rulesPart.length

      while (ri < rpl) {

        val rule = rulesPart(ri)

        val bpos: Array[Eli] = rule.bodyPosAtomsElis

        val bneg: Array[Eli] = rule.bodyNegAtomsElis

        if (!test || bpos.length > 0 || bneg.length > 0) {

          val blit = rule.blit // the blit of the rule. NB: if omitSingletonBlits, this is an ordinary (non body) a if there's just one body literal

          val blitNegated = negateEli(blit)

          val s1: Array[Eli] = Array.ofDim[Eli](bpos.length + bneg.length + 1)

          bpos.copyToArray(s1, 0)

          bneg.copyToArray(s1, bpos.length)

          s1(s1.length - 1) = blitNegated

          deltaBetaPart.append(new IntArrayUnsafeS(s1, aligned = false)) // δ(β)

          negBlitToPosBodyElis.put(blitNegated, bpos)

          val s2pos: Array[IntArrayUnsafeS] = bpos.map(eli => new IntArrayUnsafeS(Array(blit, negatePosEli(eli)), aligned = false))

          deltaBetaPart.appendAll(s2pos) // Δ(β)

          val s2neg: Array[IntArrayUnsafeS] = bneg.map(eli => new IntArrayUnsafeS(Array(blit, negateNegEli(eli)), aligned = false))

          deltaBetaPart.appendAll(s2neg) // Δ(β)

        }

        ri += 1

      }

      log("\npreptimer1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

      deltaBetaPart

    }

    def deltaAtomsComp(omit: Boolean): mutable.ArrayBuffer[IntArrayUnsafeS] = { // generate head/atom-related nogoods

      val deltaAtoms = mutable.ArrayBuffer[IntArrayUnsafeS]()

      if (!omit) {

        //deltaAtoms.sizeHint(symbols.length * 5 + 1000)

        log("\npreptimer2a: " + timerToElapsedMs(timerPrepNs) + " ms\n")

        val rulesGroupedByTheirHeadEli = Array.fill[ArrayBuffer[Rule]](noOfAllElis)(ArrayBuffer[Rule]())

        var rwci = 0

        val rwcl = rulesWoConstr.length

        while (rwci < rwcl) {

          val rule = rulesWoConstr(rwci)

          val h = rule.headAtomsElis.headOption.getOrElse(-1)

          //assert(hashOfPass >= 0)

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

          val s1s2 = ArrayBuffer[IntArrayUnsafeS]()

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

                  new IntArrayUnsafeS(Array(negHeadAtomEli), aligned = false)

                } else
                  new IntArrayUnsafeS(Array(negHeadAtomEli, rule.blit), aligned = false))

              })

            }

            // TODO:  handle #external atoms here (currently ignored / treated as undefined unless defined by some rule):
            if (((bodiesOfp.length > 1 || bodiesOfp.length == 1 && bodiesOfp.head.blit != emptyBodyBlit))) { // δ(p)
              // (^ in satMode (which normally doesn't use this method anyway, see above), this branch is only allowed if we
              // create _all_ possible pseudo-rules (for all clauses and heads), otherwise the following can lead to wrong UNSAT:)

              val s2NogoodBuffer = new IntArrayUnsafeS(bodiesOfp.length + 1, aligned = false) //Array.ofDim[Eli](bodiesOfp.length + 1)

              var s2i = 0

              bodiesOfp.foreach(rule => { // ? note: if we do this even if bodiesOfp is empty, which creates false-enforcing nogoods for undefined symbols

                s2NogoodBuffer.update(s2i, negateEli(rule.blit))

                s2i += 1

              })

              s2NogoodBuffer(s2i) = atomEli_p

              posHeadAtomToNegBlits.put(atomEli_p, s2NogoodBuffer.toArray(0, s2i))

              s1s2.append(s2NogoodBuffer)

            }

            Some(s1s2 /*.distinct*/)

          } else
            None

        }
        }.seq.foreach(deltaAtoms.appendAll(_))

        log("\npreptimer2: " + timerToElapsedMs(timerPrepNs) + " ms\n")

      }

      deltaAtoms

    }

    val deltaClark: mutable.ArrayBuffer[IntArrayUnsafeS] = if (noOfThreadsNg == 1) {

      val rulesOnlyPart = rulesPartitioning.next()

      assert(rulesOnlyPart.length == rulesWoConstr.length)

      deltaBetaPartComp(rulesOnlyPart) ++ deltaAtomsComp(omitAtomNogoods)

    } else {

      implicit val executor = scala.concurrent.ExecutionContext.global

      val deltaBetaFutures: Iterator[Future[ArrayBuffer[IntArrayUnsafeS]]] = rulesPartitioning.map((rulesPart: ArrayBuffer[Rule]) => Future {

        deltaBetaPartComp(rulesPart)

      }(executor))

      val deltaAtomsFuture = Future {

        deltaAtomsComp(omitAtomNogoods)

      }(executor)

      val deltas: ArrayBuffer[ArrayBuffer[IntArrayUnsafeS]] = Await.result(Future.sequence(Seq(deltaAtomsFuture) ++ deltaBetaFutures), Duration.Inf).to[ArrayBuffer]

      deltas.flatten

    }

    val falsNogoods: ArrayBuffer[IntArrayUnsafeS] = if (createFalsNgs)
      symbolsWithIndex.filter(si => isFalsAuxAtom(si._1)).map(x => new IntArrayUnsafeS(Array(x._2), aligned = false)).to[ArrayBuffer]
    else if (!specialConstrRuleNogoods) ArrayBuffer[IntArrayUnsafeS]() else {

      // we add special nogoods for rules which have been (elsewhere) resulted from constraints :- b1, b2, ...

      val contraintRules = rules.filter(rule => isPosAtomEli(rule.headAtomsElis.head) && isFalsAuxAtom(symbols(rule.headAtomsElis.head)))

      contraintRules.map(rule => new IntArrayUnsafeS(rule.bodyPosAtomsElis ++ rule.bodyNegAtomsElis.filterNot(_ == negateEli(rule.headAtomsElis.head)), aligned = false))

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

  def computeDependencyGraph(rules: ArrayBuffer[Rule], noOfAllPosAtomElis: Int, positiveDepGraph: Boolean = true):
  Int2ObjectOpenHashMap[List[Eli]] /*adjacency list*/ = {

    var graphInit = new Int2ObjectOpenHashMap[List[Eli]]()

    var jj = 0

    while (jj < rules.length) {

      val rule: Rule = rules(jj)

      if (!rule.headAtomsElis.isEmpty) {

        val headEli = rule.headAtomsElis.head

        if (!isPosEli(headEli))
          stomp(-5004, rule.toString)

        val successorNodes: Array[Eli] = if (positiveDepGraph) rule.bodyPosAtomsElis else rule.bodyPosAtomsElis.union(rule.bodyNegAtomsElis)

        val succsOfPosHeadEli = {

          val assocs = graphInit.get(headEli)

          if (assocs == null) {

            graphInit.put(headEli, List[Eli]())

            List[Eli]()

          } else
            assocs

        }

        successorNodes.foreach(succEli => {

          graphInit.put(headEli, graphInit.get(headEli) /*succsOfPosHeadEli*/ .:+(succEli))

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
