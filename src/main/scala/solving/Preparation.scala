/**
  * diff-SAT
  *
  * Copyright (c) 2018,2022 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package solving

import java.io.PrintWriter
import java.util
import java.util.concurrent.locks.ReentrantLock

import aspIOutils._

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, PolynomialTerm, Sum, Variable}

import input.diffSAT
import input.diffSAT._

import diff.UncertainAtomsSeprt

import it.unimi.dsi.fastutil.ints.{Int2IntOpenHashMap, Int2ObjectMap, Int2ObjectOpenHashMap, IntOpenHashSet, IntSet}
import it.unimi.dsi.fastutil.objects.ObjectArrayList

import org.apache.commons.math3.ml.clustering.CentroidCluster

import sharedDefs._
import utils.Various._

import utils.IntArrayUnsafeS
import utils.ArrayValExtensibleIntUnsafe
import utils.ArrayValExtensibleLongUnsafe

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Iterator, Seq, mutable}
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}
import scala.util.Sorting

/**
  * Various preparation steps before actual solving and sampling starts.
  *
  * @author Matthias Nickles
  *
  */
class Preparation(val aspifOrDIMACSParserResult: input.AspifOrDIMACSPlainParserResult,
                  val costsOpt: Option[UncertainAtomsSeprt],
                  satModeR: Boolean,
                  omitAtomNogoods: Boolean /*for testing purposes only*/) {

  assert(!omitAtomNogoods)

  var noOfAllElis: Int = -1

  var noOfAbsElis: Int = -1

  var assgnmFullSize: Int = -1

  val satMode = satModeR

  val timerPrepNs = System.nanoTime()

  val rulesOpt: Option[ArrayBuffer[Rule]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.left.toOption

  val dimacsClauseNogoodsOpt: Option[Array[IntArrayUnsafeS]] = aspifOrDIMACSParserResult.rulesOrClauseNogoods.right.toOption

  var symbols: Array[String] = aspifOrDIMACSParserResult.symbols

  var symbolsWithPosElis: Array[(String, Int)] = null.asInstanceOf[Array[(String, Int)]]

  var symbolsWithoutTranslation = Array[String]()

  var noOfPosAtomElis: Int = -1

  var noOfPosBlits: Int = aspifOrDIMACSParserResult.noOfPosBlits

  var emptyBodyBlit: Eli = aspifOrDIMACSParserResult.emptyBodyBlit

  assert(aspifOrDIMACSParserResult.noOfDummySymbols == 0) //deprecated; from optional padding of symbols so that #symbols is a power of 2

  val rephaseLock = if (runRephasingExclusively) new ReentrantLock() else null.asInstanceOf[ReentrantLock]

  def setFoundStructures: Unit = {

    symbolsWithPosElis = symbols.zipWithIndex.map(symInd => (symInd._1, symInd._2 + 1)) // recall that positive elis are >= 1

    noOfPosAtomElis = symbols.length

    noOfAbsElis = noOfPosAtomElis + noOfPosBlits

    assgnmFullSize = noOfAbsElis

    noOfAllElis = assgnmFullSize * 2

    if (satMode) {

      assert(noOfPosBlits == 0)

      assert(noOfPosAtomElis == noOfAbsElis)

    }

  }

  setFoundStructures

  @inline def isPosAtomEli(eli: Eli): Boolean = eli >= 1 && eli <= noOfPosAtomElis

  @inline def isPosEli(eli: Eli): Boolean = eli > 0 //eli < posNegEliBoundary

  @inline def isNegEli(eli: Eli): Boolean = eli < 0 //eli >= posNegEliBoundary

  @inline def negateEli(eli: Eli): Eli = {

    -eli

  }

  @inline def negatePosEli(eli: Eli): Eli = -eli

  @inline def negateNegEli(eli: Eli): Eli = -eli

  @inline def toAbsEli(eli: Eli): Eli = {

    ((eli >> 31) ^ eli) - (eli >> 31)

  }

  var posHeadAtomToNegBlits = new java.util.HashMap[Eli, Array[Eli]]() // for non-tight ASP only

  var negBlitToPosBodyElis = new java.util.HashMap[Eli /*negative blit*/ , Array[Eli]]() // for non-tight ASP only

  val clarkNogoods1: Array[IntArrayUnsafeS] = dimacsClauseNogoodsOpt.getOrElse {

    val rules = rulesOpt.get

    val (cngs1: Array[IntArrayUnsafeS], pHatomNegBlits: java.util.HashMap[Eli, Array[Eli]], bpbes: java.util.HashMap[Eli, Array[Eli]]) =
      computeClarkNogis(rules)

    posHeadAtomToNegBlits = pHatomNegBlits

    negBlitToPosBodyElis = bpbes

    val cngs2 = cngs1

    val cngs3 = cngs2 ++ aspifOrDIMACSParserResult.assumptionElis.map(aEli =>
      new IntArrayUnsafeS(Array(negateEli(aEli))) // if aEli is positive, this corresponds to constraint
      // :- not aEli.
      // if aEli is a negative literal, this corresponds to :- negate(aEli), i.e., the same.

    )

    cngs3

  }

  val absEliUndoChangeMap = mutable.HashMap[Eli, Eli]() // needed after solving for preProcesss_variableOrNogoodElimConfig._5 = true only, to
  // undo (re-translate) eli (positive as well as negative) mapping induced by material removing of variables.

  symbolsWithoutTranslation = symbols

  val preProcesssVariableElimConfig: (Boolean, Double, Double, Float, Boolean) = if (!preProcesssVariableElimConfigR._1 || satMode && (parameterAtomsElis == null || parameterAtomsElis.length == 0) && (costsOpt.isEmpty || costsOpt.get.innerCostExpressionInstances.isEmpty)) preProcesssVariableElimConfigR else {

    if (!satMode)
      stomp(-5014, "preProcesssVariableElimConfig cannot be used in ASP mode - setting ignored")
    else
      stomp(-5014, "preProcesssVariableElimConfig cannot be used in probabilistic settings - setting ignored") // as it may create a bias in the sample

    (false, 0d, 0d, 1f, true)

  }

  val (clarkNogoods2: Array[IntArrayUnsafeS], removedNogoodsPerAtomOpt, removedPosAtomsOrderedOpt) = {

    if (!preProcesssVariableElimConfig._1 || !satMode) {

      //if (preProcesssVariableElimConfig._1 && !satMode) // TODO: make preprocessing work again in ASP mode, at least for tight progs. Should be easy (it already worked at some time)
      //stomp(-5009, "preProcesssVariableElimConfig cannot be used in ASP mode")

      // if (preProcesssVariableElimConfig._1 && parameterAtomsElis != null && parameterAtomsElis.length > 0)
      //  stomp(-5009, "preProcesssVariableElimConfig cannot be used in probabilistic settings") // as it may create a bias in the sample

      (clarkNogoods1, None, None)

    } else {

      val cns1: ObjectArrayList[IntArrayUnsafeS] = new ObjectArrayList[IntArrayUnsafeS](clarkNogoods1.length + 1000) // clarkNogoods1.to[ArrayBuffer]

      cns1.addElements(0, clarkNogoods1)

      val preliminaryResolvents = new ObjectArrayList[IntArrayUnsafeS](100)

      var lorgno = 0

      lazy val oldN = symbols.length

      if (verbose) {

        var i = 0

        while (i < cns1.size) {

          lorgno += cns1.get(i).sizev

          i += 1

        }

        println("K-original (nogoods): " + cns1.size) // number corresponds to original #clauses

        println("L-original (literals in nogoods): " + lorgno) // original #literals (i.e., elis in our case)

        println("N-original (variables): " + oldN) // original #symbols (variables)

      }

      val startTimeVarElim = System.nanoTime()

      if (preProcesssVariableElimConfig._5 && !satMode)
        stomp(-5009, "Setting variableOrNogoodElimConfig._5 not available in ASP mode")

      val (cns2: ArrayBuffer[IntArrayUnsafeS], removedNogoodsPerAtomOpt: Option[mutable.TreeMap[Eli /*atom eli (variable)*/ , mutable.HashSet[IntArrayUnsafeS]]],
      removedPosAtomsOrderedOpt: Option[ArrayBuffer[Eli]]) =
      /*if (!preProcesss_variableOrNogoodElimConfig._1) (cns1, None) else*/ { // static nogood and/or variable elimination

        // Deletes variables and removes the nogoods which contain the deleted variables. Both need to be restored after solving (unless UNSAT),
        // as the resulting satisfying assignment is a partial assignment.
        // Core algorithm is based on iterated application of the propositional resolution rule, with certain bounds to reduce complexity. See
        // NiVER (Subbarayan, Pradhan (2004): NiVER: Non Increasing Variable Elimination Resolution for Preprocessing SAT instances).
        // Additonally, we apply subsumption and self-subsumption (nogood strengthening, ananlogous clause strengthening).
        // TODO: the overall elimination algo isn't particularly optimized yet, it should be optimized along the
        // lines of Een and Biere (2005) or some later approach: http://fmv.jku.at/papers/EenBiere-SAT05.pdf

        val removedNogis = /*Array.ofDim[Int](cns1.length * 2)*/ new IntOpenHashSet()

        val productPosNegLitsOrigCap = (Math.sqrt(cns1.size.toDouble) * preProcesssVariableElimConfig._4).toInt

        //@deprecated val noOfResolventsOverheadCap = (cns1.size.toDouble * preProcesssVariableElimConfig._2).toInt

        //@deprecated val noOfOriginalLitsOverheadCap = (noOfAllElis.toDouble * preProcesssVariableElimConfig._3).toInt

        val eliToNogisTemp: Array[IntOpenHashSet] = Array.fill[IntOpenHashSet](noOfAllElis + 1)(new IntOpenHashSet())

        var omittedDueToSubsumption = 0

        var noOfStrengthenedNogoods = 0

        def existsForeignSubsumed(nogoodCand: IntArrayUnsafeS /*<- the possibly including/larger nogood*/): Boolean = {

          // Subsumption check; checks if there is another clause \subsetof nogoodCand (so we can we ignore nogoodCand)
          // (Remark: we use "subsumes" in the sense of "includes as superset (of literals)", which appears to be different from the terminology used in Een, Biere)

          var addNogoodCand = true

          var longestOccurList = null.asInstanceOf[IntOpenHashSet]

          var k = nogoodCand.size - 1

          while (k >= 0) {

            val occurListK = eliToNogisTemp(eliToJavaArrayIndex(nogoodCand.get(k)))

            if (longestOccurList == null || occurListK.size < longestOccurList.size)
              longestOccurList = occurListK

            k -= 1

          }

          if (longestOccurList != null) {

            val longestOccurListIt = longestOccurList.iterator

            while (addNogoodCand && longestOccurListIt.hasNext) {

              val nogoodT: IntArrayUnsafeS = cns1.get(longestOccurListIt.nextInt())

              // TODO: try probably faster subsumption check from http://fmv.jku.at/papers/EenBiere-SAT05.pdf

              if (nogoodT.subsetOf(nogoodCand)) {

                omittedDueToSubsumption += 1

                if (debug2)
                  println("\nNogood " + nogoodT + " is subsumed by " + nogoodCand + ", so we are ignoring " + nogoodCand)

                addNogoodCand = false // note: the omitted resolvent may be added to removedNogis in a later resolution iteration
                // anyway, so omitting it as a result of "false" here doesn't necessarily reduce the final number of nogoods.

              }

            }

          }

          !addNogoodCand

        }

        var nogi = cns1.size - 1

        while (nogi >= 0) {

          val nogood: IntArrayUnsafeS = cns1.get(nogi)

          var k = nogood.size() - 1

          while (k >= 0) {

            eliToNogisTemp(eliToJavaArrayIndex(nogood.get(k))).add(nogi)

            k -= 1

          }

          nogi -= 1

        }

        var entry = false

        var maxElimIts = 1 // sometimes eliminating a variable (pos atom) leads to follow-up elimination opportunities, in which case > 1 should be set

        val elimPosAtoms = new IntOpenHashSet()

        val elimPosAtomsOrdered = ArrayBuffer[Eli]() // besides looking up eliminated variables, we also need to keep track of their
        // order of elimination.

        val removedNogoodsPerAtom = mutable.TreeMap[Eli /*pos atom eli*/ , /*ArrayBuffer*/ mutable.HashSet[IntArrayUnsafeS]]()

        /*
        val resolventsPoolMemSize = 0 //cns1.size * 10 // NB: this pool exists because Java unsafe memory allocation is quite slow. However,
        // this pool will be used up quickly even for medium-sized problems. We could prevent this by freeing memory from the pool, but
        // we would then end up with writing our own sort-of GC...

        var resolventsPoolMemUsed = 0

        val resolventsPoolMem: Long = if (resolventsPoolMemSize > 0) unsafe.allocateMemory(resolventsPoolMemSize) else -1l
        */

        do {

          entry = false

          var posEli = 1

          while (posEli <= noOfPosAtomElis) { // i.e. we don't consider ASP-mode blit-"atoms" here


            var noOfLiteralsInPreliminaryResolvents = 0


            if (!elimPosAtoms.contains(posEli)) {

              val negPosEli = negatePosEli(posEli)

              val nogisWithPosEli = eliToNogisTemp(eliToJavaArrayIndex(posEli)).toIntArray

              val nogisWithNegPosEli = eliToNogisTemp(eliToJavaArrayIndex(negPosEli)).toIntArray

              var pncLits = 0

              var resLits = 0

              var eliminatePosEli = false

              preliminaryResolvents.clear()

              @inline def addResolventPreliminarily(resolvent: IntArrayUnsafeS): Unit = {

                preliminaryResolvents.add(resolvent)

                noOfLiteralsInPreliminaryResolvents += resolvent.size()

              }

              def addResolvent(resolventA: IntArrayUnsafeS): Unit = {

                var k = 0

                val newNogi = cns1.size

                cns1.add(resolventA)

                k = resolventA.size - 1

                while (k >= 0) {

                  val occurListK: IntOpenHashSet = eliToNogisTemp(eliToJavaArrayIndex(resolventA.get(k)))

                  occurListK.add(newNogi)

                  k -= 1

                }

                if (debug2)
                  println("\nAdded nogood (resolvent): " + resolventA.toArray.mkString(" "))

              }

              def ccbs(): Unit = {

                var resolventsAddedHere = 0  // maximum p x n, where p (n) is the number of nogoods where variable occurs positively (negatively)

                var pIt = 0

                var nIt = -1

                if ((nogisWithPosEli.length - 1) * (nogisWithNegPosEli.length - 1) < productPosNegLitsOrigCap) { //if (pIt * nIt < productPosNegLitsOrigCap)

                  eliminatePosEli = true

                  while (pIt < nogisWithPosEli.length) {
                    {

                      val pNogi: Nogi = nogisWithPosEli(pIt)

                      if (!removedNogis.contains(pNogi)) {

                        nIt = 0

                        while (nIt < nogisWithNegPosEli.length) {
                          {

                            val nNogi: Nogi = nogisWithNegPosEli(nIt)

                            if (!removedNogis.contains(nNogi)) {

                              val pNogood: IntArrayUnsafeS = cns1.get(pNogi)

                              val nNogood: IntArrayUnsafeS = cns1.get(nNogi)

                              //sampledModels.sizeHint(pNogood.length + nNogood.length - 2)

                              pncLits += nNogood.size() + pNogood.size()

                              var ik = pNogood.size() - 1

                              var jk = nNogood.size() - 1

                              //println("\n\npNogood: " + pNogood.toString)

                              //println("nNogood: " + nNogood.toString)

                              {

                                var rs = nNogood.sizev + pNogood.sizev // initial size, will be reduced later

                                var usedPoolMem = false

                                val resolvent = /*if (resolventsPoolMemUsed + (rs << 2) < resolventsPoolMemSize) {

                                  val r = new IntArrayUnsafeS(sizev = rs, atAddress = resolventsPoolMem + resolventsPoolMemUsed)

                                  usedPoolMem = true

                                  r

                                } else*/ {

                                  new IntArrayUnsafeS(sizev = rs)

                                }

                                var isTaut = false

                                {

                                  val chhh = false

                                  if (chhh) assert(nNogood.contains(negateEli(posEli)))
                                  if (chhh) assert(pNogood.contains(posEli))

                                  if (nNogood.contains(posEli) || pNogood.contains(negateEli(posEli)))
                                    isTaut = true

                                  if (!isTaut) {

                                    unsafe.copyMemory(nNogood.getAddr, resolvent.getAddr, nNogood.sizev << 2)
                                    // ^ we couldn't simply use the existing nNogood, as the resolvent modifies it and we need the
                                    // original nNogood for finding further resolvents where nNogood is involved. But still cheaper than allocating a
                                    // fresh nogood, because of relatively slow Java unsafe mem allocation (situation would be different in C/C++).

                                    unsafe.copyMemory(pNogood.getAddr, resolvent.getAddr + (nNogood.sizev << 2), pNogood.sizev << 2)

                                    var ii = rs - 1

                                    while (ii >= 0 && !isTaut) {

                                      val lit = resolvent.get(ii)

                                      if (rs > ii && (lit == posEli || lit == negateEli(posEli))) {

                                        val lastLit = resolvent.get(rs - 1)

                                        if (lastLit != posEli && lastLit != negateEli(posEli)) {

                                          if (ii < nNogood.sizev) {

                                            if (chhh) assert(lit == negateEli(posEli)) // if nNogood is itself a tautology, we need to have caught this already (see below)

                                            //restoreNegPosEliInNnogood = ii // to restore the replace item later in case the resolvent turns out to be a tautology

                                          } else if (chhh)
                                            assert(lit == posEli) // analogously

                                          resolvent.update(ii, lastLit)

                                        }

                                        rs -= 1

                                      } else if (ii >= 1 && resolvent.contains(negateEli(lit), maxIndexExclusive = ii))
                                        isTaut = true // observe that further above we (must!) also check for tautology where the tautology is caused
                                      // by occurrence of both posEli and negateEli(posEli) _within_ either pNogood or nNogood itself!

                                      ii -= 1

                                    }

                                  }

                                  if (!isTaut) {

                                    resolvent.sizev = rs

                                    //if (usedPoolMem)
                                    // resolventsPoolMemUsed += rs << 2

                                    //println("\n\nCleaned resolvent (before duplicate check): " + resolvent.toString)

                                    if (chhh) assert(!resolvent.contains(posEli) && !resolvent.contains(negateEli(posEli)))

                                    resolvent.removeDuplicatesGlob() // important also for correctness, as we'll need to reliably create
                                    // empty resolvents occuring from two singleton nogoods (=>UNSAT)

                                    //   println("Cleaned resolvent (after duplicate check): " + resolvent.toString)

                                    resolventsAddedHere += 1

                                    val resolventLean = resolvent //new IntArrayUnsafeS(resolvent.sizev)

                                    // resolvent.cloneTo(resolventLean.getAddr)  // need to do this if resolventsPoolMem is used!

                                    addResolventPreliminarily(resolventLean)

                                  } else
                                    resolvent.free()

                                  if (chhh) assert(nNogood.contains(negateEli(posEli)))
                                  if (chhh) assert(pNogood.contains(posEli))

                                }

                              }

                            } //else
                            //cns1(nNogi).free()  // nope!

                          }

                          nIt += 1

                        }

                      } //else
                      //cns1(pNogi).free()  // nope!

                    }

                    pIt += 1

                  }

                  /*
                  println("nogisWithPosEli.length = " + nogisWithPosEli.length)
                  println("nogisWithNegPosEli.length = " + nogisWithNegPosEli.length)
                  println("resolventsAddedHere = " + resolventsAddedHere)
                  println */

                } else pncLits = -1

              }

              ccbs

              @inline def adc1(removedPosEli: Eli): Unit = {

                @inline def rmNogood(nogi: Nogi): Option[mutable.HashSet[IntArrayUnsafeS]] = {

                  removedNogis.add(nogi)

                  val oldRemovedNogoods: mutable.HashSet[IntArrayUnsafeS] =
                    removedNogoodsPerAtom.getOrElse(removedPosEli, mutable.HashSet[IntArrayUnsafeS]())

                  oldRemovedNogoods.add(cns1.get(nogi))

                  removedNogoodsPerAtom.put(removedPosEli, oldRemovedNogoods /*.distinct*/) // observe that we later after solving have
                  // to restore the eliminated variables (posAtoms) in reverse order, since the removed nogoods for a variable x
                  // might also contain variables which will be removed after x.

                }

                nogisWithPosEli.foreach(a => {

                  rmNogood(a)

                })

                nogisWithNegPosEli.foreach(a => {

                  rmNogood(a)

                })

              }


              //  println(noOfLiteralsInPreliminaryResolvents, nogisWithPosEli.length * nogisWithNegPosEli.length)

              if(noOfLiteralsInPreliminaryResolvents >= nogisWithPosEli.length * nogisWithNegPosEli.length)
                eliminatePosEli = false
              else {

                preliminaryResolvents.forEach(addResolvent(_))

              }

              if (eliminatePosEli) {

                adc1(removedPosEli = posEli) // removes nogoods

                entry = true

                elimPosAtoms.add(posEli)

                elimPosAtomsOrdered.append(posEli)

              }

            }

            if (posEli % 10 == 0 || posEli == noOfPosAtomElis) {

              val statusLine = "Variables checked for elimination: " + posEli + "/" + noOfPosAtomElis + ", removed: " + elimPosAtoms.size

              //print("\rVariables checked for elimination: " + posEli + "/" + noOfPosAtomElis + ", removed: " + elimPosAtoms.size)

              printStatusLine(statusLine)

            }

            /*if (false && posEli > 7000) {

              println("\nTTT: " + timerToElapsedMs(startTimeVarElim) + "ms")

              sys.exit(0)

            }*/

            posEli += 1

          }

          maxElimIts -= 1

        } while (entry && maxElimIts > 0)

        println

        if (debug) println("\nTime after variable elimination (identification part): " + timerToElapsedMs(startTimeVarElim) + "ms")

        //if(resolventsPoolMemSize > 0)
        //unsafe.freeMemory(resolventsPoolMem)

        val eliToNogisArraysTemp: Array[Array[Int]] = Array.fill[Array[Int]](noOfAllElis + 1)(null.asInstanceOf[Array[Int]])

        var ai = 1

        while (ai <= noOfAbsElis) {

          eliToNogisArraysTemp(eliToJavaArrayIndex(ai)) = eliToNogisTemp(eliToJavaArrayIndex(ai)).toIntArray

          eliToNogisArraysTemp(eliToJavaArrayIndex(negateEli(ai))) = eliToNogisTemp(eliToJavaArrayIndex(negateEli(ai))).toIntArray

          ai += 1

        }

        val nogoodsAfterSubsumptionChecks = ArrayBuffer[IntArrayUnsafeS]()  // original nogoods without those removed in the eliminated variable identification stage above and also without those subsumed by other nogoods

        var ni = 0

        while (ni < cns1.size) { // observe that we couldn't obtain the new nogood list from eliToNogisTemp as
          // we would miss empty nogoods

          val nogoodCand: IntArrayUnsafeS = cns1.get(ni)

          var addNogoodCand = !removedNogis.contains(ni) && (!foreignNogoodSubsumptionCheck || !existsForeignSubsumed(nogoodCand))

          if (addNogoodCand) {

            //println("added to finalNogoods: " + nogoodCand)

            nogoodsAfterSubsumptionChecks.append(nogoodCand)

          }

          //if (removedNogis.contains(ni))
          // cns1(ni).free()  // nope (would free nogood we'll require later)

          ni += 1

        }

        def findSubsumingWithOneLitNegated(subsumedNogood: IntArrayUnsafeS /*<- the included/shorter nogood*/ ,
                                           negateLitIndex: Int /*index of eli in subsumedNogood where negation is assumed */ ,
                                           negLit: Eli): Boolean /*ObjectArrayList[IntArrayUnsafeS]/*ArrayBuilder.ofRef[IntArrayUnsafeS]*/ */ = {

          // Used for strengthening nogoods by discovering self-subsumption (not for removal of subsuming nogoods).
          // Not thread-safe!

          // Finds clauses C s.t. subsumedNogood \subsetof C
          // (Remark: we use "subsumes" in the sense of "includes a smaller set (of literals)", which appears to be different from the terminology used in Een, Biere)

          var anyStrengthened = false

          val shortestOccurList: Array[Int] = eliToNogisArraysTemp(eliToJavaArrayIndex(negLit))

          if (shortestOccurList != null) {

            var shortestOccurListIt = 0

            //println(shortestOccurList.length)

            while (shortestOccurListIt < shortestOccurList.length.min(100) /*.hasNext*/ ) {

              if (shortestOccurList(shortestOccurListIt) != -1) {

                val nogoodT: IntArrayUnsafeS = cns1.get(shortestOccurList(shortestOccurListIt) /*.nextInt()*/)

                // TODO: try probably faster subsumption check from http://fmv.jku.at/papers/EenBiere-SAT05.pdf

                if (subsumedNogood.subsetOfExceptOne(nogoodT, ignoreIndexInThis = negateLitIndex)) {

                  //if (debug2)
                  //println("\nNogood " + subsumedNogood + " is subsumed by " + nogoodT)

                  //resultingSubsumingNogoods.add(nogoodT) //resultingSubsumingNogoods.+=(nogoodT)

                  //println("Strengthened nogi " + shortestOccurList(shortestOccurListIt) + " by removing eli " + negLit)

                  noOfStrengthenedNogoods += 1

                  nogoodT.removeItem(negLit)

                  shortestOccurList(shortestOccurListIt) = -1 // we need to mark this as negLit is no longer part of it, but
                  // nogoodT is still returned as part of eliToNogisArraysTemp(...negLit...)

                  anyStrengthened = true

                }

              }

              shortestOccurListIt += 1

            }

          }

          anyStrengthened

        }

        var strengthen = strengthenNogoodsDuringPreproc  // using self-subsumption

        while (strengthen) {

          strengthen = false

          var i = 0

          while (i < nogoodsAfterSubsumptionChecks.length) {

            val nogoodCand = nogoodsAfterSubsumptionChecks(i)

            if (nogoodCand.sizev > 4) {

              // We check for self-subsumption and strengthen the subsuming nogoods by removing redundant literals:

              var nin = 0

              while (nin < nogoodCand.sizev) {

                val negLit = negateEli(nogoodCand.get(nin))

                strengthen = findSubsumingWithOneLitNegated(nogoodCand, nin, negLit)

                nin += 1

              }

            }

            i += 1

            if (verbose && (i % 1000 == 0 || i == nogoodsAfterSubsumptionChecks.length)) {

              //print("\r#Nogoods checked for self-subsumption: " + i + "/" + finalNogoods.length + ", strengthened: " + noOfStrengthenedNogoods)

              val statusLine = "#Nogoods checked for self-subsumption: " + i + "/" + nogoodsAfterSubsumptionChecks.length + ", strengthened: " + noOfStrengthenedNogoods

              printStatusLine(statusLine)

            }

          }

        }

        if (verbose) {

          println("\n#Nogoods omitted due to subsumption: " + omittedDueToSubsumption)

          println("#Nogoods strengthened: " + noOfStrengthenedNogoods)

        }

        (nogoodsAfterSubsumptionChecks, Some(removedNogoodsPerAtom), Some(elimPosAtomsOrdered))

      }

      if (debug) println("\n#cns2: " + cns2.size)


      val cns3WitDuplicateNogoods: ArrayBuffer[IntArrayUnsafeS] = if (preProcesssVariableElimConfig._5 && removedNogoodsPerAtomOpt.isDefined) {

        // Here, we materially remove the variables in removedNogoodsPerAtomOpt.get.keys. Resulting gaps in the
        // original 1..noOfAbsElis are closed (and need to be restored in any discovered models).

        assert(satMode) // TODO: make work with ASP (see "posHeadAtomToNegBlits =" below) or generatePseudoRulesForNogoodsForSATMode

        if (!satMode) {

          stomp(-5006)

        }

        if (debug) println("\nRemoving elis marked for elimination...")

        val removedPosElis = removedNogoodsPerAtomOpt.get.keys.toSet

        val absEliChangeMap = mutable.HashMap[Eli, Eli]()

        var offset = 0

        (1 to noOfAbsElis).foreach(oldAbsEli => {

          // we firstly close the gaps in the sequence of eli numbers created by marking variables as deleted

          if (removedPosElis.contains(oldAbsEli) /*isPosEli(oldEli) && removedPosElis.contains(oldEli) || isNegEli(oldEli) && removedPosElis.contains(negateNegEli(oldEli))*/ )
            offset += 1
          else {

            val newAbsEli = oldAbsEli - offset

            absEliChangeMap.update(oldAbsEli, newAbsEli)

            absEliUndoChangeMap.put(newAbsEli, oldAbsEli)

          }

        })

        val r = cns2.map(nogood => { // we update the nogoods using the new eli numbers. TODO: use foreach, no need for map

          val updatedNogood = new IntArrayUnsafeS(nogood.size())

          var i = 0

          while (i < nogood.size()) {

            val oldEli = nogood.get(i)

            assert(!removedPosElis.contains(toAbsEli(oldEli)))

            val newEli = if (isPosEli(oldEli)) {

              assert(!removedPosElis.contains(oldEli))

              absEliChangeMap(oldEli)

            } else {

              assert(!removedPosElis.contains(negateNegEli(oldEli)))

              negateEli(absEliChangeMap(negateNegEli(oldEli)))

            }

            updatedNogood.update(i, newEli)

            i += 1

          }

          updatedNogood

        }

        )

        symbolsWithoutTranslation = symbols.clone()

        symbols = symbolsWithPosElis.filterNot { case (_, absEli) => removedPosElis.contains(absEli) }.map(_._1)
        // Observe that the noAbsElis in SolverMulti is thus lower than the noOfAbsElis here.

        assert(noOfPosBlits == 0)

        setFoundStructures

        //    posHeadAtomToNegBlits = pHatomNegBlits // TODO
        //
        //    negBlitToPosBodyElis = bpbes  // TODO

        if (debug) println("Removed pos elis: " + removedPosElis.size)

        if (debug) println("#variables:" + symbols.length)

        r

      } else {

        cns2

      }

      if (debug) println("\n#cns3WitDuplicateNogoods: " + cns3WitDuplicateNogoods.size)

      val cns3 = cns3WitDuplicateNogoods/*.distinctBy((s: IntArrayUnsafeS) => {  // TODO: bug (crashes sometimes)

        s.sortBy(_.toFloat)  // don't use (current) hashcode implementation for nogood, need precise equality

        s.toString

      })*/

      if (debug) println("\n#cns3: " + cns3.size)


      if (verbose) {

        println("\nTime variable elimination: " + timerToElapsedMs(startTimeVarElim) + "ms")

        val kDiff = cns3.length - cns1.size

        println("K (clauses) after elimination stage: " + cns3.length + " (" + (if (kDiff > 0) "+" else "") + kDiff.toFloat / cns1.size.toFloat * 100f + "%)")

        val l = cns3.map(_.size()).sum

        val lDiff = l - lorgno

        println("L (literals in nogoods) after elimination stage: " + l + " (" + (if (lDiff > 0) "+" else "") + lDiff.toFloat / lorgno.toFloat * 100 + "%)")

        val nDiff = symbols.length - oldN

        println("N (variables) after elimination stage: " + symbols.length + " (" + (if (nDiff > 0) "+" else "") + nDiff.toFloat / oldN.toFloat * 100f + "%)")

        if (!preProcesssVariableElimConfig._5) println("  (note: material variable elimination is off)")

      }

      (cns3.toArray, removedNogoodsPerAtomOpt, removedPosAtomsOrderedOpt)

    }

  }

  if (showIntermediateTimers)
    println("\npreptimer 2.1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  var clarkNogoods3: Array[IntArrayUnsafeS] = if (!initCleanUpArrangeClarkNogoods && !preProcesssVariableElimConfig._1) clarkNogoods2 else {

    if (removeDuplicateLiteralsFromClarkNogoods) {

      var i = 0

      while (i < clarkNogoods2.length) {

        val nogood: IntArrayUnsafeS = clarkNogoods2(i)

        nogood.removeDuplicatesGlob()

        //if(nogood.sizev == 1)
        // elisInSingletonNogoods.append(nogood.get(0))

        i += 1

      }

    }

    clarkNogoods2

  }

  if (showIntermediateTimers)
    println("\npreptimer 2.2: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val noOfNogoodClusters = 100.min(clarkNogoods3.length)

  case class NogoodClusterable(nogood: IntArrayUnsafeS) extends org.apache.commons.math3.ml.clustering.Clusterable {

    override def getPoint: Array[Double] = {

      val r = nogood.toArray.map(_.toDouble).padTo(15, 0d) // TODO: might need to increase to avoid some out of bounds error in clustering code

      //println(r.mkString(","))

      r
    }

  }

  val nogoodClusters: util.List[CentroidCluster[NogoodClusterable]] = if (clusterNogoods) { //TODO: Nogood clustering useful for anything? keep? remove?

    assert(!sortInitialNogoods)
    assert(shuffleNogoods == 0)

    val nogoodNogoodDistanceCache = new mutable.HashMap[Set[IntArrayUnsafeS], Double]()

    val t = System.nanoTime()

    @inline def nogoodNogoodDistance(nogoodX: IntArrayUnsafeS, nogoodY: IntArrayUnsafeS): Double = {

      nogoodNogoodDistanceCache.getOrElseUpdate(Set(nogoodX, nogoodY), {

        val r = {

          var inCommon = 0

          var xi = 0

          while (xi < nogoodY.sizev) {

            if (nogoodX.contains(nogoodY.get(xi), nogoodX.sizev - 1) ||
              nogoodX.contains(negateEli(nogoodY.get(xi)), nogoodX.sizev - 1))
              inCommon += 1

            xi += 1

          }

          if (inCommon == 0)
            1d
          else
            1d / (inCommon.toDouble + 1d)

        }

        r

      })

    }

    class NogoodNogoodDistance extends org.apache.commons.math3.ml.distance.DistanceMeasure {

      override def compute(a: Array[Double], b: Array[Double]): Double =
        nogoodNogoodDistance(nogoodX = new IntArrayUnsafeS(a.map(_.toInt)), nogoodY = new IntArrayUnsafeS(b.map(_.toInt)))

    }

    val nogoodClusterer = new org.apache.commons.math3.ml.clustering.KMeansPlusPlusClusterer[NogoodClusterable](noOfNogoodClusters, 50,
      new NogoodNogoodDistance() /*,  new JDKRandomGenerator((System.currentTimeMillis() << 3).toInt),
        KMeansPlusPlusClusterer.EmptyClusterStrategy.LARGEST_VARIANCE*/)

    val points = new java.util.ArrayList[NogoodClusterable](clarkNogoods3.length)

    clarkNogoods3.foreach(nogood => points.add(NogoodClusterable(nogood)))

    val nogoodClusters: util.List[CentroidCluster[NogoodClusterable]] = nogoodClusterer.cluster(points)

    if (debug) println("Time for nogood clustering / k-means++: " + timerToElapsedMs(t) + "ms")

    if (debug) println("\npreptimer 9a: " + timerToElapsedMs(timerPrepNs) + " ms\n")

    nogoodClusters

  } else
    null.asInstanceOf[util.List[CentroidCluster[NogoodClusterable]]]

  val clarkNogoods4: Array[IntArrayUnsafeS] = if (nogoodClusters != null) {

    val buf = ArrayBuffer[IntArrayUnsafeS]()

    import scala.collection.JavaConverters._
    nogoodClusters.asScala.foreach { case (centroid: CentroidCluster[NogoodClusterable]) =>

      if (debug) println(/*"cluster centroid: " + centroid.getCenter +*/ ", elements: " + centroid.getPoints.size)

      buf.appendAll(centroid.getPoints.asScala.map(_.nogood))

    }

    buf.toArray

  } else clarkNogoods3

  val clarkNogoodsFinal: Array[IntArrayUnsafeS] = if (!sortInitialNogoods && clarkNogoods4.length <= shuffleNogoods) {

    shuffleArray(clarkNogoods4, rngGlobal) // TODO: move this into solver threads

    clarkNogoods4

  } else if (sortInitialNogoods) {

    clarkNogoods4.sortBy(_.sizev)

  } else
    clarkNogoods4

  @inline def psCombine(hash: Long, eli: Eli): Long = {

    hash * (eli + noOfAbsElis).toLong

  }

  // ***** In the following, note that extReducibles 0, 3 and 4 currently don't exist (anymore) *****

  val offsetIntsForBitsetWithExtReducibles345 = 4
  // int 0 = #elis in nogood, int 1 = #unassigned elis ("unassigned length"),
  // ints 2 and 3: long with product of elis (if small enough, or 0l else), or 0l if extReducibles != 5,
  // int 4..: bitset (where no product can be used).
  // Behind bitset: list of elis in nogood

  val offsetBytesForBitsetWithExtReducibles345 = offsetIntsForBitsetWithExtReducibles345 << 2

  val sizeInBitsForBitsetWithExtReducibles345 = noOfAllElis

  val noOfLongsForBitsetWithExtReducibles345 = ((sizeInBitsForBitsetWithExtReducibles345 /*- 1*/) >> 6) + 1

  val spaceInBytesForBitsetWithExtReducibles3 = noOfLongsForBitsetWithExtReducibles345 * 2 * 4

  val offsetIntsOfNogoodInReducible = (if (extReducibles == 4) offsetIntsForBitsetWithExtReducibles345 else if (extReducibles == 3 || extReducibles == 5)
    offsetIntsForBitsetWithExtReducibles345 + (spaceInBytesForBitsetWithExtReducibles3 >> 2)
  else if (extReducibles == 2) 3 /*5*/
  else if (extReducibles == 1) 5 else 3) + 4

  val closingIntsAfterNogoodInReducible = 2
  // ^ number of Ints added after the nogood literals in the reducible (currently
  // used as an endmarker(-s) (akin \0 in C-strings) in some extReducibles=1/2 BCP methods)

  // NB: total size of a reducible in #ints = offsetIntsOfNogoodInReducible + nogoodSize + closingIntsAfterNogoodInReducible
  //  !! Observe that this might be smaller than the size allocated for the reducible (since learned nogoods might be
  // put into larger slots from deleted older nogoods). Use the Int value at offsetIntsOfNogoodInReducible - 3 (see below) to
  // find out the number of bytes actually allocated (using UNSAFE) for the reducible's slot in memory.

  // Layout of memory at a NogoodReducible **if NOT extReducibles3/4/5** (for extReducibles 3/4/5 see above):
  // Int at index 0 = length (#elis) of nogood (number of literals (elis)),
  // Long(!) at index 1 with extReducibles1/2: start address for the next false or unassigned eli search in nogood
  // If extReducibles == 1:
  //     Int at index 3 = W1,
  //     Int at index 4 = W2.
  // Float at index offsetIntsOfNogoodInReducible - 4: Nogood activity (only with appropriate nogood scoring approaches, see scoringForRemovalOfLearnedNogoods)
  // Int at index offsetIntsOfNogoodInReducible - 3:  size (in number of Ints!) of entire allocated memory slot for reducible of a learned nogood (might be larger than the minimum size needed to store the nogood and its metadata, because of recycling of deleted old learned reducibles)
  // Int at index offsetIntsOfNogoodInReducible - 2: in some configurations (see code): #usesInBCPs
  // Int at index offsetIntsOfNogoodInReducible - 1: LBD (learned nogoods only)
  // From index offsetIntsOfNogoodInReducible on: the actual nogood (as a sequence of elis (literals) as Ints)
  // After nogood (that is, starting at int-index (offsetIntsOfNogoodInReducible+nogoodSize)):
  //  closingIntsAfterNogoodInReducible*Int filled with 0 (e.g., as nogood end marker pseudo-eli 0 utilized by some fillUp procedures)
  //
  // Also see generateNogoodReducible(), conflictAnalysis() and printInfoAboutReducible()
  //sharedDefs.offsetIntsOfNogoodInReducible = offsetIntsOfNogoodInReducible

  //val alignmentForClarkNogoodReducibles = 0 // in bytes. > 0 had no visible effect on my machine except using up more memory.

  val ensuredMaxNoElisInNogoodForProductRepresentationWithExt5 = (Math.log(Long.MaxValue) / Math.log(noOfAbsElis)).toInt

  /*
  var requiredSpaceForClarkReducibles: Long = 0l // we need this for initializing nogiClarkToNogoodReducible in SolverMulti

  var nogi: Nogi = 0

  while (nogi < clarkNogoodsFinal.length) {

    requiredSpaceForClarkReducibles += ((clarkNogoodsFinal(nogi).sizev + offsetIntsOfNogoodInReducible + 1) << 2) + alignmentForClarkNogoodReducibles

    nogi += 1

  }*/

  if (debug2) {

    println("First 100 'clark' nogoods (after preprocessing):")

    println(clarkNogoodsFinal.take(100).mkString("\n"))

  }

  val positiveDependencyGraph: Int2ObjectOpenHashMap[List[Eli]] = if (satMode) new Int2ObjectOpenHashMap[List[Eli]]() else rulesOpt.map(rules => {

    if (debug2) {

      println("Rules extracted from aspif:\n")

      println(rules.map(_.toString(this.symbols)).mkString("\n"))

      println("-----------\n")

    }

    computeDependencyGraph(rules, noOfPosAtomElis) // TODO: exempt dummy symbols

  }).getOrElse(new Int2ObjectOpenHashMap[List[Eli]]())

  val progIsTight: Boolean = if (satMode) true else isAcyclic(positiveDependencyGraph)

  if (!satMode) (if (progIsTight && verbose) println("\nProgram is tight") else if (verbose) println("\nProgram is not tight"))

  if (emitASPpositiveDependencyGraph) { // for debugging purposes. Open resulting DOT file in Mathematica using, e.g.,
    // Import["C:\\Users\\Owner\\workspaceScala211\\DelSAT\\depGraphPosNeg.dot", ImagePadding -> 10]

    if (satMode)
      stomp(-10000, "Dependency graph can only be generated in ASP mode")

    val emitDepGraphPosNeg = true

    val reverseDepGraph = false

    val showEdgeLabels = true

    val showNotAsEdgeLabelOnly = true

    val showNegEdgesInRed = true

    val dependencyGraph: Int2ObjectOpenHashMap[List[Eli]] = rulesOpt.map(rules => {

      computeDependencyGraph(rules, noOfPosAtomElis, positiveDepGraph = true /*false*/) // TODO: exempt dummy symbols

    }).getOrElse(new Int2ObjectOpenHashMap[List[Eli]]())

    val nodesForDot = ArrayBuffer[String]()

    val edgesForDot = ArrayBuffer[String]()

    @inline def eliToStr(eli: Eli): String = (if (isPosEli(eli)) symbols(eli - 1) else "not " + symbols(negateNegEli(eli) - 1))

    val nodesAsElis: IntSet = dependencyGraph.keySet

    val nit = nodesAsElis.iterator

    while (nit.hasNext) { // all rule heads (must be positive, negative heads should have already been translated away by this point)

      val nodeEli = nit.nextInt()

      assert(isPosEli(nodeEli), "Error: negative head elis in aspif not supported")

      val nodeStr = nodeEli.toString

      nodesForDot.append(nodeStr + " [label=\"" + symbols(nodeEli - 1) + "\"]")

      println("Node added for eli: " + nodeStr)

    }

    val dges = dependencyGraph.int2ObjectEntrySet

    val dgesit = dges.iterator

    while (dgesit.hasNext) {

      val dge: Int2ObjectMap.Entry[List[Eli]] = dgesit.next()

      val parentNodeEli = dge.getIntKey

      println("parentNodeEli: " + parentNodeEli + "(" + symbols(parentNodeEli - 1) + ")")

      print("   descendants: ")

      val descendantElis: Seq[Eli] = dge.getValue

      val deit = descendantElis.iterator

      while (deit.hasNext) {

        val descendantEli = deit.next()

        print(descendantEli + "(" + eliToStr(descendantEli) + "), ")

        val edgeStr = symbols(parentNodeEli - 1) + (if (reverseDepGraph) "<-" else "->") + eliToStr(descendantEli)

        val edgeForDot = (if (reverseDepGraph) toAbsEli(descendantEli) + " -> " + parentNodeEli else parentNodeEli + " -> " + toAbsEli(descendantEli)) +
          (if (showEdgeLabels) " [label=\"" + (if (showNotAsEdgeLabelOnly) (if (isNegEli(descendantEli)) "not" else "") else edgeStr) + "\"]" else "") + (if (showNegEdgesInRed && isNegEli(descendantEli)) " [color=red]" else "")
        // NB: Mathematica doesn't show red color or other style attriibutes for edges imported from DOT (but parses these into Graph format!)

        edgesForDot.append(edgeForDot)

        //println("toAbsEli(descendantEli): " + toAbsEli(descendantEli))

      }

      println

    }

    if (emitDepGraphPosNeg) {

      println("Writing positive dependency graph to .dot file (open with, e.g., GraphViz)")

      val dotGraphStr = "digraph dependencyGraphPos {\n" + nodesForDot.mkString("\n") + "\n" + edgesForDot.mkString("\n") + "\n}"

      new PrintWriter("dependencyGraphPos.dot") {

        write(dotGraphStr)

        close

      }

      sys.exit(0)

    }

    scala.io.StdIn.readChar()

    sys.exit(0)

  }

  val costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE = mutable.HashMap[Eli, DifferentialFunction[DoubleReal]]()
  // Note ^: this is needed only for the simplified (faster) approach where each partial derivative is computed from an inner cost
  // term, e.g., in case of MSE. I.e., with --solverarg "partDerivComplete" "false"

  val nablasInner /*partial derivatives of the inner cost functions wrt. parameter atoms (as freqx variables)*/ : Array[DifferentialFunction[DoubleReal]] =
    Array.fill[DifferentialFunction[DoubleReal]](symbols.length + 1 /*if we could place
the uncertain atoms at the beginning of symbols, we could keep this array smaller, but this would require costly re-ordering operations
in aspifParse() */)(null.asInstanceOf[DifferentialFunction[DoubleReal]])

  val dFFactory = new diff.DifferentialFunctionFactoryStasp()

  val eliToVariableInCostFunctions: mutable.Map[Eli, Variable[DoubleReal]] = costsOpt.map(_.eliToVariableInCostFunctions).getOrElse(mutable.HashMap[Int, Variable[DoubleReal]]())
  // ^ for each measured eli, the corresponding autodiff.Variable within the inner cost. We can only differentiate wrt. parameter elis which are contained in this map.

  val symbolToAbsEli: Predef.Map[String, Eli] = if (aspifOrDIMACSParserResult.symbolToEliOpt.isDefined && aspifOrDIMACSParserResult.symbols.length == symbols.length && !preProcesssVariableElimConfig._5)
    aspifOrDIMACSParserResult.symbolToEliOpt.get
  else
    (Array("000" /*dummy, since eli 0 doesn't exist*/) ++ symbols).zipWithIndex.toMap // TODO: symbolsWithElis nutzen?

  val parameterAtomsElis0 /*(from  the "pats" line)*/ : Array[Eli] = costsOpt.map(_.parameterAtomsSeq).map(pmasg =>
    pmasg.map(pred => symbolToAbsEli(pred))).getOrElse(Array[Eli]())

  @inline def measuredAtomNameInCostFnToSymbol(n: String): String = if (satMode) n.stripPrefix("v") else n.replaceAllLiterally(" ", "")

  val measuredAtomsElis /*(from within the cost functions)*/ : Array[Eli] = costsOpt.map(_.measuredAtomsSeq).map(_.map((vn: Pred) =>
    symbolToAbsEli(measuredAtomNameInCostFnToSymbol(vn)))).getOrElse(Array[Eli]())

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

  def setCostFctsInner: Unit = {

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

  @inline def findInnerCostFunForParameterAtom_ForPartDerivINCOMPLETE(parameterAtomEli: Eli): Option[DifferentialFunction[DoubleReal]] = {

    assert(!partDerivComplete) // works only with partDerivComplete=false

    costFctsInnerWithPossMeasuredElis_ForPartDerivINCOMPLETE.get(parameterAtomEli) //costFctsInnerWithPossMeasuredElis.find(_._2 == parameterAtomEli)

  }

  if (showIntermediateTimers)
    println("\npreptimer 3: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val parameterAtomsElis = parameterAtomsElis0

  val innerCostFunForParamAtomEli_ForPartDerivINCOMPLETE = if (ignoreParamVariablesR || partDerivComplete) mutable.Map[Eli, Option[DifferentialFunction[DoubleReal]]]() else
    mutable.HashMap[Eli, Option[DifferentialFunction[DoubleReal]]]().++(parameterAtomsElis.map(eli => {

      // NB: implicit assumption for !partDerivComplete is that measured atoms = parameter atoms

      eli -> findInnerCostFunForParameterAtom_ForPartDerivINCOMPLETE(eli)

    }).toMap)

  if (showIntermediateTimers)
    println("\npreptimer 4: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val n = dFFactory.`val`(new DoubleReal(costFctsInner.length.toDouble))

  val totalCostFun_forPartDerivCompl: DifferentialFunction[DoubleReal] = if (costFctsInner.isEmpty) dFFactory.`val`(new DoubleReal(-1 /*dummy*/)) else
    costFctsInner.reduceLeft((reduct: DifferentialFunction[DoubleReal], x: DifferentialFunction[DoubleReal])
    => {

      innerCostReductFun(reduct, x)

    }
    ).div(n)

  // We store the partial derivatives of the cost function(s) in nablasInner:
  if (!ignoreParamVariablesR && (!allowNumFiniteDiff || mixedScenario))
    parameterAtomsElis.foreach(parameterAtomEli => {

      if (eliToVariableInCostFunctions.contains(parameterAtomEli)) { // otherwise, we have an abductive reasoning situation (handled currently by numerical finite differences)

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

        if (debug) println("   part derivative wrt parameter atom " + symbols(parameterAtomEli - 1) + ": " + nablasInner(parameterAtomEli))

      }

    })

  if (showIntermediateTimers)
    println("\npreptimer 5: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  val parameterAtomsElisSet: Set[Eli] = parameterAtomsElis.toSet

  val parameterLiteralElisArray = parameterAtomsElis ++ parameterAtomsElis.map(negatePosEli(_))

  val parameterLiteralElis: IntArrayUnsafeS = new IntArrayUnsafeS(parameterLiteralElisArray) // (might be empty)

  if (verbose) {

    println("\nMeasured atoms (after adding parameter atoms not occurring in cost): " + measuredAtomsElis.map(e => symbols(e - 1)).mkString(" ") +
      "Parameter atoms: " + parameterAtomsElisSet.map(e => symbols(e - 1)).mkString(" "))

  }

  @inline def deficitByDeriv(parameterLiteralEli: Eli): Double = {

    // Assumes that in a step directly preceding the re-sorting, the freqx variables in the nablaInner have been
    // updated to measuredAtomEliToStatisticalFreq!

    val r = if (isPosAtomEli(parameterLiteralEli)) {

      if (nablasInner(parameterLiteralEli) != null) {

        nablasInner(parameterLiteralEli).getReal

      } else
        return Double.NaN

    } else {

      if (nablasInner(negateNegEli(parameterLiteralEli)) != null)
        -nablasInner(negateNegEli(parameterLiteralEli)).getReal
      else
        return Double.NaN

    }

    if (r.isNaN)
      0.5d - rngGlobal.nextDouble()
    else
      r

  }

  var deficitOrderedUncertainLiteralsForJava: Array[Integer] = parameterLiteralElisArray.map(new Integer(_))

  if (debug) {

    println("Parameter elis:")

    parameterLiteralElisArray.foreach(p => if (isPosEli(p)) println(p + " = " + symbols(p - 1)) else println(p + " = not " + symbols(negateNegEli(p) - 1)))

  }

  if (shuffleRandomVariables)
    shuffleArray(deficitOrderedUncertainLiteralsForJava, rngGlobal)

  if (showIntermediateTimers)
    println("\npreptimer 6: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  // ! Not to be confused with eliToReduciblesClark which is similar (TODO: unify?)
  val eliToNogisClark: Array[ArrayValExtensibleIntUnsafe] = if (initAbsElisArrangementP.alternatives.values.toSeq.contains(9) || initAbsElisArrangementP.alternatives.values.toSeq.contains(10) ||
    clusterAbsElis && noOfPosAtomElis <= clusterAbsElisIfVarsMax) {

    val eliToNogisClark = Array.ofDim[ArrayValExtensibleIntUnsafe](noOfAllElis + 1) // per each eli, all nogis which contain that eli
    //NB: in the context of both SAT and ASP, "nogisClark" refers to the nogoods from the input CNF/Aspif (but perhaps cleaned/simplified), without any learned nogoods (loop nogoods or other learned nogoods)

    var ei = 1

    while (ei <= noOfAbsElis) { // we don't initialize eliToNogisClark lazily, since there might be elis which don't occur in nogoods

      eliToNogisClark(eliToJavaArrayIndex(ei)) = new ArrayValExtensibleIntUnsafe(new IntArrayUnsafeS(3), 0)

      eliToNogisClark(eliToJavaArrayIndex(negatePosEli(ei))) = new ArrayValExtensibleIntUnsafe(new IntArrayUnsafeS(3), 0)

      ei += 1

    }

    var nogj = 0

    val cnl = clarkNogoodsFinal.length

    while (nogj < cnl) {

      clarkNogoodsFinal(nogj).forEach(sideEffect = eliInNogood => {

        eliToNogisClark(eliToJavaArrayIndex(eliInNogood)).append(nogj)

      })

      nogj += 1

    }

    eliToNogisClark

  } else null

  case class AbsEliClusterable(absEli: Eli) extends org.apache.commons.math3.ml.clustering.Clusterable {

    override def getPoint: Array[Double] = Array[Double](absEli.toDouble)

  }

  val absEliClusters: util.List[CentroidCluster[AbsEliClusterable]] = if (clusterAbsElis && noOfPosAtomElis <= clusterAbsElisIfVarsMax) {

    val absEliAbsEliDistanceCache = new mutable.HashMap[Set[Eli], Double]()

    val t = System.nanoTime()

    @inline def absEliAbsEliDistance(absEliX: Eli, absEliY: Eli): Double = {

      absEliAbsEliDistanceCache.getOrElseUpdate(Set(absEliX, absEliY), {

        val r = {

          if (absEliX == absEliY)
            0
          else {

            val nogisWithXPos = eliToNogisClark(eliToJavaArrayIndex(absEliX)).getContent

            val nogisWithXNeg = eliToNogisClark(eliToJavaArrayIndex(negatePosEli(absEliX))).getContent

            val nogisWithYPos = eliToNogisClark(eliToJavaArrayIndex(absEliY)).getContent

            val nogisWithYNeg = eliToNogisClark(eliToJavaArrayIndex(negatePosEli(absEliY))).getContent

            var inCommon = 0

            var xi = 0

            while (xi < nogisWithXPos.length) {

              if (nogisWithYPos.contains(nogisWithXPos(xi)))
                inCommon += 1

              xi += 1

            }

            xi = 0

            while (xi < nogisWithXPos.length) {

              if (nogisWithYNeg.contains(nogisWithXPos(xi)))
                inCommon += 1

              xi += 1

            }

            xi = 0

            while (xi < nogisWithXNeg.length) {

              if (nogisWithYPos.contains(nogisWithXNeg(xi)))
                inCommon += 1

              xi += 1

            }

            xi = 0

            while (xi < nogisWithXNeg.length) {

              if (nogisWithYNeg.contains(nogisWithXNeg(xi)))
                inCommon += 1

              xi += 1

            }

            // println(inCommon)

            if (inCommon == 0)
              1d
            else
              1d / inCommon.toDouble

          }
        }

        //if(r != 0) println(r)
        r

      })

    }

    class AbsEliAbsEliDistance extends org.apache.commons.math3.ml.distance.DistanceMeasure {

      override def compute(a: Array[Double], b: Array[Double]): Double =
        absEliAbsEliDistance(absEliX = a(0).toInt, absEliY = b(0).toInt)

    }

    val absEliClusterer = new org.apache.commons.math3.ml.clustering.KMeansPlusPlusClusterer[AbsEliClusterable](200, 1000, /*100, 100d, -1,*/
      new AbsEliAbsEliDistance() /*,  new JDKRandomGenerator((System.currentTimeMillis() << 3).toInt),
KMeansPlusPlusClusterer.EmptyClusterStrategy.LARGEST_VARIANCE*/)
    // ^^^^we could also use FuzzyKMeansClusterer, in which case an absEli could be member of multiple clusters. In this case,
    // we would need to modify absEliClusteredMap appropriately (making it map from absEli to a set of cluster indices)

    val points = new java.util.ArrayList[AbsEliClusterable](noOfAbsElis)

    (1 to noOfAbsElis).foreach(absEli => points.add(AbsEliClusterable(absEli)))

    val absEliClusters: util.List[CentroidCluster[AbsEliClusterable]] = absEliClusterer.cluster(points)

    if (showIntermediateTimers)
      println("Time for absEli clustering / k-means: " + timerToElapsedMs(t) + "ms")

    if (showIntermediateTimers)
      println("\npreptimer 9b: " + timerToElapsedMs(timerPrepNs) + " ms\n")

    absEliClusters

  } else
    null.asInstanceOf[util.List[CentroidCluster[AbsEliClusterable]]]

  import scala.collection.JavaConverters._

  val absEliClustered: Array[Array[Eli]] = if (absEliClusters != null) // TODO: keep?
    absEliClusters.asScala.toArray.distinct.map((cluster: CentroidCluster[AbsEliClusterable]) =>
      cluster.getPoints.asScala.toArray.map(point => point.absEli))
  else
    null.asInstanceOf[Array[Array[Eli]]]

  if (debug2 && absEliClustered != null) println("absEliClustered:\n" + absEliClustered.map(_.mkString("; ")).mkString("\n"))

  val absEliClusterMaps = if (absEliClustered != null) {

    val absElisGrouped: mutable.Seq[(mutable.Buffer[Eli], Int)] = absEliClusters.asScala.zipWithIndex.map((tuple: (CentroidCluster[AbsEliClusterable], Int)) =>
      (tuple._1.getPoints.asScala.map(_.absEli), tuple._2))

    val absEliClusteredMap: Int2IntOpenHashMap = new Int2IntOpenHashMap()
    absElisGrouped.foreach /*flatMap*/ ((tuple: (mutable.Buffer[Eli], Int)) =>
      tuple._1.foreach(tx => absEliClusteredMap.put(tx, tuple._2)))

    absEliClusteredMap

  } else
    null.asInstanceOf[Int2IntOpenHashMap]

  val absEliClusteredMap: Int2IntOpenHashMap = absEliClusterMaps

  if (debug2 && absEliClustered != null) {

    // println("absEliClusteredMap:\n" + absEliClusteredMap.mkString("\n"))

    //println("absEliClusterSizeMap:\n" + absEliClusterSizeMap.mkString("\n"))

  }

  @inline def eliToJavaArrayIndex(eli: Eli): Int = eli + noOfAbsElis // to use a +/- eli as index into a "safe" (Java/Scala) array

  if (verbose)
    println("\nPreparation time final: " + timerToElapsedMs(timerPrepNs) + " ms\n")

  def computeClarkNogis(rules: ArrayBuffer[Rule]): (Array[IntArrayUnsafeS], java.util.HashMap[Eli, Array[Eli]], java.util.HashMap[Eli, Array[Eli]]) = {

    // Nogood generation largely follows (with a few minor differences) https://www.cs.uni-potsdam.de/wv/pdfformat/gekanesc07a.pdf

    // NB: the following algorithm assumes that all rules are normal. E.g., :- integrity constraints are not allowed (need
    // to translated away during preprocessing/grounding of the original ASP program, see AspifParser).

    // Deprecated: in SATmode, we could in earlier version end up in this method only with experimental flag generatePseudoRulesForNogoodsForSATMode = true,
    // otherwise in SAT mode all nogoods have already been generated entirely from the CNF clauses.
    assert(!satMode)

    val exclEmptyBodyInDeltaAtoms = false // true simplifies nogoods from empty bodies, but without prior resolution during solving it can also increase solving time (simpler != faster)

    val test = false // must be false (true for current debugging purposes)

    val thresholdForSymbolsPar = 1000000

    val thresholdForRulesPar = 1000000

    val noOfThreads = (Runtime.getRuntime().availableProcessors() / 2).max(1)

    @deprecated val createFalsNgs: Boolean = false

    val specialConstrRuleNogoods: Boolean = false // TODO: must be false (true doesn't work yet); if true, we create an alternative form of nogoods for :- constraints (see code)

    assert(!specialConstrRuleNogoods)

    val rulesWoConstr = if (!specialConstrRuleNogoods) rules else /*we create special nogoods later for the omitted ones: */
      rules.filterNot(rule => isPosEli(rule.headAtomsElis.head) && isFalsAuxAtom(symbols(rule.headAtomsElis.head - 1)))

    val noOfThreadsNg = if (rulesWoConstr.length < thresholdForRulesPar) 1 else noOfThreads

    val rulesPartitioning: Iterator[ArrayBuffer[Rule]] = if (rulesWoConstr.isEmpty) Iterator(ArrayBuffer[Rule]()) else rulesWoConstr.grouped(if (noOfThreadsNg == 1 || rulesWoConstr.length < noOfThreadsNg - 1) rulesWoConstr.length else rulesWoConstr.length / (noOfThreadsNg - 1))

    val negBlitToPosBodyElis: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    val posHeadAtomToNegBlits: java.util.HashMap[Eli, Array[Eli]] = new java.util.HashMap[Eli, Array[Eli]]()
    // ^ we need this only for loop nogood generation in ASP; could be omitted for SAT or tight problems

    if (showIntermediateTimers)
      println("\npreptimer 0: " + timerToElapsedMs(timerPrepNs) + " ms\n")

    def deltaBetaPartComp(rulesPart: ArrayBuffer[Rule]): ArrayBuffer[IntArrayUnsafeS] = { // generate body nogoods

      val deltaBetaPart = mutable.ArrayBuffer[IntArrayUnsafeS]()

      //deltaBetaPart.sizeHint(rulesWoConstr.length * 5 + 1000)

      assert(!test)

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

          deltaBetaPart.append(new IntArrayUnsafeS(s1)) // δ(β)

          negBlitToPosBodyElis.put(blitNegated, bpos) // we need this later re loop nogoods

          val s2pos: Array[IntArrayUnsafeS] = bpos.map(eli => new IntArrayUnsafeS(Array(blit, negatePosEli(eli))))

          deltaBetaPart.appendAll(s2pos) // Δ(β)

          val s2neg: Array[IntArrayUnsafeS] = bneg.map(eli => new IntArrayUnsafeS(Array(blit, negateNegEli(eli))))

          deltaBetaPart.appendAll(s2neg) // Δ(β)

        }

        ri += 1

      }

      if (showIntermediateTimers)
        println("\npreptimer1: " + timerToElapsedMs(timerPrepNs) + " ms\n")

      deltaBetaPart

    }

    def deltaAtomsComp(omit: Boolean): mutable.ArrayBuffer[IntArrayUnsafeS] = { // generate head/atom-related nogoods

      val deltaAtoms = mutable.ArrayBuffer[IntArrayUnsafeS]()

      if (!omit) {

        //deltaAtoms.sizeHint(symbols.length * 5 + 1000)

        if (showIntermediateTimers)
          println("\npreptimer2a: " + timerToElapsedMs(timerPrepNs) + " ms\n")

        val rulesGroupedByTheirHeadEli = Array.fill[ArrayBuffer[Rule]](noOfAllElis + 1)(ArrayBuffer[Rule]())

        var rwci = 0

        val rwcl = rulesWoConstr.length

        while (rwci < rwcl) {

          val rule: Rule = rulesWoConstr(rwci)

          val h: Eli = rule.headAtomsElis.headOption.getOrElse({
            assert(false);
            0
          })

          rulesGroupedByTheirHeadEli(eliToJavaArrayIndex(h) /*since elis ranges are [-noOfAbsElis..-1], [1..noAbsElis] */).append(rule) //***

          rwci += 1

        }

        if (showIntermediateTimers)
          println("\npreptimer2b: " + timerToElapsedMs(timerPrepNs) + " ms\n")

        val eliListsAll = (1 to noOfPosAtomElis)

        // (Deprecated: ^ all positive and negative literals except blits. Note that negative head lits should not (yet) occur in ASP mode, these
        //   are only generated if there are pseudo-rules active (also currently not) in SAT-mode. )

        (if (eliListsAll.size > thresholdForSymbolsPar) eliListsAll /*.par*/
        else eliListsAll).flatMap { atomEli_p => {
          // TODO: .par doesn't work with Scala 2.13.1 (also see import scala.collection.parallel.CollectionConverters._ )

          // TODO: We should optionally treat #external atoms here specially, even if they don't occur in any rules, in which case nogoods are generated for them to ensure they are never true.

          val bodiesOfp: ArrayBuffer[Rule] = rulesGroupedByTheirHeadEli(eliToJavaArrayIndex(atomEli_p)) //*** NB: this also includes empty bodies!

          val s1s2 = ArrayBuffer[IntArrayUnsafeS]()

          var isFact = false

          if (!satMode /*see above*/ || !bodiesOfp.isEmpty) {

            if (bodiesOfp.isEmpty && isPosEli(atomEli_p) && !symbols(atomEli_p - 1).startsWith(auxPredPrefixBase))
              stomp(-5005, symbols(atomEli_p - 1))

            s1s2.sizeHint(bodiesOfp.length + 1)

            if (!bodiesOfp.isEmpty) {

              val negHeadAtomEli: Eli = negateEli(atomEli_p)

              bodiesOfp.foreach(rule => { // Δ(p)

                s1s2.append(if (exclEmptyBodyInDeltaAtoms && (
                  rule.blit == emptyBodyBlit) || isFact) {

                  isFact = true

                  new IntArrayUnsafeS(Array(negHeadAtomEli))

                } else
                  new IntArrayUnsafeS(Array(negHeadAtomEli, rule.blit)))

              })

            }

            assert(!satMode) // (in satMode (which doesn't use this method anyway), the following would only be allowed if we
            // create _all_ possible pseudo-rules (for all clauses and heads), otherwise the following can lead to wrong UNSAT:)

            // TODO:  handle #external atoms here (currently ignored / treated as undefined unless defined by some rule):

            if (true || /*nope:*/ ((bodiesOfp.length > 1 || bodiesOfp.length == 1 && bodiesOfp.head.blit != emptyBodyBlit))) { // δ(p)  |||

              val s2NogoodBuffer = new IntArrayUnsafeS(bodiesOfp.length + 1) //Array.ofDim[Eli](bodiesOfp.length + 1)

              var s2i = 0

              bodiesOfp.foreach(rule => { // ? note: if we do this even if bodiesOfp is empty, which creates false-enforcing nogoods for undefined symbols

                s2NogoodBuffer.update(s2i, negateEli(rule.blit))

                s2i += 1

              })

              s2NogoodBuffer(s2i) = atomEli_p

              posHeadAtomToNegBlits.put(atomEli_p, s2NogoodBuffer.toArray(0, s2i)) // we'll need this later re loop nogoods

              s1s2.append(s2NogoodBuffer)

            }

            Some(s1s2 /*.distinct*/)

          } else
            None

        }
        }.seq.foreach(deltaAtoms.appendAll(_))

        if (showIntermediateTimers)
          println("\npreptimer2: " + timerToElapsedMs(timerPrepNs) + " ms\n")

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

      val deltas: ArrayBuffer[ArrayBuffer[IntArrayUnsafeS]] = Await.result(Future.sequence(Seq(deltaAtomsFuture) ++ deltaBetaFutures), Duration.Inf).to(ArrayBuffer)

      deltas.flatten

    }

    val falsNogoods: ArrayBuffer[IntArrayUnsafeS] = if (createFalsNgs)
      symbolsWithPosElis.filter(si => isFalsAuxAtom(si._1)).map(x => new IntArrayUnsafeS(Array(x._2))).to(ArrayBuffer)
    else if (!specialConstrRuleNogoods) ArrayBuffer[IntArrayUnsafeS]() else {

      // we add special nogoods for rules which have been (elsewhere) resulted from constraints :- b1, b2, ...

      val contraintRules = rules.filter(rule => isPosAtomEli(rule.headAtomsElis.head) && isFalsAuxAtom(symbols(rule.headAtomsElis.head - 1)))

      contraintRules.map(rule => new IntArrayUnsafeS(rule.bodyPosAtomsElis ++ rule.bodyNegAtomsElis.filterNot(_ == negateEli(rule.headAtomsElis.head))))

    }

    if (debug) println("# special constraint rule nogoods = " + falsNogoods.length)

    val r = deltaClark ++ falsNogoods

    (r.toArray, posHeadAtomToNegBlits, negBlitToPosBodyElis)

  }

  @inline def computeLeastHerbrandDefClauses(posDefClauseProg: Seq[Rule]): IntOpenHashSet = {

    val m = new IntOpenHashSet()

    var conv = false

    @inline def tp: Unit = {

      posDefClauseProg.foreach((rule: Rule) => {

        if (rule.bodyPosAtomsElis.forall(m.contains(_)))
          m.add(rule.headAtomsElis.headOption.getOrElse(0 /* *** -1*/))

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

    // We compute the Gelfond-Lifschitz reduct with the extension that for double negation, we use the
    // definition from Lifschitz et al: Nested Expressions in Logic Programs

    val r1: Seq[Rule] = rules.filterNot {
      _.bodyNegAtomsElis.exists(negEli /* modelCandidate contains positive atomic elis only (i.e., "not a"'s are omitted), so we need to check for negated negEli: */ => {

        val x = negateNegEli(negEli)

        modelCandidate._2.contains(x)

      }
      )
    }

    val r2: Seq[Rule] = r1.flatMap { rule => { // we now examine the (eliminated) double negations in rule bodies, using the
      // extended reduct definition in Lifschitz et al: Nested Expressions..., Sect. 3 and
      // Sect. 7.1 in Lierer's PhD thesis
      // (but observe the typo in the rule for (not F)^X (interchanged top/bottom) on page 31).

      val removeRule = rule.bodyPosAtomsElis.exists(posEliInBody => {

        if (rule.elisFromDoubleNegationsInBodyPosAtomsElis.contains(posEliInBody)) { // this eli stems from "not not" in the original body

          val x = posEliInBody

          val r = !modelCandidate._2.contains(x) // i.e., (not (not F)^X) = Bottom, i.e., we omit the entire rule from the reduct

          r

        } else
          false

      }
      )

      if (removeRule)
        None
      else {

        val newBodyPosAtomsElis = rule.bodyPosAtomsElis.flatMap(posEliInBody => {

          if (rule.elisFromDoubleNegationsInBodyPosAtomsElis.contains(posEliInBody /*WithIndex._2*/)) { // this eli stems from "not not" in the original body

            val x = posEliInBody

            val r = modelCandidate._2.contains(x)

            if (r) // i.e., (not (not F)^X) = Top, i.e., we omit this body literal from the rule's body
              None
            else
              Some(posEliInBody)

          } else
            Some(posEliInBody)

        })

        Some(Rule(headAtomsElis = rule.headAtomsElis,
          bodyPosAtomsElis = newBodyPosAtomsElis,
          bodyNegAtomsElis = rule.bodyNegAtomsElis,
          blit = rule.blit,
          elisFromDoubleNegationsInBodyPosAtomsElis = rule.elisFromDoubleNegationsInBodyPosAtomsElis))

      }

    }

    }

    val reduct: Seq[Rule] = r2.map(r => new Rule(headAtomsElis = r.headAtomsElis,
      bodyPosAtomsElis = r.bodyPosAtomsElis, bodyNegAtomsElis = Array[Eli](), blit = 0 /* ***  -1*/))

    val lhm = computeLeastHerbrandDefClauses(reduct)

    val isAS =
      if (lhm.contains(0
        /*i.e., false, from a ':- ...' constraint */))
        (false, modelCandidate._1)
      else {

        val isStableModel = modelCandidate._2.equals(lhm)

        // Iff we were guaranteed that modelCandidate is already a supported model, it was
        // sufficient to say isStableModel <=> modelCandidate.--(lhm).isEmpty (see revisedASSAT paper).

        // Make sure to use the revised ASSAT paper (http://www.cs.ust.hk/~flin/papers/assat-aij-revised.pdf), the original paper
        // contains a severe typo.

        (isStableModel, if (isStableModel) Array[Eli]() else {

          val remainder: Array[Eli] = modelCandidate._1.filterNot(lhm.contains(_))

          remainder

        })

      }

    isAS

  }

  def computeDependencyGraph(rules: ArrayBuffer[Rule], noOfAllPosAtomElis: Int, positiveDepGraph: Boolean = true):
  Int2ObjectOpenHashMap[List[Eli]] /*adjacency list*/ = { // TODO: check

    assert(positiveDepGraph) // this is the only kind we require

    val graphInit = new Int2ObjectOpenHashMap[List[Eli]]()

    var jj = 0

    while (jj < rules.length) {

      val rule: Rule = rules(jj)

      if (!rule.headAtomsElis.isEmpty) {

        val headEli = rule.headAtomsElis.head

        if (!isPosEli(headEli))
          stomp(-5004, rule.toString)

        val successorNodes: Array[Eli] = if (positiveDepGraph) rule.bodyPosAtomsElis else rule.bodyPosAtomsElis. /*union*/ concat(rule.bodyNegAtomsElis)

        val assocs = graphInit.get(headEli)

        if (assocs == null) {

          graphInit.put(headEli, List[Eli]())

        }

        successorNodes.foreach(succEli => {

          graphInit.put(headEli, graphInit.get(headEli).:+(succEli))

        })
      }

      jj += 1

    }

    graphInit

  }

  @tailrec final def isAcyclic(depGraph: Int2ObjectOpenHashMap[List[Eli]]): Boolean = { // TODO: check again

    depGraph.isEmpty || {

      val leaveElisB = new mutable.ArrayBuilder.ofInt

      val nonLeaveGraphPart = ArrayBuffer[(Eli, List[Eli])]()

      val graphEntries: IntSet = depGraph.keySet()

      val graphEntriesIterator = graphEntries.iterator()

      while (graphEntriesIterator.hasNext()) {

        val key = graphEntriesIterator.nextInt()

        val v: List[Eli] = depGraph.get(key)

        if (v.isEmpty)
          leaveElisB.+=(key)
        else
          nonLeaveGraphPart.append((key, v))

      }

      val leaveElis: Array[Eli] = leaveElisB.result()

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
