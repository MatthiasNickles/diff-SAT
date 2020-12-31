/**
  * diff-SAT
  *
  * Copyright (c) 2018-2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package solving

import input.diffSAT.stomp
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import sharedDefs._
import utils.Various._
import utils.{ByteArrayUnsafeS, RandomLongSet}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** To test this approach in isolation, use command line options like this:
  *
  * *  --solverarg rephasePhaseMemo true --solverarg useSLSinPhaseMemoRephasingP "true" --solverarg allowEliToClarkReduciblesLookup true --solverarg maxInnerSLSTrials 200000000 --solverarg sasatOuterMaxInSLS 1 --solverarg minNoConflictsBeforeFirstRephasing 0 --solverarg rephasePhaseMemoIntervalInit 0 --solverarg maxSolverThreadsR 1 -n 1
  *
  */
object StochasticLocalSearch {

  def stochasticLocalSearch(singleSolverThreadData: SingleSolverThreadData,
                            solverThreadSpecificSettings: SolverThreadSpecificSettings,
                            sharedAmongSingleSolverThreads: SharedAmongSingleSolverThreads,
                            preparation: Preparation): Int = { // optionally called as a helper method during rephasing (not as our overall solving algo)
    // TODO: implement further SLS variants, such as probSAT / YalSAT

    import preparation._
    import singleSolverThreadData._
    import solverThreadSpecificSettings._

    val noOfSetElisPerNogoodInSLS = new Long2IntOpenHashMap(nogiClarkToNogoodReducible.size)

    if (!allowEliToClarkReduciblesLookup)
      stomp(-5009, "allowEliToClarkReduciblesLookup=true required for Stochastic Local Search")

    val walkSATnoise = walkSATnoiseR

    if (debug2) println("\nmaxInnerSLSTrials:  " + maxInnerSLSTrials)

    val minimumNoInnerItsBeforeNextRestartInSLS = (resetInnerSLSAfterPercentMaxInnerTrials * maxInnerSLSTrials).toInt

    var minimumNoInnerItsBeforeNextRestartCounterInSLS = minimumNoInnerItsBeforeNextRestartInSLS

    @inline def copySLSPhasesFromBestPhases: Unit = {

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        updateInPhasePreviousForAbsElis(absEli, bestPhasesQueue.front.get(absEli))

        absEli += 1

      }

    }

    @inline def initializeSLSPhasesRandomly = {

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        if (rngLocal.nextBoolean())
          updateInPhasePreviousForAbsElis(absEli, 0x00.toByte)
        else
          updateInPhasePreviousForAbsElis(absEli, 0x01.toByte)

        absEli += 1

      }

    }

    /*@inline def initializeSLSPhasesPartRandomlyPartBest = {

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        if (rngLocal.nextFloat() < 0.01) {

          if (rngLocal.nextBoolean())
            updateInPhasePreviousForAbsElis(absEli, 0x01.toByte)
          else
            updateInPhasePreviousForAbsElis(absEli, 0x00.toByte)

        } else {

          updateInPhasePreviousForAbsElis(absEli, bestPhasesQueue.front.get(absEli))

        }

        absEli += 1

      }

    }*/

    if (copyPhasesFromAssignmentInSLS) {

      if (copyPhasesFromBestPhasesInSLS)
        stomp(-5006)

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        if (isSetInPass(absEli))
          updateInPhasePreviousForAbsElis(absEli, 0x01.toByte)
        else
          updateInPhasePreviousForAbsElis(absEli, 0x00.toByte)

        absEli += 1

      }

    } else if (copyPhasesFromBestPhasesInSLS && !bestPhasesQueue.isEmpty) {

      copySLSPhasesFromBestPhases

    }

    @inline def isAbsEliSetAsPosInSLS(absEli: Eli): Boolean = getFromPhasePreviousForAbsElis(absEli) != 0x00.toByte

    @inline def isAbsEliSetAsNegInSLS(absEli: Eli): Boolean = getFromPhasePreviousForAbsElis(absEli) == 0x00.toByte

    @inline def isNogoodViolatedUnderAssumptionInSLS(nogoodReducible: NogoodReducible, assumptionAbsEli: Eli = 0, assumptionPhase: Byte = 0): Boolean = {

      var i = 0

      while (i < getNogoodSizeFromReducible(nogoodReducible)) {

        val eliInNogood = getEliFromNogoodInReducible(nogoodReducible, i)

        val absEliInNogood = toAbsEli(eliInNogood)

        if (absEliInNogood == assumptionAbsEli) {

          if (extraChecks) assert(assumptionAbsEli != 0)

          if (isPosEli(eliInNogood) && assumptionPhase == 0x00.toByte ||
            isNegEli(eliInNogood) && assumptionPhase != 0x00.toByte) {

            return false

          }

        } else {

          if (isPosEli(eliInNogood) && isAbsEliSetAsNegInSLS(absEliInNogood) ||
            isNegEli(eliInNogood) && isAbsEliSetAsPosInSLS(absEliInNogood)) {

            return false

          }

        }

        i += 1

      }

      true

    }

    @inline def countNoOfSetElisInNogoodInSLS(nogoodReducible: NogoodReducible): Eli = {

      var noOfSetElis = 0

      val absEliHashSet = if (extraChecks) mutable.HashSet[Eli]() else null.asInstanceOf[mutable.HashSet[Eli]]

      var i = 0

      while (i < getNogoodSizeFromReducible(nogoodReducible)) {

        val eliInNogood = getEliFromNogoodInReducible(nogoodReducible, i)

        //println(" eliInNogood: " + eliInNogood + " in nogood " + nogoodReducible)

        val absEliInNogood = toAbsEli(eliInNogood)

        if (extraChecks && !absEliHashSet.add(absEliInNogood))
          assert(false, "nogood with certain eli in pos and neg phase found") // TODO: adapt code so that this can be handled

        if (isPosEli(eliInNogood) && isAbsEliSetAsPosInSLS(absEliInNogood) ||
          isNegEli(eliInNogood) && isAbsEliSetAsNegInSLS(absEliInNogood)) {

          noOfSetElis += 1

        }

        i += 1

      }

      //println("noOfSetElis = " + noOfSetElis)

      noOfSetElis

    }

    @inline def initializeViolatedNogoodsInSLS(): Eli = {

      violatedNogoodsInSLS.clear()

      if (extraChecks) {

        val clarkNogoodsFromEliToReduciblesAll = mutable.HashSet[NogoodReducible]()

        var absEli = 1

        while (absEli <= noOfAbsElis) {

          val clarkReduciblesForPosEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(absEli))

          val clarkReduciblesForNegEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli)))

          clarkReduciblesForPosEli.toArrayBufferOfReducibles.foreach(clarkNogoodsFromEliToReduciblesAll.add(_))

          clarkReduciblesForNegEli.toArrayBufferOfReducibles.foreach(clarkNogoodsFromEliToReduciblesAll.add(_))

          absEli += 1

        }

        if (extraChecks) assert(nogiClarkToNogoodReducible.size == clarkNogoodsFromEliToReduciblesAll.size)

      }

      var violations = 0

      var nogi = 0

      while (nogi < nogiClarkToNogoodReducible.size) {

        val nogoodReducible = nogiClarkToNogoodReducible.get(nogi)

        //println("in initializeViolatedNogoods: checking nogood " + nogoodInReducibleToString(nogoodReducible))

        val noOfSetElisInNogood = countNoOfSetElisInNogoodInSLS(nogoodReducible)

        noOfSetElisPerNogoodInSLS.put(nogoodReducible, noOfSetElisInNogood)

        if (noOfSetElisInNogood == getNogoodSizeFromReducible(nogoodReducible)) {

          violatedNogoodsInSLS.add(nogoodReducible)

          violations += 1

          if (extraChecks) assert(isNogoodViolatedUnderAssumptionInSLS(nogoodReducible))

        }

        nogi += 1

      }

      violations

    }

    @inline def countViolatedNogoodsFromScratchInSLS: Eli = {

      var violations = 0

      var nogi = 0

      while (nogi < nogiClarkToNogoodReducible.size) {

        val nogoodReducible = nogiClarkToNogoodReducible.get(nogi)

        val noOfSetElisInNogood = countNoOfSetElisInNogoodInSLS(nogoodReducible)

        if (noOfSetElisInNogood == getNogoodSizeFromReducible(nogoodReducible)) {

          violations += 1

          if (extraChecks) assert(isNogoodViolatedUnderAssumptionInSLS(nogoodReducible))

          if (extraChecks) assert(violatedNogoodsInSLS.contains(nogoodReducible))

        }

        nogi += 1

      }

      violations

    }

    /*@inline def printViolatedNogoodsInSLS(): Unit = {

      println("\n--------- violated nogood:")

      var violations = 0

      var nogi = 0

      while (nogi < nogiClarkToNogoodReducible.size) {

        val nogoodReducible = nogiClarkToNogoodReducible.get(nogi)

        //println("in initializeViolatedNogoods: checking nogood " + nogoodInReducibleToString(nogoodReducible))

        if (isNogoodViolatedUnderAssumptionInSLS(nogoodReducible)) {

          println("   " + nogoodInReducibleToString(nogoodReducible) + " = " + nogoodReducible)

          violations += 1

        }

        nogi += 1

      }

      println("   #Violations = " + violations)
      //println("size = " + violatedNogoods.size)

      // println("\n-----------------------------------------------")

    }*/

    @inline def countViolatedNogoodsInSLS: Eli = violatedNogoodsInSLS.size

    @inline def updateForAffectedReduciblesInSLS(reduciblesInWhichEliWithOldPhaseOccurred: NogoodReduciblesSequenceUnsafe
                                                 /* ^ those reducibles from which after flipping the eli "would be" removed */ ,
                                                 reduciblesInWhichEliWithOldPhaseDidntOccur: NogoodReduciblesSequenceUnsafe
                                                 /* ^ those reducibles to which after flipping the eli "would be" added */): Unit = {

      /*if (extraChecks) {  // (requires update for new NogoodReduciblesSequenceUnsafe item format):

          assert(reduciblesInWhichEliWithOldPhaseOccurred.toArrayBuffer.distinct.length == reduciblesInWhichEliWithOldPhaseOccurred.size)

          assert(reduciblesInWhichEliWithOldPhaseDidntOccur.toArrayBuffer.distinct.length == reduciblesInWhichEliWithOldPhaseDidntOccur.size)

          assert(reduciblesInWhichEliWithOldPhaseOccurred.toArrayBuffer.toSet.intersect(reduciblesInWhichEliWithOldPhaseDidntOccur.toArrayBuffer.toSet).size == 0)

        }*/

      var i = 0

      while (i < reduciblesInWhichEliWithOldPhaseOccurred.size) {

        val affectedReducible: NogoodReducible = reduciblesInWhichEliWithOldPhaseOccurred.getReducibleUS(i)

        if (extraChecks) assert(!isNogoodViolatedUnderAssumptionInSLS(affectedReducible))

        violatedNogoodsInSLS.remove(affectedReducible)

        noOfSetElisPerNogoodInSLS.put(affectedReducible, noOfSetElisPerNogoodInSLS.get(affectedReducible) - 1)

        if (extraChecks) assert(countNoOfSetElisInNogoodInSLS(affectedReducible) == noOfSetElisPerNogoodInSLS.get(affectedReducible))

        i += 1

      }

      i = 0

      while (i < reduciblesInWhichEliWithOldPhaseDidntOccur.size) {

        val affectedReducible: NogoodReducible = reduciblesInWhichEliWithOldPhaseDidntOccur.getReducibleUS(i)

        val oldNoOfSetElisInNogood = noOfSetElisPerNogoodInSLS.get(affectedReducible)

        noOfSetElisPerNogoodInSLS.put(affectedReducible, oldNoOfSetElisInNogood + 1)

        if (extraChecks) assert(countNoOfSetElisInNogoodInSLS(affectedReducible) == noOfSetElisPerNogoodInSLS.get(affectedReducible))

        if (oldNoOfSetElisInNogood + 1 == getNogoodSizeFromReducible(affectedReducible) /*isNogoodViolatedUnderAssumptionInSLS(affectedReducible)*/ ) {

          violatedNogoodsInSLS.add(affectedReducible)

        } else {

          if (extraChecks) assert(!violatedNogoodsInSLS.contains(affectedReducible))

        }

        i += 1

      }

      if (extraChecks)
        assert(countViolatedNogoodsFromScratchInSLS == violatedNogoodsInSLS.size)

    }

    @inline def updateForAffectedReduciblesTentativeInSLS(reduciblesInWhichEliWithOldPhaseOccurred: NogoodReduciblesSequenceUnsafe
                                                          /* ^ those reducibles from which after flipping the eli "would be" removed */ ,
                                                          reduciblesInWhichEliWithOldPhaseDidntOccur: NogoodReduciblesSequenceUnsafe
                                                          /* ^ those reducibles to which after flipping the eli "would be" added */ ,
                                                          assumptionAbsEli: Eli = 0, assumptionPhase: Byte = 0): Int /*the predicted change to
                                                         cardinality of current set of violated nogoods*/ = {

      var removals = 0

      var additions = 0

      var i = 0

      while (i < reduciblesInWhichEliWithOldPhaseOccurred.size) {

        val affectedReducible: NogoodReducible = reduciblesInWhichEliWithOldPhaseOccurred.getReducibleUS(i)

        if (violatedNogoodsInSLS.contains(affectedReducible))
          removals += 1

        i += 1

      }

      i = 0

      while (i < reduciblesInWhichEliWithOldPhaseDidntOccur.size) {

        val affectedReducible: NogoodReducible = reduciblesInWhichEliWithOldPhaseDidntOccur.getReducibleUS(i)

        val isPredictedViolated = /*isNogoodViolatedUnderAssumptionInSLS(affectedReducible, assumptionAbsEli, assumptionPhase)*/
          noOfSetElisPerNogoodInSLS.get(affectedReducible) + 1 == getNogoodSizeFromReducible(affectedReducible)

        if (extraChecks) {

          assert(countNoOfSetElisInNogoodInSLS(affectedReducible) == noOfSetElisPerNogoodInSLS.get(affectedReducible))

          if (assumptionAbsEli != 0) {

            assert(isPredictedViolated == isNogoodViolatedUnderAssumptionInSLS(affectedReducible, assumptionAbsEli, assumptionPhase))

          }

        }

        if (isPredictedViolated) {

          if (extraChecks) assert(!violatedNogoodsInSLS.contains(affectedReducible))

          additions += 1

        } else {

          if (extraChecks) assert(!violatedNogoodsInSLS.contains(affectedReducible))

        }

        /* nope:
            if (!violatedNogoods.contains(affectedReducible))
                additions += 1
            else
              assert(false)
           */

        i += 1

      }

      additions - removals

    }

    var mostRecentlyFlippedAbsEliWhenLearning = 0

    @inline def flipInSLS(absEli: Eli): Unit = {

      //println("Flip: " + absEli)

      //println(getAbsEliScore(absEli))

      if (useScoresInSLS > 0f)
        bumpUpEVSIDSscoreOfAbsEliMinimally(absEli)

      val affectedReduciblesPosEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(absEli))

      val affectedReduciblesNegEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli)))

      if (isAbsEliSetAsPosInSLS(absEli)) {

        updateInPhasePreviousForAbsElis(absEli, 0x00.toByte)

        updateForAffectedReduciblesInSLS(affectedReduciblesPosEli, affectedReduciblesNegEli)

      } else {

        if (extraChecks) assert(isAbsEliSetAsNegInSLS(absEli))

        updateInPhasePreviousForAbsElis(absEli, 0x01.toByte)

        updateForAffectedReduciblesInSLS(affectedReduciblesNegEli, affectedReduciblesPosEli)

      }

      mostRecentlyFlippedAbsEliWhenLearning = absEli

      // println("violatedNogoodsInSLS.size = " + violatedNogoodsInSLS.size)

    }

    @inline def flipTentativeInSLS(absEli: Eli /*the absEli whose phase we pretend to flip*/): Int /*the predicted change in #violatedNogoods*/ = {

      val affectedReduciblesPosEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(absEli))
      // NB: eliToReduciblesClark is a data structure which is not normally maintained in CDNL; it needs to be activated
      // using allowEliToClarkReduciblesLookup=true in sharedDefs.scala

      val affectedReduciblesNegEli: NogoodReduciblesSequenceUnsafe = eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli)))

      if (isAbsEliSetAsPosInSLS(absEli)) {

        updateForAffectedReduciblesTentativeInSLS(affectedReduciblesPosEli, affectedReduciblesNegEli, assumptionAbsEli = absEli, assumptionPhase = 0x00.toByte)

      } else {

        //if(extraChecks) assert(isAbsEliSetAsNegInSLS(absEli))

        updateForAffectedReduciblesTentativeInSLS(affectedReduciblesNegEli, affectedReduciblesPosEli, assumptionAbsEli = absEli, assumptionPhase = 0x01.toByte)

      }

    }

    var temperatureInSLS = fixedTemperatureWithPlainWalkSAT //  -1d  // (initial value not meaningful if we use temperature decline)

    var decayRateForTempInSLS = -1d

    var sasaOuterI = 1

    assert(maxInnerSLSTrials > 0)

    var minViolatedNogoodsInSLS = Int.MaxValue

    do { // SASAT outer loop  (for WalkSAT, this is optional. Simply resets assignments to new random truth values)

      if (sasaOuterI > 1 || alwaysStartFromRandomPhasesInSLS) { // that means we (differently from original SASAT) use the last regular phase in the first sasaOuterI iteration and
        // only afterwards we use a random assignment

        initializeSLSPhasesRandomly

      }

      if (useSASATinSLS || walkSATwithTempDecl)
        decayRateForTempInSLS = if (decayRateSLS > 0f)
          decayRateSLS
        else
          1d / ((noOfRephasings + sasaOuterI).toDouble * clarkNogoodsFinal.length.toDouble) / -decayRateSLS

      if (debug2)
        println("\ndecayRateForTempInSLS = " + decayRateForTempInSLS)

      initializeViolatedNogoodsInSLS()

      var noOfInnerSLSTrials = 0

      var flipsInSASAT = 0

      val bestStateInSLS: Array[Byte] =
        if (!resetSLStoStoredBestState) null.asInstanceOf[Array[Byte]] else Array.ofDim[Byte](noOfAbsElis + 1)


      @inline def initTempInSLS: Unit = {

        temperatureInSLS = maxTempInSLS * Math.exp(-noOfInnerSLSTrials.toFloat * decayRateForTempInSLS)

      }

      while (noOfInnerSLSTrials < maxInnerSLSTrials && !stopSolverThreads) { // SASAT + WalkSAT inner loop

        val c = countViolatedNogoodsInSLS

        if (c == 0) {

          if (verbose)
            println("\n*** Stochastic Local Search (" + (if (useSASATinSLS) "SASAT" else "WalkSAT") + ") has found a satisfying assignment! ***\n")

          if (debug) println("countViolatedNogoods counted from scratch = " + countViolatedNogoodsFromScratchInSLS)

          assert(countViolatedNogoodsFromScratchInSLS == 0)

          //if (runRephasingExclusively)
          // rephaseLock.unlock()

          return countViolatedNogoodsInSLS // formula is satisfiable

        }

        if (c < minViolatedNogoodsInSLS) {

          minViolatedNogoodsInSLS = c

          if (resetSLStoStoredBestState) { // TODO: not useful? Remove?

            println("\nRefreshing bestStateInSLS... ; minViolatedNogoodsInSLS = " + minViolatedNogoodsInSLS)

            var absEli = 1

            while (absEli <= noOfAbsElis) {

              bestStateInSLS.update(absEli, getFromPhasePreviousForAbsElis(absEli))

              absEli += 1

            }

          }

        }

        if (showSLSprogress && noOfInnerSLSTrials % (if (useSASATinSLS) 100 else 10000) == 0) {

          val pStr = "\r@ " + timerToElapsedMs(solverTimer) / 1000 + "sec: " + (if (useSASATinSLS)
            ("Stochastic Local Search (SASAT) thread $" + threadNo + " (#rephs: " + noOfRephasings + "): #viol nogoods = " + c + " @ sasaOuterI: " + sasaOuterI + "/" + sasatOuterMaxInSLS + ", noOfInnerSLSTrials: " + noOfInnerSLSTrials + "/" + maxInnerSLSTrials +
              ", temp = " + round(temperatureInSLS, 3) + ", decayRateTmp = " + round(decayRateForTempInSLS, 12) + ", flip rate: " +
              (flipsInSASAT.toDouble / noOfAbsElis.toDouble / noOfInnerSLSTrials.toDouble) +
              ", sasatRandomWalkProb = " + randomWalkProbInSASAT + ", minViolatedNogoodsInSLS = " + minViolatedNogoodsInSLS)
          else if (walkSATwithTempDecl)
            ("Stochastic Local Search (WalkSAT+temp decline) thread $" + threadNo + " (#reps: " + noOfRephasings + "): #viol nogoods = " + c + " @noOfInnerSLSTrials " + noOfInnerSLSTrials + "/" + maxInnerSLSTrials +
              ", temp = " + round(temperatureInSLS, 3) + ", decayRateTmp = " + round(decayRateForTempInSLS, 12) +
              ", minViolatedNogoodsInSLS = " + minViolatedNogoodsInSLS)
          else
            ("Stochastic Local Search (WalkSAT) thread $" + threadNo + " (#reps: " + noOfRephasings + "): #viol nogoods = " + c +
              " @noOfInnerSLSTrials " + noOfInnerSLSTrials + "/" + maxInnerSLSTrials + ", minViolatedNogoodsInSLS = " + minViolatedNogoodsInSLS)
            )

          printStatusLine(pStr, cutOffAt = 256)

        }

        if (useSASATinSLS || walkSATwithTempDecl) {

          initTempInSLS

          if (temperatureInSLS < minTempInSLS)
            noOfInnerSLSTrials = maxInnerSLSTrials

        }

        if (noOfInnerSLSTrials < maxInnerSLSTrials) {

          if (useSASATinSLS) {

            if (rngLocal.nextFloat() < randomWalkProbInSASAT) { // we perform a random walk or pseudo-WalkSAT step

              val randomNogoodReducible = /*violatedNogoodsInSLS.get(rngLocal.nextInt(violatedNogoodsInSLS.size))*/ violatedNogoodsInSLS.getRandomItem(rngLocal)

              val randomNogoodReducibleSize = getNogoodSizeFromReducible(randomNogoodReducible)

              if (!SASATwithWalkSATsteps) {

                val randomEliInNogood = getEliFromNogoodInReducible(randomNogoodReducible, rngLocal.nextInt(randomNogoodReducibleSize))

                flipInSLS(toAbsEli(randomEliInNogood))

              } else {

                var minViolationsAbsEli = 0

                var minViolations = Int.MaxValue

                var i = 0

                while (i < randomNogoodReducibleSize) {

                  val testAbsEli = toAbsEli(getEliFromNogoodInReducible(randomNogoodReducible, i))

                  val oldCount = countViolatedNogoodsInSLS

                  val testNoViolations = oldCount + flipTentativeInSLS(testAbsEli)

                  if (testNoViolations < minViolations) {

                    minViolations = testNoViolations

                    minViolationsAbsEli = testAbsEli

                  }

                  i += 1

                }

                assert(minViolationsAbsEli != 0)

                flipInSLS(minViolationsAbsEli)

              }

            } else {

              var absEli = 1

              while (absEli <= noOfAbsElis) {

                val increaseNoViolations = flipTentativeInSLS(absEli) // observe that, since we are using nogoods, this is the "opposite" of the increase/decrease δ in
                // W. M. Spears: Simulated Annealing for Hard Satisfiability Problems

                val flipProb = 1d / (1d + Math.exp(increaseNoViolations.toDouble / temperatureInSLS))

                if (rngLocal.nextDouble() < flipProb) {

                  flipsInSASAT += 1

                  flipInSLS(absEli)

                }

                absEli += 1

              }

            }

          } else { // WalkSAT_plus_X ---------

            minimumNoInnerItsBeforeNextRestartCounterInSLS -= 1

            if (minimumNoInnerItsBeforeNextRestartCounterInSLS < 0 /*&& violatedNogoodsInSLS.size > minViolatedNogoodsInSLS * 5*/ ) {

              println("\nResetting SLS...")

              minimumNoInnerItsBeforeNextRestartCounterInSLS = minimumNoInnerItsBeforeNextRestartInSLS

              if (!resetSLStoStoredBestState)
                initializeSLSPhasesRandomly
              else { // TODO: not useful? Remove?

                var absEli = 1

                while (absEli <= noOfAbsElis) {

                  //minViolCache.update(absEli, getFromPhasePreviousForAbsElis(absEli))

                  if (rngLocal.nextFloat() < 0.001f) {

                    if (rngLocal.nextBoolean())
                      updateInPhasePreviousForAbsElis(absEli, 0x00.toByte)
                    else
                      updateInPhasePreviousForAbsElis(absEli, 0x01.toByte)

                  } else
                    updateInPhasePreviousForAbsElis(absEli, bestStateInSLS(absEli))

                  absEli += 1

                }

              }


              initializeViolatedNogoodsInSLS

              initTempInSLS

            }

            @inline def findHighestScoredNogood: NogoodReducible = {

              val randomNogoodReducible = if (useScoresInSLS > 0f && rngLocal.nextFloat() < useScoresInSLS) {

                var shortestViolatedNogoodReducible = violatedNogoodsInSLS.get(0)

                var i = 1

                while (i < violatedNogoodsInSLS.size) {

                  val nogoodScoreX = getNogoodReducibleScore(violatedNogoodsInSLS.get(i), scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods)

                  val nogoodScoreY = getNogoodReducibleScore(shortestViolatedNogoodReducible, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods)

                  if (true) {

                    if (nogoodScoreX < nogoodScoreY)
                      shortestViolatedNogoodReducible = violatedNogoodsInSLS.get(i)

                  }

                  i += 1

                }

                shortestViolatedNogoodReducible

              } else
                violatedNogoodsInSLS.getRandomItem(rngLocal)

              randomNogoodReducible

            }

            @inline def findHighestScoredOrRandomEliInNogood(nogoodReducible: NogoodReducible, sizeOfNogood: Eli) = {

              if (useScoresInSLS > 0f && rngLocal.nextFloat() < useScoresInSLS) {

                var maxScore = Double.MinValue

                var eli: Eli = 0

                var i = 0

                while (i < sizeOfNogood) {

                  val testEli = getEliFromNogoodInReducible(nogoodReducible, i)

                  val testAbsEli = toAbsEli(testEli)

                  if (getAbsEliScore(testAbsEli) > maxScore) {

                    eli = testEli

                    maxScore = getAbsEliScore(testAbsEli)

                  }

                  i += 1

                }

                eli

              } else
                getEliFromNogoodInReducible(nogoodReducible, rngLocal.nextInt(sizeOfNogood))

            }

            if (extraChecks)
              assert(countViolatedNogoodsFromScratchInSLS > 0)

            val pr = walkSATnoise * temperatureInSLS * 10f

            val randomNogoodReducible = findHighestScoredNogood

            val randomNogoodReducibleSize = getNogoodSizeFromReducible(randomNogoodReducible)

            if (useScoresInSLS > 0f)
              bumpNogoodReducibleActivity(randomNogoodReducible) // observe we do this also for clark nogoods here, since purpose here isn't just scoring for learned nogood removal


            if (!semiLocalSearchInSLS && rngLocal.nextFloat() <= pr /*||
              semiLocalSearchInSLS && rngLocal.nextFloat() <= 0.3f*/ ) {

              val randomEliInNogood = findHighestScoredOrRandomEliInNogood(randomNogoodReducible, randomNogoodReducibleSize)

              //if (useScoresInSLS > 0f)
              // bumpUpEVSIDSscoreOfAbsEliMinimally(toAbsEli(randomEliInNogood))

              flipInSLS(toAbsEli(randomEliInNogood))

            } else {

              if (!semiLocalSearchInSLS) {

                var minViolationsAbsEli = 0

                var minViolations = Int.MaxValue

                var i = 0

                while (i < randomNogoodReducibleSize) {

                  val testAbsEli = toAbsEli(getEliFromNogoodInReducible(randomNogoodReducible, i))

                  val testNoViolations = flipTentativeInSLS(testAbsEli)

                  if (testNoViolations < minViolations) {

                    if (true) {

                      minViolations = testNoViolations

                      minViolationsAbsEli = testAbsEli

                    }

                  }

                  i += 1

                }

                //assert(minViolationsAbsEli != 0)

                if (minViolationsAbsEli != 0)
                  flipInSLS(minViolationsAbsEli)

              } else { // Experimental (allows for taking into account previously violated nogoods and also
                // to test flipping literals from multiple violated nogoods):

                val violatedNogoods: RandomLongSet = violatedNogoodsInSLS

                if (allViolatedNogoodsSoFarInSLS.size > 100) {

                  while (allViolatedNogoodsSoFarInSLS.size > 10) {

                    allViolatedNogoodsSoFarInSLS.removeAt(rngLocal.nextInt(allViolatedNogoodsSoFarInSLS.size))

                  }

                }

                var k = 0

                while (k < violatedNogoods.size) {

                  allViolatedNogoodsSoFarInSLS.add(violatedNogoods.get(k))

                  k += 1

                }

                if (rngLocal.nextFloat() <= 0.2f) {

                  if (allViolatedNogoodsSoFarInSLS.size == 0 || rngLocal.nextFloat() <= 0.2f) {

                    flipInSLS(rngLocal.nextInt(noOfAbsElis) + 1)

                    /*   val randomEliInNogood = findHighestScoredOrRandomEliInNogood(randomNogoodReducible, randomNogoodReducibleSize)

                       flipInSLS(toAbsEli(randomEliInNogood))
   */
                  } else {

                    val randomNogoodReducible: NogoodReducible = allViolatedNogoodsSoFarInSLS.
                      getRandomItem(rngLocal)

                    val randomNogoodReducibleSize = getNogoodSizeFromReducible(randomNogoodReducible)

                    //val randomEliInNogood: Eli = toAbsEli(getEliFromNogoodInReducible(randomNogoodReducible, rngLocal.nextInt(randomNogoodReducibleSize)))

                    val randomEliInNogood = findHighestScoredOrRandomEliInNogood(randomNogoodReducible, randomNogoodReducibleSize)

                    flipInSLS(toAbsEli(randomEliInNogood))

                  }

                } else if (violatedNogoods.size > 0) {

                  var minViolations = violatedNogoodsInSLS.size * 2 // Int.MaxValue

                  var minViolationsTestAbsElis = mutable.HashSet[Eli]()

                  @inline def noOfConfigsToTest: Int = violatedNogoodsInSLS.size.min(minViolations) * 3

                  var ci = 0

                  while (ci < noOfConfigsToTest) {

                    val testAbsElis = mutable.HashSet[Eli]()

                    var i = 0

                    while (testAbsElis.size <= 3 && i < 5000 && violatedNogoodsInSLS.size > 0) {

                      val testAbsEli = {

                        val randomNogoodReducible: NogoodReducible = violatedNogoods /*allViolatedNogoodsSoFarInSLS*/ .getRandomItem(rngLocal)

                        val randomNogoodReducibleSize = getNogoodSizeFromReducible(randomNogoodReducible)

                        toAbsEli(getEliFromNogoodInReducible(randomNogoodReducible, rngLocal.nextInt(randomNogoodReducibleSize)))

                      }

                      val doTest = testAbsElis.add(testAbsEli)

                      if (doTest)
                        flipInSLS(testAbsEli)

                      i += 1

                    }

                    if (violatedNogoods.size < minViolations) {

                      minViolations = violatedNogoods.size

                      minViolationsTestAbsElis = testAbsElis

                    }

                    testAbsElis.foreach(flipInSLS(_))

                    ci += 1

                  }

                  if (!minViolationsTestAbsElis.isEmpty)
                    minViolationsTestAbsElis.foreach(flipInSLS(_))

                }

              }

            }

          }

          noOfInnerSLSTrials += 1

        }

        //println ("noOfInnerSLSTrials = " + noOfInnerSLSTrials)

      }

      sasaOuterI += 1

    } while (sasaOuterI < sasatOuterMaxInSLS /*&& useSASATinSLS */ && !stopSolverThreads)

    if (copySLSPhasesToBestPhasesInSLS) {

      sharedAmongSingleSolverThreads.refreshedBestPhasesGlobal += 1

      val newBestPhases = new ByteArrayUnsafeS(noOfAbsElis + 1, initialValue = 0x00.toByte)

      var absEli = 1

      /*bestPhasesForAbsElis.synchronized*/
      {

        while (absEli <= noOfAbsElis) {

          newBestPhases.update(absEli, if (isAbsEliSetAsPosInSLS(absEli)) 0x01.toByte else 0x00.toByte)

          absEli += 1

        }

      }

      bestPhasesQueue.synchronized {
        bestPhasesQueue.enqueueFinite(newBestPhases, maxSize = 1) // keeping >1 "best" states doesn't seem to improve things, but more tests required
      }

    }

    countViolatedNogoodsInSLS // either max trials exceeded or UNSAT

  }

}
