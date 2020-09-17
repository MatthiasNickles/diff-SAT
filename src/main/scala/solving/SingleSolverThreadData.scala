/**
  * delSAT
  *
  * Copyright (c) 2018-2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package solving

import java.lang.management.ManagementFactory
import java.util.Map

import input.UNSAFEhelper.{UNSAFE, addAllocOffHeapMemToGarbage, allocateOffHeapMem, approxSizeOfCurrentFreeUnsafeMemory, freeOffHeapMem}
import input.UNSAFEhelper
import input.delSAT._

import it.unimi.dsi.fastutil.ints._
import it.unimi.dsi.fastutil.longs.{Long2IntOpenHashMap, Long2IntRBTreeMap, LongArrayList}
import it.unimi.dsi.fastutil.objects.{ObjectArrayList, ObjectBidirectionalIterator}

import sharedDefs._
import utils._
import utils.Various._

import scala.collection.mutable.ArrayBuffer
import scala.collection.{Seq, mutable}

/** Data structures and associated methods used in the inner (i.e. SAT solving) loop of a single solver thread.
  *
  * @todo further refactoring
  * @param prep
  * @param singleSolverConf
  * @param tempFacts
  * @param maxCompetingSolverThreads
  * @param sharedAmongSingleSolverThreads
  */
class SingleSolverThreadData(prep: Preparation, singleSolverConf: SolverThreadSpecificSettings,
                             tempFacts: List[Eli],
                             maxCompetingSolverThreads: Int,
                             sharedAmongSingleSolverThreads: SharedAmongSingleSolverThreads) { // ´´´´´´´´´´´´´´´´´´´´´´´´´´´´

  import prep._
  import singleSolverConf._

    if(debug)
      println("\nConstructing SingleSolverThreadData instance...")

    var workingReducibleSizeInConflictAnalysisAutoValueInNoOfInts = initialNewNogoodReducibleSlotSize // initial expected number of Ints per memory slot for learned nogood reducibles

    var minUnassignedThisThread = noOfAllElis

    val solverTimer: Long = System.nanoTime()

    if(debug) println("rngLocal seed thread $" + threadNo + " = " + seed + "\n")

    val rngLocal: RandomGenSuperclass = if (altRandomNumGen)
      new XoRoRNGd(seed)
    else
      new XORShift32(java.util.Optional.of(seed)) // faster but less random.

    var rndmBranchProb = if (rndmBranchProbR < 0) 0.01f/*TODO*/ else rndmBranchProbR

    if(autoGenerateCostLinesForHypotheses && !ensureParamAtomsAreMeasured)
      stomp(-5006, "Invalid setting: autoGenerateCostLinesForHypotheses && !ensureParamAtomsAreMeasured")

    val sccCache = mutable.HashMap[mutable.Seq[Eli], ArrayBuffer[ArrayBuffer[Eli]]]()

    /*

    There are three ways nondeterministic branching is influenced (besides randomization and noise, e.g., noisePhaseMemo):
      1) partial derivatives obtained from cost functions (for parameter elis)
      2) for non-parameter literals: the eli order in elisArranged
      3) for non-parameter literals: absEliScores
    Which of 2) and/or 3) is used, depends on freeEliSearchApproach
    Also, 3) might influence how nogoods are ignored and/or removed.

    */

    val restartTriggerConf = restartTriggerConfR

    val restartsFactModifier: Float = restartFrequencyModifierFactorR

    val useSLSinPhaseMemoRephasing = useSLSinPhaseMemoRephasingR &&
      noOfAbsElis >= boundsOnNoOfAbsElisForSLSinrephasing._1 && noOfAbsElis <= boundsOnNoOfAbsElisForSLSinrephasing._2

    val glucoseRestarts: Boolean = restartsFactModifier < 0f

    val freeEliSearchApproach11or14or15 = freeEliSearchApproach == 15 || freeEliSearchApproach == 11 || freeEliSearchApproach == 14

    val reusedTrailRestarts = reusedTrailRestartsR && freeEliSearchApproach11or14or15

    var forceRestart = false

    var enforceLBDemaComputation = (rndmBranchProbR < 0 || absEliScoringApproach == 0 && !evsids || glucoseRestarts) // also see setThreadParams!

    val scoringForRemovalOfLearnedNogoods: Eli = scoringForRemovalOfLearnedNogoodsR

    var useLBD /*LBD = "glue degree" of nogoods or clauses*/ : Boolean =
      enforceLBDemaComputation ||
        scoringForRemovalOfLearnedNogoods == 0 || scoringForRemovalOfLearnedNogoods == 8 || scoringForRemovalOfLearnedNogoods == 11

    val allowSwitchFreeEliSearchApproach = abandonOrSwitchSlowThreads != 0d && slowThreadAction == 3

    var playStackStartOrderNumber = -1 // for absEliScoringApproach == 1

    val absEliClusteredLocal = if (absEliClustered != null)
      absEliClustered.clone()
    else
      null.asInstanceOf[Array[Array[Eli]]]

    val bestPhasesQueue: FiniteQueue[ByteArrayUnsafeS] = if (globalBestPhaseMemo) sharedAmongSingleSolverThreads.bestPhasesQueueGlobal else if (weakRephasingAtRestartEvery > 0 || rephasePhaseMemo)
      new FiniteQueue[ByteArrayUnsafeS](scala.collection.mutable.Queue[ByteArrayUnsafeS]()) //new ByteArrayUnsafeS(noOfAbsElis + 1, initValue = if (rngLocal.nextBoolean()) 0x01.toByte else 0x00.toByte)
    else
      null.asInstanceOf[FiniteQueue[ByteArrayUnsafeS]]

    assert(globalBestPhaseMemo) // false not tested well enough (and probably no advantage over global queue)

    val violatedNogoodsInSLS: RandomLongSet = if (rephasePhaseMemo && useSLSinPhaseMemoRephasing)
      new RandomLongSet(clarkNogoodsFinal.length)
    else
      null.asInstanceOf[RandomLongSet]

    val nogiClarkToNogoodReducible = new LongArrayUnsafeS(clarkNogoodsFinal.length)
    // NB(1): nogis (nogood indices) are only defined
    // for the original nogoods ("Clark nogoods"), not for any learned or loop nogoods!
    // NB(2): we cannot make this global for all solver threads, as each competing thread might (depending on BCP method)
    // modify the contained reducibles.
    // NB(3): nogiClarkToNogoodReducible is initially filled with rubbish, use only after initialization of for each nogi

    val usedUpInLevel = if (!(freeEliSearchApproach == 12 || freeEliSearchApproach == 13) && !allowSwitchFreeEliSearchApproach)
      null.asInstanceOf[IntArrayUnsafeS]
    else
      new IntArrayUnsafeS(2000000) // TODO: find a reasonable value here without the need to enhance array

    val deficitOrderedUncertainLiteralsHalf: Eli = deficitOrderedUncertainLiteralsForJava.size / 2 // each variable appears twice (pos and neg polarity), we only need their lowest ranked literals

    val ignoreParamVariables: Boolean = ignoreParamVariablesR || deficitOrderedUncertainLiteralsHalf == 0

    var maxBCPPush: Eli = maxBCPPushInit + parameterLiteralElisArray.length

    var rmiStoreG: IntArrayUnsafeS = // NB: size limits amount of literals which can be assigned in one setEliWithNogoodUpdatesNoHeap BCP call:
      new IntArrayUnsafeS(maxBCPPush)
    // TODO: rename

    var rmiStorePos: Eli = 0

    var rmiStorePosOld: Eli = 0

    var ri = -1

    @deprecated val reasonsForRmiStoreForNoHeap: LongArrayUnsafeS = if (extReducibles == 1 || extReducibles == 5)
      new LongArrayUnsafeS(maxBCPPush) else null.asInstanceOf[LongArrayUnsafeS]

    val eliWatchedToReducibles: Array[NogoodReduciblesSequenceUnsafe] = new Array[NogoodReduciblesSequenceUnsafe](noOfAllElis + 1)
    // ^ the watched eli lists

    val eliToReduciblesClark: Array[NogoodReduciblesSequenceUnsafe] = if (allowEliToClarkReduciblesLookup)
      new Array[NogoodReduciblesSequenceUnsafe](noOfAllElis + 1)
    else
      null.asInstanceOf[Array[NogoodReduciblesSequenceUnsafe]]

    val eliToReduciblesDeficitResto: Array[NogoodReduciblesSequenceUnsafe] = if (extReducibles == 1) new Array[NogoodReduciblesSequenceUnsafe](noOfAllElis + 1) else null.asInstanceOf[Array[NogoodReduciblesSequenceUnsafe]]

    @inline def getEstimatedNoOfNogoodsPerAbsEli(absEli: Eli, forFull: Boolean = false): Eli = {

      defaultEliToReducibleListCapacity

    }

    var absEli = 1

    while (absEli <= noOfAbsElis) {

      eliWatchedToReducibles(eliToJavaArrayIndex(absEli)) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli))

      if (allowEliToClarkReduciblesLookup)
        eliToReduciblesClark(eliToJavaArrayIndex(absEli)) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli, forFull = true))

      if (extReducibles == 1)
        eliToReduciblesDeficitResto(eliToJavaArrayIndex(absEli)) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli))

      eliWatchedToReducibles(eliToJavaArrayIndex(negateEli(absEli))) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli))

      if (allowEliToClarkReduciblesLookup)
        eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli))) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli, forFull = true))

      if (extReducibles == 1)
        eliToReduciblesDeficitResto(eliToJavaArrayIndex(negateEli(absEli))) = new NogoodReduciblesSequenceUnsafe(initialCapacity = getEstimatedNoOfNogoodsPerAbsEli(absEli))

      absEli += 1

    }

    val lPass = new ByteArrayUnsafeS/*IntArrayUnsafeS*/(noOfAllElis + 2, initialValue = 0)  // Initialization with 0 is required. Observe that
    // in particular, we must get 0 for pseudo-eli 0 because 0 is used as end-marker "eli" with some BCP methods and
    // they iterate until isNotSetInPass.
    // Remark: instead of lPass, formerly an Int array of size noOfAbsElis within varsSpace was used (i.e., where
    // both pos/neg literal phases are encoded in the variable position, similar to MiniSat). However, given growing
    // cache sizes and more isSetInPass than setInPass calls appear to make an array of size noOfAllElis more sensible.
    // In practice (preliminary tests) however, the performance difference seems to be negligible anyway.

    val lPassBoundary = noOfAllElis + 1

    @inline def getFromlPass(eli: Eli): Int = {

      if(eli >= 0)
        lPass.get(eli)
      else
        lPass.get(lPassBoundary + eli)

    }

    @inline def updateInlPass(eli: Eli, value: Byte): Unit = {

      if(eli >= 0)
        lPass.update(eli, value)
      else
        lPass.update(lPassBoundary + eli, value)

    }

    // ***** The following allocates a single space for various absEli->x and decision level->x mappings (observe
    // that the maximum number of decisions corresponds to the maximum number of variables)

    val powerOf2ForNoOfBytesPerVarSpace = 6 // specifies size of slot. 6 = 64 bytes (bytes 0-63) // 2^x bytes per each variable (absEli) slot in off-heap memory

    val noOfBytesVarSpace = 1 << powerOf2ForNoOfBytesPerVarSpace // must be a power of 2

    // TODO?: ?Can we identify any sequences here where decoupling them from the others in the cacheline is useful, and put them into their own independent arrays?

    // NB: not all of the slots below are updated in all configurations!

    val offsetInBytesForReasonedAbsEli = 0 // Int (bytes 0-3)

    val offsetInBytesForReasonInVarSpace = 4 // Long (bytes 4-11)

    val offsetInBytesForAbsEliScoreInVarSpace = 12 // Float (bytes 12-15)

    val offsetInBytesForAbsEliScoreUpdatesInVarSpace = 16 // Int (bytes 16-19)

    val offsetInBytesForLastConflictOfAbsEliInVarSpace = 20 // Int (bytes 20-23)

    val offsetInBytesForParticipatedAbsEliInVarSpace = 24 // Int (bytes 24-27)

    val offsetInBytesForDecisionLevelInVarSpace = 28 // Int (bytes 28-31)

    val offsetInBytesForPhasePreviousForAbsElisInVarSpace = 32 // Byte (byte 32)

    val offsetInBytesForSeenInVarSpace = 33 // Byte (byte 33)

    val offsetInBytesForDecisionAbsEliSeqForRTR = 34 // Int (bytes 34-37)

    val offsetInBytesForConflictsAtDecisionLevel = 38 // Int (bytes 38-41)

    val alignmentVarsSpace = noOfBytesVarSpace //8  observe that unsafe's allocateMemory does some alignment (to value size) by itself

    val sizeVarsSpace_ = (noOfAbsElis + 2) * noOfBytesVarSpace + alignmentVarsSpace

    var varsSpace_ = allocateOffHeapMem(sizeVarsSpace_)

    val varsSpace = if (alignmentVarsSpace > 0l && (varsSpace_ & (alignmentVarsSpace - 1l)) != 0)
      varsSpace_ + (alignmentVarsSpace - (varsSpace_ & (alignmentVarsSpace - 1)))
    else
      varsSpace_

    UNSAFE.setMemory(varsSpace, (noOfAbsElis + 1) * noOfBytesVarSpace, 0x00.toByte)

    @inline def updateInSeen(absEli: Eli, newValue: Byte): Unit =
      UNSAFE.putByte(varsSpace + offsetInBytesForSeenInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), newValue)

    @inline def getFromSeen(absEli: Eli): Byte =
      UNSAFE.getByte(varsSpace + offsetInBytesForSeenInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    @inline def updateInPhasePreviousForAbsElis(absEli: Eli, newValue: Byte): Unit =
      UNSAFE.putByte(varsSpace + offsetInBytesForPhasePreviousForAbsElisInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), newValue)

    @inline def getFromPhasePreviousForAbsElis(absEli: Eli): Byte =
      UNSAFE.getByte(varsSpace + offsetInBytesForPhasePreviousForAbsElisInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    @inline def updateReasonOfEli(eli: Eli, reason: NogoodReducible): Unit =
      UNSAFE.putLong(varsSpace + offsetInBytesForReasonInVarSpace + (toAbsEli(eli) << powerOf2ForNoOfBytesPerVarSpace), reason)

    @inline def getReasonOfEli(eli: Eli): NogoodReducible =
      UNSAFE.getLong(varsSpace + offsetInBytesForReasonInVarSpace + (toAbsEli(eli) << powerOf2ForNoOfBytesPerVarSpace))

    @inline def decisionLevelOfEli(eli: Eli): Eli =  // NB: in the way conflict analysis is implemented this value might also be requested for unassigned elis
      UNSAFE.getInt(varsSpace + offsetInBytesForDecisionLevelInVarSpace + (toAbsEli(eli) << powerOf2ForNoOfBytesPerVarSpace))

    @inline def updateAbsEliToDl(eli: Eli, dl: Eli): Unit =
      UNSAFE.putInt(varsSpace + offsetInBytesForDecisionLevelInVarSpace + (toAbsEli(eli) << powerOf2ForNoOfBytesPerVarSpace), dl)

    @inline def getAbsEliScore(absEli: Eli): Float =
      UNSAFE.getFloat(varsSpace + offsetInBytesForAbsEliScoreInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    @inline def updateAbsEliScore(absEli: Eli, newScore: Double): Unit = {

      UNSAFE.putFloat(varsSpace + offsetInBytesForAbsEliScoreInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), newScore.toFloat)

      // Remark: in many other code locations, absEli scores are still represented as Double values - doesn't really matter, we
      // use Float only to squeeze more absEli metadata into a 32 byte slot, not because of performance.

      // Remark: the actual range of these scores depends mainly from absEliScoringApproach. E.g.,
      // with approach 2, the scores are Q-values.

    }

    @inline def updateLastConflictOfAbsEli(absEli: Eli, newValue: Eli): Unit = {

      UNSAFE.putInt(varsSpace + offsetInBytesForLastConflictOfAbsEliInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), newValue)

    }

    @inline def getLastConflictOfAbsEli(absEli: Eli): Eli = {

      UNSAFE.getInt(varsSpace + offsetInBytesForLastConflictOfAbsEliInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    }

    @inline def updateParticipatedAbsEli(absEli: Eli, newValue: Eli): Unit = {

      UNSAFE.putInt(varsSpace + offsetInBytesForParticipatedAbsEliInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), newValue)


    }

    @inline def incParticipatedAbsEli(absEli: Eli): Eli = {

      UNSAFE.getAndAddInt(null, varsSpace + offsetInBytesForParticipatedAbsEliInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), 1)

    }

    @inline def getParticipatedAbsEli(absEli: Eli): Eli = {

      UNSAFE.getInt(varsSpace + offsetInBytesForParticipatedAbsEliInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    }

    @inline def incAbsEliScoreUpdates(absEli: Eli): Eli = {

      UNSAFE.getAndAddInt(null, varsSpace + offsetInBytesForAbsEliScoreUpdatesInVarSpace + (absEli << powerOf2ForNoOfBytesPerVarSpace), 1)

    }


    @inline def updateDecisionAbsEliSeqForRTR(decLevel: Int, newValue: Eli): Unit = {

      UNSAFE.putInt(varsSpace + offsetInBytesForDecisionAbsEliSeqForRTR + (decLevel << powerOf2ForNoOfBytesPerVarSpace), newValue)

    }

    @inline def getDecisionAbsEliSeqForRTR(decLevel: Int): Eli = {

      UNSAFE.getInt(varsSpace + offsetInBytesForDecisionAbsEliSeqForRTR + (decLevel << powerOf2ForNoOfBytesPerVarSpace))

    }

    @inline def updateConflictsAtDecisionLevel(decLevel: Int, newValue: Int): Unit = {

      UNSAFE.putInt(varsSpace + offsetInBytesForConflictsAtDecisionLevel + (decLevel << powerOf2ForNoOfBytesPerVarSpace), newValue)

    }

    @inline def getConflictsAtDecisionLevel(decLevel: Int): Eli = {

      UNSAFE.getInt(varsSpace + offsetInBytesForConflictsAtDecisionLevel + (decLevel << powerOf2ForNoOfBytesPerVarSpace))

    }

    @inline def updateReasonedAbsEli(absEli: Eli, newValue: Int): Unit = {

      UNSAFE.putInt(varsSpace + offsetInBytesForReasonedAbsEli + (absEli << powerOf2ForNoOfBytesPerVarSpace), newValue)

    }

    @inline def incReasonedAbsEli(absEli: Eli): Eli = {

      UNSAFE.getAndAddInt(null, varsSpace + offsetInBytesForReasonedAbsEli + (absEli << powerOf2ForNoOfBytesPerVarSpace), 1)

    }

    @inline def getReasonedAbsEli(absEli: Eli): Eli = {

      UNSAFE.getInt(varsSpace + offsetInBytesForReasonedAbsEli + (absEli << powerOf2ForNoOfBytesPerVarSpace))

    }


    val absEliComparator = new IntComparator {

      @inline override def compare(o1: Eli, o2: Eli) = {

        if (getAbsEliScore(o1) == getAbsEliScore(o2))
          0
        else if (getAbsEliScore(o1) > getAbsEliScore(o2))
          -1
        else
          1

      }

    }

    class AbsElisPriorityQueue(/*array: Array[Int]*/) extends IntHeapIndirectPriorityQueue(
      (0 /*<-- sic!*/ to noOfAbsElis).toArray, noOfAbsElis + 1, absEliComparator) {

      @inline def downHeap(elem: Eli) = {

        IntIndirectHeaps.downHeap(refArray, heap, inv, size, inv(elem), c)

      }

      @inline def upHeap(elem: Eli) = {

        IntIndirectHeaps.upHeap(refArray, heap, inv, size, inv(elem), c)

      }

      @inline override def changed(elem: Eli) = {

        super.changed(elem)


      }

      @inline def containsElem(elem: Eli): Boolean = {

        this.contains(elem)

      }

      @inline def getHeap: Array[Eli] = this.heap


      @inline def removeLazy(index: Eli): Boolean = {

        val result = inv(index)

        if (result < 0) return false

        inv(index) = -1

        if (result < {
          size -= 1;
          size
        }) {

          heap(result) = heap(size)

          inv(heap(size)) = result

        }

        true

      }

    }


    val unassignedScoredAbsEliTreeSet = if (freeEliSearchApproach == 9 || allowSwitchFreeEliSearchApproach) {

      new IntRBTreeSet /*IntAVLTreeSet*/ (absEliComparator) // TODO: add all absEliSeqArranged elis (like with unassignedScoredAbsElisPriorityQueue)

    } else null.asInstanceOf[IntRBTreeSet /*IntAVLTreeSet*/ ]

    val unassignedScoredAbsElisPriorityQueue: AbsElisPriorityQueue = if ((freeEliSearchApproach == 11) || allowSwitchFreeEliSearchApproach)
      new AbsElisPriorityQueue()
    else null.asInstanceOf[AbsElisPriorityQueue]

    var unassignedAbsEliSet: DualIndexedIntSet = if (freeEliSearchApproach == 14 || allowSwitchFreeEliSearchApproach)
      new DualIndexedIntSet(noOfAbsElis + 1, rngLocal,
        sortedMode = true, getAbsEliScore = getAbsEliScore, updateAbsEliScore_ = updateAbsEliScore)
    else
      null.asInstanceOf[DualIndexedIntSet]

    val unassignedAbsEliBinSet = if (freeEliSearchApproach == 15 || allowSwitchFreeEliSearchApproach) {

      // Instead of maintaining a single queue ordered by absEli scores, we keep a number of unordered "bins". Each (unassigned) eli
      // is placed in one of these bins, the bin determined by a rounded absEli score. Essentially a form of radix sort.

      val noOfBins = 25 // should be between (about) 25 and 100. See getBinFromScoreForFreeEliSearchApproach15() for
      // the mapping from absEli scores to bin indices.

      val r = Array.ofDim[DualIndexedIntSet](noOfBins)

      var i = 0

      while (i < noOfBins) {

        r.update(i, new DualIndexedIntSet(noOfAbsElis + 1, rngLocal, sortedMode = false))

        i += 1

      }

      r

    } else null.asInstanceOf[Array[DualIndexedIntSet]]

    val absElisSeqArranged: IntArrayUnsafeS = new IntArrayUnsafeS({

      val absEliSeq: Seq[Eli] = 1 to noOfAbsElis

      (if (initAbsElisArrangement == 7 || initAbsElisArrangement == 8) {

        /*phasePreviousForAbsElis.synchronized*/
        { // TODO: bug (occassional sort contract violations) with globalPhaseMemo=true
          absEliSeq.sortWith((absEli1: Eli, absEli2: Eli) => {

            val v1 = getFromPhasePreviousForAbsElis(absEli1)

            val v2 = getFromPhasePreviousForAbsElis(absEli2)

            if (initAbsElisArrangement == 7)
              v1 > v2
            else
              v1 < v2

          }).toArray

        }

      }
      else if (initAbsElisArrangement == 1)
        absEliSeq.reverse.toArray
      else if (initAbsElisArrangement == 2) {

        val absEliSeqArray = absEliSeq.toArray

        shuffleArray(absEliSeqArray, rngLocal)

        absEliSeqArray

      } else if (initAbsElisArrangement == 0)
        absEliSeq.toArray
      else if (initAbsElisArrangement == 9 || initAbsElisArrangement == 10) { // requires eliToNogisClark in Preparation.scala

        absEliSeq.sortBy(absEli => {

          val l = eliToNogisClark(eliToJavaArrayIndex(absEli)).length + eliToNogisClark(eliToJavaArrayIndex(negatePosEli(absEli))).length

          // println("absEli: " + absEli + ", l = " + l)

          if (initAbsElisArrangement == 9) l else -l

        }).toArray

      } else if (allowEliToClarkReduciblesLookup && (initAbsElisArrangement == 5 || initAbsElisArrangement == 6)) {

        absEliSeq.sortWith((absEli1: Eli, absEli2: Eli) => {

          val v1 = eliToReduciblesClark(eliToJavaArrayIndex(absEli1)).size.toFloat /
            eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli1))).size.toFloat

          val v2 = eliToReduciblesClark(eliToJavaArrayIndex(absEli2)).size.toFloat /
            eliToReduciblesClark(eliToJavaArrayIndex(negateEli(absEli2))).size.toFloat

          if (initAbsElisArrangement == 5)
            v1 < v2
          else
            v1 > v2

        }).toArray

      } else {

        val absEliSet = new utils.DualIndexedIntSet(noOfAbsElis + 1 /*sic! because the underlying array is indexed by absElis*/ ,
          rngLocal)

        clarkNogoodsFinal.foreach(nogood => {

          var i = 0

          while (i < nogood.sizev) {

            val absEli = toAbsEli(nogood.get(i))

            absEliSet.add(absEli)

            i += 1

          }

        })

        absEliSeq.foreach(absEli => {

          absEliSet.add(absEli) // fill up with any remaining variables

        })

        val o = absEliSet.dta.toArray(0, absEliSet.size)

        absEliSet.free()

        if (initAbsElisArrangement == 3)
          o
        else
          o.reverse

      })

    })

    val targetArrayUnsafeForNogoodInConfA = if (conflictNogoodSelfSubsumption) new IntArrayUnsafeS(24 * 1024) else null.asInstanceOf[IntArrayUnsafeS]

    var dtaIndexOfMaxScoredInUnassignedAbsEliSet: Eli = -1

    var orderNumber: Eli = 1 // sequence number of next eli assignment (not necessarily consecutive). Cannot be zero.

    var dl: Eli = 0 // decision level (increased at each nondeterministic branching literal decision)

    var violatedNogoodReducible: NogoodReducible = 0l // (not to be confused with the conflict nogood which is the learned nogood after a conflict)

    var timeAtLastProgressPrintedNs: NogoodReducible = -1l

    var noOfPropagationsSinceLastProgressPrinted: Eli = 0

    var avgNoPropagationsPerSecond: NogoodReducible = 0l

    var noOfProgressUpdatesPrinted: Eli = 0

    var totalNoElisInLearnedNogoods: Eli = 0

    var noOfConflictsTotal: Eli = 0

    var noOfConflictsAfterRestart: Eli = 0

    var reducibleSlotSizeEnlargementsEMA: Float = 0f // exponential moving average (alpha 1/500) over (important) events
    // that the initial slot size for a new learned nogood reducible turned out to be too small

    @inline def getNoOfConflictsForERWA: Eli = noOfConflictsTotal

    var noOfConflictsAfterLastRephasing: Eli = 0

    var lbdEmaSlow: Double = 0d

    var lbdEmaFast: Double = 0d

    var noOfProgressChecks = 0

    var noOfRephasings: Eli = 0

    var noOfRephasingsUsingSLS: Eli = 0

    var noOfWeakRephasings = 0

    var timeOfLastRestartNs: NogoodReducible = 0l

    var noOfRestarts: Eli = 0

    var scheduleRescaleAbsElis = false

    var rescalingsAbsEliScores = 0

    var totalAbsEliScoreForDebugging: Double = 0d

    var omittedByPreFilterForNogoods: Eli = 0

    var keptByPreFilterForNogoods: Eli = 0

    var nogoodRemovalThreshAdapted: Double = if (nogoodRemovalThreshInit < 0)
      clarkNogoodsFinal.length / (noOfAbsElis/*can be zero*/ + 1) * -nogoodRemovalThreshInit
    else
      nogoodRemovalThreshInit

    @deprecated val freeNogoodReducibleMemoryMap = // For some approaches to free the memory of learned nogoods only. Maps memory slot size to list of unoccupied memory addresses
      if (freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach == 0)
        new Int2ObjectRBTreeMap[LongArrayList](new IntComparator {
          // Moving this to a thread-global position (and adding synchronization) seems to be slowing down things (but more tests required)

          // Observe that this tree typically has only a small number of nodes, as all addresses
          // for reducibles with nogood size up to minNogoodAllocation go into the same node (list)!
          @inline override def compare(k1: Eli, k2: Eli): Eli = if (k1 == k2) 0 else if (k1 < k2) -1 else 1

        }) else null

    @deprecated val occupiedNogoodReducibleMemoryMap = if (freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach == 0)
      new Long2IntRBTreeMap() // For learned nogoods only. Maps occupied memory slot address (of reducible) to its size
    else
      null

    val fmStackThreadLocalInitialCapacity = 50000

    val fmStackThreadLocal = if (freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach == 2)
      new ArrayValExtensibleLongUnsafe(buffer = new LongArrayUnsafeS(fmStackThreadLocalInitialCapacity),
        initiallyOccupiedInBuffer = 0) /*LongArrayList(fmStackThreadLocalInitialCapacity)*/
    else
      null

  def queueOffHeapGarbageInSingleSolver: Unit = UNSAFEhelper.garbage.synchronized/*as off-heap garbage tracking isn't thread-safe*/ {

    /*if (collectOffHeapGarbage)*/ { // TODO: this works fully only with freeDeletedNogoodMemoryApproach=2 (which is the default anyway), otherwise it's leaky

      if(freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach != 2)
        stomp(-5017, "With freeDeletedNogoodMemoryApproach != 2 no complete off-heap garbage collection is possible")

      if (UNSAFEhelper.debugMode)
        println("Available off-heap memory before possible garbage collection:  " + approxSizeOfCurrentFreeUnsafeMemory() + " (" + approxSizeOfCurrentFreeUnsafeMemory().toDouble / 1073741824d + " GB)")
      // (if you get a negative value here ^, approxSizeOfCurrentFreeUnsafeMemory underestimated the original amount of native memory available for the JVM, which can easily happen)

      // NB: we manually list the items to be freed here, since automatic keeping of a reference list (e.g., alloc with UNSAFE.helper.debugMode)
      // would be too costly.

      if (nogiClarkToNogoodReducible != null) {

        var nogi = 0

        while (nogi < nogiClarkToNogoodReducible.size) {

          val nogoodReducible = nogiClarkToNogoodReducible.get(nogi)

          if(nogoodReducible != null.asInstanceOf[NogoodReducible])  // null occurs if triviallyUNSAT
          addAllocOffHeapMemToGarbage(nogoodReducible, getTotalSizeOfReducibleInBytes(nogoodReducible))

          nogi += 1

        }

      }

      // Firstly we delete the space occupied by any remaining learned nogoods:

      var i = 0

      while (i < learnedNogoodReduciblesListCurrent.size) {

        val learnedNogoodReducible = learnedNogoodReduciblesListCurrent.get(i)

        addAllocOffHeapMemToGarbage(learnedNogoodReducible, getTotalSizeOfReducibleInBytes(learnedNogoodReducible))

        i += 1

      }

      learnedNogoodReduciblesListCurrent.freeBuffer()

      if(false && learnedNogoodReduciblesListTotal != null) {  // nope

        if(!freeOrReassignDeletedNogoodMemory) {  // TODO: can't do that, since even with !freeOrReassignDeletedNogoodMemory
          // with nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0 we might have duplicate memory addresses across learnedNogoodReduciblesListTotal and learnedNogoodReduciblesListCurrent

          assert(false)

          var i = 0

          while (i < learnedNogoodReduciblesListTotal.size) {

            val learnedNogoodReducible = learnedNogoodReduciblesListTotal.get(i)

            addAllocOffHeapMemToGarbage(learnedNogoodReducible, getTotalSizeOfReducibleInBytes(learnedNogoodReducible))

            i += 1

          }

          learnedNogoodReduciblesListTotal.freeBuffer()

        }

      }

      // Next, we free the space released from deleted older learned nogoods:

      if (fmStackThreadLocal != null) {

        while (!fmStackThreadLocal.isEmpty) {

          val a = fmStackThreadLocal.popLast

          addAllocOffHeapMemToGarbage(a, getTotalSizeOfReducibleInBytes(a))

        }

        fmStackThreadLocal.addToGarbageBuffer()

      }

      addAllocOffHeapMemToGarbage(varsSpace_, sizeVarsSpace_)

      rmiStoreG.addToGarbage()

      if (usedUpInLevel != null)
        usedUpInLevel.addToGarbage()

      absElisSeqArranged.addToGarbage()

      if (reasonsForRmiStoreForNoHeap != null)
        reasonsForRmiStoreForNoHeap.addToGarbage()

      if (unassignedAbsEliSet != null)
        unassignedAbsEliSet.addToGarbage()

      if (unassignedAbsEliBinSet != null)
        unassignedAbsEliBinSet.foreach(_.addToGarbage())

      if (targetArrayUnsafeForNogoodInConfA != null)
        targetArrayUnsafeForNogoodInConfA.addToGarbage()

      eliWatchedToReducibles.foreach(rl => if (rl != null) rl.addToGarbage())

      if (eliToReduciblesClark != null)
        eliToReduciblesClark.foreach(rl => if (rl != null) rl.addToGarbage())

      if (eliToReduciblesDeficitResto != null)
        eliToReduciblesDeficitResto.foreach(rl => if (rl != null) rl.addToGarbage())

      nogiClarkToNogoodReducible.free()

      if (loopNogoodsForEmitClauses != null)
        loopNogoodsForEmitClauses.forEach(_.addToGarbage())

      lPass.addToGarbage()

      if (!globalBestPhaseMemo) {

        if (bestPhasesQueue != null)
          while (!bestPhasesQueue.isEmpty)
            bestPhasesQueue.dequeue.addToGarbage()

      }

      if (showIntermediateTimers)
        println("$" + threadNo + ": solverTimer 3d: " + timerToElapsedMs(solverTimer) + " ms")

      // Remark: Make sure not to accidentially free any structures here which have been allocated outside the inner SAT solver procedure

      // To find off-heap memory leaks, use UNSAFEhelper.debugMode=true, call freeGarbageOffHeapMem(Long.MaxValue) here and then check
      // showRemainingAllocsDebug()

    }

  }

    var avgNormProgress = 0d

    val threadmxBean = ManagementFactory.getThreadMXBean()

    var absEliScoreScaleBaseAdaptive: Float = absEliScoreScaleBaseLow

    val loopNogoodsForEmitClauses: ObjectArrayList[IntArrayUnsafeS] = if (emitClauses) new ObjectArrayList[IntArrayUnsafeS]() else null.asInstanceOf[ObjectArrayList[IntArrayUnsafeS]]

    var alpha: Float = alphaInit

    val hashSetForComputeLBD = new IntOpenHashSet()

    val learnedNogoodReduciblesListCurrent = new ArrayValExtensibleLongUnsafe(buffer = new LongArrayUnsafeS(16 * 1024), 0)

    val learnedNogoodReduciblesListTotal = if(nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0) {

      if(freeOrReassignDeletedNogoodMemory)
        stomp(-5016, "nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0 only makes sense with freeOrReassignDeletedNogoodMemory = false")

      new ArrayValExtensibleLongUnsafe(buffer = new LongArrayUnsafeS(64 * 1024), 0)

    } else null.asInstanceOf[ArrayValExtensibleLongUnsafe]

    var noOfCurrentlyKeptLearnedNogoods = 0

    var noOfDeletedLearnedNogoods = 0

    var noOfRecycledLearnedNogoodsFromTotal = 0

    var thresholdForRemovalOfNogoods: Double = 0d

    var ngActivityCMA = 0f

    var ngActivityCMAn = 0

    var noOfSharedNogoods = 0

    var nogi: Nogi = 0

    var noOfReducibleSpaceRequests = 0

    var noOfReducibleSpaceRequestsMisses = 0

    var nii = 0

    @deprecated @inline def setThreadParams(): Unit = { // TODO: remove the need for this:

      var enforeceLearnRateComputation = rndmBranchProbR < 0 || absEliScoringApproach == 0 && !evsids || glucoseRestarts

      useLBD =
        enforceLBDemaComputation || scoringForRemovalOfLearnedNogoods == 0 || scoringForRemovalOfLearnedNogoods == 8 || scoringForRemovalOfLearnedNogoods == 11

    }

    setThreadParams()

      @inline def isSetInPass(eli: Eli): Boolean = {

        getFromlPass(eli) != 0

      }

      @inline def isNotSetInPass(eli: Eli): Boolean = {

        getFromlPass(eli) == 0

      }

      @inline def isNegSetInPass(eli: Eli): Boolean = {

         isSetInPass(-eli)

      }

      @inline def isNotAbsSetInPass(eli: Eli): Boolean = // a.k.a. variable (absEli) is unassigned (clear)
        getFromlPass(eli) == 0 && getFromlPass(-eli) == 0

      @inline def isPosOrNegSetInPass(eli: Eli): Boolean = // a.k.a. absEli is assigned (positively or negatively)
        !isNotAbsSetInPass(eli)

      @inline def setInPass(eli: Eli): Unit =
        updateInlPass(eli, 1)  // Obviously, this must only be called for a literal of an unassigned variable, that is, if both
      // eli and -eli are unset (e.g., after backtracking). Otherwise, this leads to an inconsistent state if -eli is also set.

      @inline def unsetInPass(eli: Eli): Unit =
        updateInlPass(eli, 0)  // see remarks at setIntPass

      // Don't use to unset an eli ("unassign" means unassigning the entire variable, that is, both the positive and the negative literal are unset)
      @inline def unassignInPass(eli: Eli): Unit = {

        updateInlPass(eli, 0)

        updateInlPass(-eli, 0)

      }

      @inline def setDecisionLevelTo(newDl: Eli): Unit = dl = newDl

      @inline def getIntFromReducible(addr: NogoodReducible, index: Eli): Eli =
        UNSAFE.getInt(addr + (index << 2))

      @inline def updateIntInReducible(addr: NogoodReducible, index: Eli, value: Eli): Unit =
        UNSAFE.putInt(addr + (index << 2), value)

      @inline def getLongFromReducible(addr: NogoodReducible, intIndex: Eli): NogoodReducible =
        UNSAFE.getLong(addr + (intIndex << 2))

      @inline def updateLongInReducible(addr: NogoodReducible, intIndex: Eli, value: NogoodReducible): Unit =
        UNSAFE.putLong(addr + (intIndex << 2), value)

      @inline def getFloatFromReducible(addr: NogoodReducible, index: Eli): Float =
        UNSAFE.getFloat(addr + (index << 2))

      @inline def updateFloatInReducible(addr: NogoodReducible, index: Eli, value: Float): Unit =
        UNSAFE.putFloat(addr + (index << 2), value)

      @inline def getAddrOfNogoodInReducible(addr: NogoodReducible): NogoodReducible = addr + (offsetIntsOfNogoodInReducible << 2)

      @inline def getEliFromNogoodInReducible(addr: NogoodReducible, indexInNogood: Eli): Eli =
        getIntFromReducible(addr, offsetIntsOfNogoodInReducible + indexInNogood)

      @inline def updateEliInNogoodInReducible(addr: NogoodReducible, indexInNogood: Eli, value: Eli): Unit =
        UNSAFE.putInt(addr + ((offsetIntsOfNogoodInReducible + indexInNogood) << 2), value)

      @inline def getNogoodSizeFromReducible(addr: NogoodReducible): Eli = getIntFromReducible(addr, 0)

      @inline def getTotalSizeOfReducibleInBytes(addr: NogoodReducible): Eli =
        getIntFromReducible(addr, index = offsetIntsOfNogoodInReducible - 3) << 2

      @inline def cloneNogoodReducible(addr: NogoodReducible): NogoodReducible = {

        val noOfBytes = getTotalSizeOfReducibleInBytes(addr)

        val newAddr = UNSAFE.allocateMemory(noOfBytes)

        UNSAFE.copyMemory(addr, newAddr, noOfBytes)

        newAddr

      }

      @inline def cloneNogoodInReducibleTo(addr: NogoodReducible, targetArrayUnsafe: IntArrayUnsafeS): Unit = {

        UNSAFE.copyMemory(addr + (offsetIntsOfNogoodInReducible << 2), targetArrayUnsafe.getAddr, getNogoodSizeFromReducible(addr) << 2)

      }

      @inline def setNogoodSizeInReducible(addr: NogoodReducible, newSize: Eli): Unit = /*getNogoodFromReducible(addr).sizev*/ {

        updateIntInReducible(addr, 0, newSize)

      }

      @inline def getLBDFromReducible(addr: NogoodReducible): Eli = {

        // NB: lbd in delSAT not computed for non-learned ("clark") nogood!

        val r = getIntFromReducible(addr, offsetIntsOfNogoodInReducible - 1)

        //println("r = " + r)

        r

      }

      @inline def setLBDInReducible(addr: NogoodReducible, lbd: Eli): Unit = /*getNogoodFromReducible(addr).sizev*/ {

        updateIntInReducible(addr, offsetIntsOfNogoodInReducible - 1, lbd)

      }


      @inline def nogoodInReducibleContains(addr: NogoodReducible, eli: Eli): Boolean = {

        var i = getNogoodSizeFromReducible(addr) - 1

        while (i >= 0) {

          if (getEliFromNogoodInReducible(addr, i) == eli)
            return true

          i -= 1

        }

        false

      }

      @inline def nogoodInReducibleContainsAbs(addr: NogoodReducible, eli: Eli): Boolean = {

        var i = getNogoodSizeFromReducible(addr) - 1

        val absEli = toAbsEli(eli)

        while (i >= 0) {

          if (toAbsEli(getEliFromNogoodInReducible(addr, i)) == absEli)
            return true

          i -= 1

        }

        false

      }

      @inline def countInNogoodInReducible(addr: NogoodReducible, p: Eli => Boolean): Eli = {

        var i = getNogoodSizeFromReducible(addr) - 1

        var c = 0

        while (i >= 0) {

          if (p(getEliFromNogoodInReducible(addr, i)))
            c += 1

          i -= 1

        }

        c

      }

  @inline def intersectionCountNogoodsInReducibles(red1: NogoodReducible, red2: NogoodReducible): Int = {

    val size1 = getNogoodSizeFromReducible(red1)

    val size2 = getNogoodSizeFromReducible(red2)

    if (size2 < size1)
      intersectionCountNogoodsInReducibles(red2, red1)
    else {

     var c = 0

     var i = 0

     while(i < size1) {

       if(nogoodInReducibleContains(red2, getEliFromNogoodInReducible(red1, i)))
         c += 1

       i += 1

     }

     c

    }

  }

      @inline def forEachEliInNogood(addr: NogoodReducible, what: Eli => Unit) = {

        val size = getNogoodSizeFromReducible(addr)

        var i = 0

        while (i < size) {

          what(getEliFromNogoodInReducible(addr, i))

          i += 1

        }

      }

      @inline def generateRefToNogoodInReducible(addr: NogoodReducible): NogoodReducible = { // this method should NOT be used if only access to the nogood content or size of the reducible is needed

        addr + (offsetIntsOfNogoodInReducible << 2)

      }

      @inline def psOfElisInNogoodInReducible(addr: NogoodReducible): NogoodReducible = { // can be used as a simple hash code

        var s = 1l

        var i = getNogoodSizeFromReducible(addr) - 1

        while (i >= 0) {

          s = psCombine(s, getEliFromNogoodInReducible(addr, i))

          i -= 1

        }

        s

      }

      @inline def nogoodInReducibleToString(addr: NogoodReducible): String = {

        val sb = new StringBuilder()

        var i = 0

        while (i < getNogoodSizeFromReducible(addr)) {

          sb.append(getEliFromNogoodInReducible(addr, i))

          sb.append(',')

          i += 1

        }

        sb.result

      }

      def printInfoAboutReducible(addr: NogoodReducible, metaOnly: Boolean = false): Unit = {

        println("\nReducible: " + addr + " with nogood " + nogoodInReducibleToString(addr) + " (size: " + getNogoodSizeFromReducible(addr) + ")")

        if (!metaOnly) {

          var i = 0

          while (i < getNogoodSizeFromReducible(addr)) {

            val eli = getEliFromNogoodInReducible(addr, i)

            println("  index " + i + "/eli: " + eli + " isSetInPass: " + isSetInPass(eli) + ", isNegSetInPass: " + isNegSetInPass(eli) + ", decisionLevel = " + decisionLevelOfEli(eli))

            i += 1

          }

        }

        println("at reducible index '0': " + getIntFromReducible(addr, 0) +
          ", at index '1': " + getIntFromReducible(addr, 1) +
          ", at index '2': " + getIntFromReducible(addr, 2) +
          ", at index '3': " + getIntFromReducible(addr, 3) +
          ", at index '4': " + getIntFromReducible(addr, 4)
        )

      }

      @deprecated
      @inline def incReferenceCounterOfNogoodReducible(addr: NogoodReducible): Eli = UNSAFE.getAndAddInt(null, addr + (2 << 2), 1)
      // ^observe that the returned value is the value BEFORE the increment

      @deprecated
      @inline def decReferenceCounterOfNogoodReducible(addr: NogoodReducible): Eli = UNSAFE.getAndAddInt(null, addr + (2 << 2), -1)
      // ^observe that the returned value is the value BEFORE the decrement

      @inline def isBitSetInReducibleBitsetExt3(addr: NogoodReducible, eli: Eli): Boolean = {

        val addrOfLongInBitset = addr + offsetBytesForBitsetWithExtReducibles345 + ((eliToJavaArrayIndex(eli) >> 6) << 3)

        (UNSAFE.getLong(addrOfLongInBitset) & (1l << eliToJavaArrayIndex(eli))) != 0l
        // note: only n lowest-order bits of the right-hand operand are used by <<

      }

      @inline def setBitInReducibleBitsetExt3(addr: NogoodReducible, eli: Eli): Unit = { // this is called after eli is cleared(!) in pass

        //assert(isNotSetInPass(eli))

        val addrOfLongInBitset = addr + offsetBytesForBitsetWithExtReducibles345 + ((eliToJavaArrayIndex(eli) >> 6) << 3)

        UNSAFE.putLong(addrOfLongInBitset, UNSAFE.getLong(addrOfLongInBitset) | (1l << eliToJavaArrayIndex(eli)))
        // note: only n lowest-order bits of the right-hand operand are used by <<

        if (debug2) println("Changing reducible " + addr + " unsets length from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) + 1))

        updateIntInReducible(addr, index = 1, value = getIntFromReducible(addr, index = 1) + 1)

      }

      @inline def multiplyByFactorOrSetBitInReducibleBitsetExt5(addr: NogoodReducible, eli: Eli): Unit = { // this is called after eli is cleared(!) in pass

        //assert(isNotSetInPass(eli))

        val product = getLongFromReducible(addr, intIndex = 2)

        if (product == 0l) {

          val addrOfLongInBitset = addr + offsetBytesForBitsetWithExtReducibles345 + ((eliToJavaArrayIndex(eli) >> 6) << 3)

          UNSAFE.putLong(addrOfLongInBitset, UNSAFE.getLong(addrOfLongInBitset) | (1l << eliToJavaArrayIndex(eli)))
          // note: only n lowest-order bits of the right-hand operand are used by <<

        } else {

          updateLongInReducible(addr, intIndex = 2, product * eli)

        }

        if (debug2) println("Changing reducible " + addr + " unset length from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) + 1))

        updateIntInReducible(addr, index = 1, value = getIntFromReducible(addr, index = 1) + 1)

      }

      @inline def getUnsetLengthInReducibleBitsetExt3(addr: NogoodReducible): Eli =
        getIntFromReducible(addr, index = 1)

      def countUnsetsInPassInNogood(red: NogoodReducible): Eli = { // for debugging only

        var unsets = 0
        var i = 0

        while (i < getNogoodSizeFromReducible(red)) {

          //   println("eli " + i + " in nogood = " + getEliFromNogoodInReducible(red, i) +
          //    ", set in pass: " + isSetInPass(getEliFromNogoodInReducible(red, i)) + ", in bitset: " + isSetEliInReducibleBitsetExt3(red, getEliFromNogoodInReducible(red, i)))

          if (isNotSetInPass(getEliFromNogoodInReducible(red, i)))
            unsets += 1
          i += 1

        }

        unsets

      }

      @inline def unsetBitInReducibleBitsetExt3(addr: NogoodReducible, eli: Eli): (Eli, Boolean) = { // this is called after eli is set(!) in pass

        //assert(isSetInPass(eli))

        val addrOfLongInBitset = addr + offsetBytesForBitsetWithExtReducibles345 + ((eliToJavaArrayIndex(eli) >> 6) << 3)

        val newLongValue = UNSAFE.getLong(addrOfLongInBitset) & ~(1l << eliToJavaArrayIndex(eli))

        UNSAFE.putLong(addrOfLongInBitset, newLongValue)

        val newNoOfUnsetsInPass = getIntFromReducible(addr, index = 1) - 1

        if (debug2) println("Changing reducible " + addr + " unsets length from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) - 1))

        updateIntInReducible(addr, index = 1, value = newNoOfUnsetsInPass)

        (newNoOfUnsetsInPass, newLongValue != 0l) // number of unassigned elis in nogood (i.e., where the bits in bitset are still set(!))

      }

      @inline def setProductForExt5(addr: NogoodReducible, newProduct: NogoodReducible): Eli = { // this is called after eli is set(!) in pass

        //assert(isSetInPass(eli))

        updateLongInReducible(addr, intIndex = 2, newProduct)

        val newNoOfUnsetsInPass = getIntFromReducible(addr, index = 1) - 1

        if (debug2) println("Changing reducible " + addr + " unsets length from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) - 1))

        updateIntInReducible(addr, index = 1, value = newNoOfUnsetsInPass)

        newNoOfUnsetsInPass // number of unassigned elis in nogood (i.e., where the bits in bitset are still set(!))

      }

      @inline def reduceLengthInReducibleExt4(addr: NogoodReducible, eli: Eli): Eli = { // this is called after eli is set(!) in pass

        //assert(isSetInPass(eli))

        val newNoOfUnsetsInPass = getIntFromReducible(addr, index = 1) - 1

        if (debug2) println("Changing red " + addr + " lenghth from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) - 1))

        updateIntInReducible(addr, index = 1, value = newNoOfUnsetsInPass)

        newNoOfUnsetsInPass // number of unassigned elis in nogood

      }

      @inline def increaseLengthInReducibleExt4(addr: NogoodReducible, eli: Eli): Unit = { // this is called after eli is cleared(!) in pass

        //assert(isNotSetInPass(eli))

        if (debug2) println("Changing red " + addr + " lenghth from " + getIntFromReducible(addr, index = 1) + " to " + (getIntFromReducible(addr, index = 1) + 1))

        updateIntInReducible(addr, index = 1, value = getIntFromReducible(addr, index = 1) + 1)

      }

      @inline def isConflictingReducibleBitsetExt3(addr: NogoodReducible): Boolean = {

        var i = noOfLongsForBitsetWithExtReducibles345 - 1

        while (i >= 0) {

          //println("long #" + i + " = " + UNSAFE.getLong(addr + offsetBytesForBitsetWithExtReducibles3 + (i << 3)))

          if (UNSAFE.getLong(addr + offsetBytesForBitsetWithExtReducibles345 + (i << 3)) != 0l)
            return false

          i -= 1

        }

        true

      }

      @inline def checkUnitReducibleBitsetExt3(addr: NogoodReducible): Eli /*0: nogood not unit resulting*/ = {

        var noOfSetBits = 0

        var pivotIndexOfLong = -1

        var pivotValueOfLong = -1l

        var i = 0

        while (i < noOfLongsForBitsetWithExtReducibles345) {

          var valueOfLong = UNSAFE.getLong(addr + offsetBytesForBitsetWithExtReducibles345 + (i << 3))

          if (valueOfLong != 0l) {

            val noOfSetBitsInLong = java.lang.Long.bitCount(valueOfLong) // popCount (compiles to a single instruction with x86)

            if (noOfSetBitsInLong > 1)
              return 0
            else {

              noOfSetBits += noOfSetBitsInLong

              if (noOfSetBits > 1)
                return 0
              else if (noOfSetBits == 1) {

                pivotIndexOfLong = i

                pivotValueOfLong = valueOfLong

              }

            }

          }

          i += 1

        }

        if (pivotIndexOfLong != -1) { // the nogood is unit resulting (contains exactly one eli which isn't set in the partial assignment)

          @inline def noTrailingZeros(i: NogoodReducible) = {

            // intrinsic in Java >=8. Better implementation (below) in place since Java ?:

            val x = i.toInt

            if (x == 0)
              32 + java.lang.Integer.numberOfTrailingZeros((i >>> 32).toInt)
            else
              java.lang.Integer.numberOfTrailingZeros(x)

          }

          val eliJava = noTrailingZeros /*java.lang.Long.numberOfTrailingZeros*/ (pivotValueOfLong) + pivotIndexOfLong * 64

          eliJava - noOfAbsElis

        } else
          0

      }

      @inline def findEliInUnitReducibleBitsetExt3(addr: NogoodReducible, eliInRequiredLong: Eli = 0): Eli /*result only meaningfull if exactly one unset eli in nogood*/ = {

        if (eliInRequiredLong != 0) { // we already know that the unit eli bit is in the same Long as eliInRequiredLong

          val longIndex = eliToJavaArrayIndex(eliInRequiredLong) >> 6

          //assert(valueOfLong != 0l)

          java.lang.Long.numberOfTrailingZeros(UNSAFE.getLong(addr + offsetBytesForBitsetWithExtReducibles345 + ((longIndex) << 3))) +
            (longIndex << 6) - noOfAbsElis

        } else {

          var r = 0

          var i = noOfLongsForBitsetWithExtReducibles345 - 1

          val baseAddr = addr + offsetBytesForBitsetWithExtReducibles345

          do { // there must be exactly one remaining set bit (corresponding to the
            // only remaining UNset(!) eli in the nogood)

            var valueOfLong = UNSAFE.getLong(baseAddr + (i << 3))

            if (valueOfLong != 0l) {

              //return /*java.lang.Long.*/ numberOfTrailingZeros(valueOfLong) + (i << 6) - noOfAbsElis
              r = java.lang.Long.numberOfTrailingZeros(valueOfLong) + (i << 6) - noOfAbsElis

              i = -2

            } else
              i -= 1

          } while (i >= 0)

          assert(i == -2)

          r

        }

      }

      @inline def findEliInUnitReducibleExt4(addr: NogoodReducible): Eli /*result only meaningfull if exactly one unset eli in nogood*/ = {

        var i = getNogoodSizeFromReducible(addr) - 1

        do { // there must be exactly one remaining unset eli in the nogood

          if (isNotSetInPass(getEliFromNogoodInReducible(addr, i)))
            return getEliFromNogoodInReducible(addr, i)
          else
            i -= 1

        } while (i >= 0)

        assert(false)

        0

      }

      @inline def fillUpW(addr: NogoodReducible, index: Eli, oldWContent: Eli): Eli = {

        // for |nogood|>2 only

        var i = getNogoodSizeFromReducible(addr) - 1

        var r = 0

        do {

          if (isNotSetInPass(getEliFromNogoodInReducible(addr, i))) {

            updateEliInNogoodInReducible(addr, index, getEliFromNogoodInReducible(addr, i))

            updateEliInNogoodInReducible(addr, i, oldWContent)

            //return getEliFromNogoodInReducible(addr, index) // it appears the JVM or CPU doesn't like return branches
            r = getEliFromNogoodInReducible(addr, index)

            i = 0

          } else
            i -= 1

        } while (i >= 2)

        r

      }



      @inline def isClarkReducible(reducible: NogoodReducible): Boolean =
        getIntFromReducible(reducible, offsetIntsOfNogoodInReducible - 1) == -1

      @inline def setItemIndicExt1(addr: NogoodReducible, item: Eli): Eli = { // variant with reducible literals external to the nogood

        //if (extraChecks) assert(!isNogoodInReducibleMarkedForDeletion(addr))

        @inline def fillUpExt1(cpiEli: Eli /*<-- this is always getIntFromReducible(addr, 3)*/
                              ): Boolean = { // the by far most busy method in delSAT

          // simple, using intIndex = 1 (but not updating it!) and end marker 0:

          var addri = getLongFromReducible(addr, intIndex = 1)

          do {

            if (isNotSetInPass(UNSAFE.getInt(addri)) && UNSAFE.getInt(addri) != cpiEli) {

              updateIntInReducible(addr, 4, UNSAFE.getInt(addri))

              return false

            }

            addri += 4l

          } while (UNSAFE.getInt(addri) != 0)

          updateIntInReducible(addr, 4, 0)

          true

        }

        // NB: deleting remainders from eliToNogoodRemainders(item), where required, must be taken care of by the caller!

        if (getNogoodSizeFromReducible(addr) == 1) {

          assert(item == getIntFromReducible(addr, 3))

          assert(getIntFromReducible(addr, 3) != 0)

          updateIntInReducible(addr, 3, 0)

          eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

          0 // conflict

        } else if (getNogoodSizeFromReducible(addr) == 2) {

          if (item == getIntFromReducible(addr, 3)) {

            if (getIntFromReducible(addr, 4) != 0) {

              //updateIntInReducible(addr, 3, getIntFromReducible(addr, 4))
              UNSAFE.copyMemory(addr + (4 << 2), addr + (3 << 2), 1 << 2)

              updateIntInReducible(addr, 4, 0)

              eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

              getIntFromReducible(addr, 3) // propagate

            } else {

              updateIntInReducible(addr, 3, 0)

              eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

              0  // conflict

            }

          } else if (item == getIntFromReducible(addr, 4)) {

            assert(getIntFromReducible(addr, 3) != 0)

            updateIntInReducible(addr, 4, 0) // NB: it's not possible here that get(addr, 1) == -1

            eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

            getIntFromReducible(addr, 3)

          } else {

            assert(false)

            Int.MaxValue

          }

        } else if (item == getIntFromReducible(addr, 3)) {

          if (getIntFromReducible(addr, 4) != 0) {

            UNSAFE.copyMemory(addr + (4 << 2), addr + (3 << 2), 1 << 2)

            if (fillUpExt1(getIntFromReducible(addr, 3) /*, item*/)) { // we try to refill (4) with an unset eli (omitting (3) in the search)

              // no success, so (3) is the only unset eli left in the nogood, so (3) is unit-resulting

              eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

              getIntFromReducible(addr, 3) // propagates -(3)

            } else {

              // both (3) and (4) are still unset

              eliWatchedToReducibles(eliToJavaArrayIndex(getIntFromReducible(addr, 4))).addReducibleUS(addr)

              Int.MaxValue // nothing else to do

            }

          } else if (getIntFromReducible(addr, 3) != 0) {

            updateIntInReducible(addr, 3, 0)

            eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

            0 // conflict

          } else
            6666666

        } else {

          if (item != getIntFromReducible(addr, 4))
            stomp(-10000, "Consistency check failure, item != getIntFromReducible(addr, 4)")

          assert(getIntFromReducible(addr, 3) != 0)

          if (fillUpExt1(getIntFromReducible(addr, 3 /*sic!*/))) {

            eliToReduciblesDeficitResto(eliToJavaArrayIndex(item)).addReducibleUS(addr) //  we have a deficit now (less than two literals selected for this nogood) which we need to rectify later when jumping back

            getIntFromReducible(addr, 3)

          } else {

            eliWatchedToReducibles(eliToJavaArrayIndex(getIntFromReducible(addr, 4))).addReducibleUS(addr)

            Int.MaxValue

          }

        }

      }

      if (showIntermediateTimers)
        println("$" + threadNo + ": solverTimer 1: " + timerToElapsedMs(solverTimer) + " ms")

      @inline def absEliBasedNogoodScore(nogoodReducible: NogoodReducible): Double = {

        // Higher result = better, i.e., it means lower probability of being removed for a learned nogood

        var absEliNogoodScore = 0d

        var kk = getNogoodSizeFromReducible(nogoodReducible) - 1

        while (kk >= 0) {

          absEliNogoodScore += getAbsEliScore(toAbsEli(getEliFromNogoodInReducible(nogoodReducible, kk)))

          kk -= 1

        }

        val r = absEliNogoodScore / getNogoodSizeFromReducible(nogoodReducible).toDouble

        if (r.isNaN) { // should not happen, but we must catch this to avoid that the contract of comparators which use this score is violated

          Double.MinValue

        } else
          r

      }

      @inline def computeLBD(nogoodReducible: NogoodReducible /*, upperBound: Int = Int.MaxValue*/): Eli = {

        val lbd = if (getNogoodSizeFromReducible(nogoodReducible) == 2) {

          2

        } else {

          var lbda = 0

          hashSetForComputeLBD.clear()

          var kk = 0

          //println("\nnogoodReducible = " + nogoodReducible)

          while (kk < getNogoodSizeFromReducible(nogoodReducible)) {

            // Remark: We and most solvers store decision levels for entire variables. Thus:

            val dl = decisionLevelOfEli((getEliFromNogoodInReducible(nogoodReducible, kk)))

            //println("     dl = " + dl)

            if (dl != Int.MinValue && hashSetForComputeLBD.add(dl)) {

              lbda += 1

            }

            kk += 1

          }

          lbda

        }

       lbd

      }

      @inline def lbdNogoodScore(nogoodReducible: NogoodReducible /*, useCache: Boolean = true*/): Double = {
        // The higher the score the better, i.e., less likely is the learned nogood to be removed (i.e., high score = nogood is "good").
        // NB: with reduceLearnedNogoodAtRestartsOnly = true (i.e., if this method is called only directly after restarts), the
        // LBD is always 0.
        // Remark: LBD is originally defined for clauses, not nogoods.

        val r = if (keepGlue >= 0) {

          val lbd: Eli = getLBDFromReducible(nogoodReducible)

          //println("lbd: " + lbd)

          if (lbd <= keepGlue)
            1d //Double.MaxValue // nogoods with lbd = 2 should normally never be removed
          else
            (1d + (-lbd.toDouble / 10d)).max(0d)

        } else {

          val lbd: Eli = getLBDFromReducible(nogoodReducible)

          //println("lbdScore = " + lbdScore)

          if (lbd <= -keepGlue)
            1d
          else
            0d

        }

        //println("r: " + r)

        r

      }

      @inline def getLearnedNogoodReducibleActivity(nogoodReducible: NogoodReducible): Float =
       getFloatFromReducible(nogoodReducible, index = offsetIntsOfNogoodInReducible - 4)

      @inline def setLearnedNogoodReducibleActivity(nogoodReducible: NogoodReducible, newActivity: Float): Unit = {

        updateFloatInReducible(nogoodReducible, index = offsetIntsOfNogoodInReducible - 4, newActivity) //learnedNogoodReducibleActivity.put(nogoodReducible, newActivity)

        ngActivityCMA = (newActivity + ngActivityCMAn * ngActivityCMA) / (ngActivityCMAn + 1)

        ngActivityCMAn += 1

      }


      @inline def bumpNogoodReducibleActivity(nogoodReducible: NogoodReducible): Unit = {

        val oldNogoodActivity = getLearnedNogoodReducibleActivity(nogoodReducible)

        val newNogoodActivity = oldNogoodActivity + nogoodActivityBump

        setLearnedNogoodReducibleActivity(nogoodReducible, newNogoodActivity)

        if (newNogoodActivity > 1e37f) {

          // There isn't really much we can do here (?) if we store the activities inside the reducibles

          nogoodActivityBump = 1e-37f // well...  //TODO

          nogoodActivityDecay = 1e-20f

        }

        //println("\n" + learnedNogoodReducibleActivity.get(nogoodReducible))

      }

      @inline def getNogoodReducibleScore(nogoodReducible: NogoodReducible, scoringForRemovalOfLearnedNogoods: Eli): Double = {

        // Higher=better, that is, a higher result means lower probability of being removed for this nogood. The scores
        // must only be used to compare them with other using <, >, =, as they aren't normalized.
        // Don't use them in comparison against some constant value!

        {

          if (getNogoodSizeFromReducible(nogoodReducible) <= highestScoreForLearnedNogoodUpToSize)
            return Double.MaxValue // (observe that we'll need to add up these values at one point, so there we'll have to skip MaxValue)

          if (scoringForRemovalOfLearnedNogoods == 8) {

            //  val r = absEliBasedNogoodScore(nogoodReducible) * lbdNogoodScore(nogoodReducible) // seems to be most efficient?

            val r = absEliBasedNogoodScore(nogoodReducible) * lbdNogoodScore(nogoodReducible)

            //println(r)

            r

          } else if (scoringForRemovalOfLearnedNogoods == 1) {

            val r = getLearnedNogoodReducibleActivity /*learnedNogoodReducibleActivity.get*/ (nogoodReducible) //* lbdNogoodScore(nogoodReducible)

            r

          } else if (scoringForRemovalOfLearnedNogoods == 11) {

            val r = getLearnedNogoodReducibleActivity(nogoodReducible) * lbdNogoodScore(nogoodReducible)

           // if(noOfNogoodRemovalPhases % 2 == 0) println(r)

            r

          } else if (scoringForRemovalOfLearnedNogoods == 6) {

            assert(false) // not working anymore (getIntFromReducible(...,4) isn't updated anymore)

            -1d

          } else if (scoringForRemovalOfLearnedNogoods == 3) {

            absEliBasedNogoodScore(nogoodReducible) // based on the individual absEli scores of the elis in the nogood

          } else if (scoringForRemovalOfLearnedNogoods == 0) {

            val r = lbdNogoodScore(nogoodReducible)

            // println(r)

            r

          } else if (scoringForRemovalOfLearnedNogoods == 7) {

            1d / getNogoodSizeFromReducible(nogoodReducible).toDouble

          } else if (scoringForRemovalOfLearnedNogoods == 9) {

            (1d / getNogoodSizeFromReducible(nogoodReducible).toDouble) * absEliBasedNogoodScore(nogoodReducible)

          } else if (scoringForRemovalOfLearnedNogoods == 10) {

            assert(false) // not working anymore (getIntFromReducible(...,4) isn't updated anymore)

            -1d

          } else if (scoringForRemovalOfLearnedNogoods == 2) {

            1d / absEliBasedNogoodScore(nogoodReducible) // useful?

          } else {

            // assert(false)

            -1d

          }

        }

      }

      @inline def unSetItemExt01(reducible: NogoodReducible, item: Eli /*must be element of nogood in reducible addr*/): Unit = {

        assert(extReducibles != 3)

          // TODO: are the == 0 checks here necessary? If not, remove and also don't set |nogood|=1 watch 3 to 0 in setItemIndicExt

          if (getIntFromReducible(reducible, 3) == 0 /*-1*/ && item != getIntFromReducible(reducible, 4)) {

            updateIntInReducible(reducible, 3, item)

            val s = getNogoodReducibleScore(reducible, 11)

            eliWatchedToReducibles(eliToJavaArrayIndex(item)).addReducibleUS(reducible)

          } else if (getIntFromReducible(reducible, 4) == 0 /*-1*/ && item != getIntFromReducible(reducible, 3)) {

            updateIntInReducible(reducible, 4, item)

            eliWatchedToReducibles(eliToJavaArrayIndex(item)).addReducibleUS(reducible)

          } else if (false) { //  the entire rest of this method is optional (TODO: remove?) - we move the cleared eli to the nogood front so that it's found quicker with fillUp:

            // not effective:

            var addri = reducible + (offsetIntsOfNogoodInReducible << 2)

            val addriFirst = addri

            var lastAddri = addri + ((getNogoodSizeFromReducible(reducible) - 1) << 2)

            addri += 4l

            while (addri <= lastAddri) {

              if (UNSAFE.getInt(addri) == item) {

                val h = UNSAFE.getInt(addriFirst)

                UNSAFE.putInt(addriFirst, item)

                UNSAFE.putInt(addri, h)

                return

              }

              addri += 4l

            }

          }


          if (keepNogoodsWeaklySorted) { // not effective?

            var addri = reducible + (offsetIntsOfNogoodInReducible << 2)

            val addriFirst = addri

            var lastAddri = addri + ((getNogoodSizeFromReducible(reducible) - 1) << 2) //addr + ((offsetOfNogoodInReducible + getNogoodSizeFromReducible(addr) - 1) << 2)

            while (isNotSetInPass(UNSAFE.getInt(addri)) && addri <= lastAddri) {

              if (UNSAFE.getInt(addri) == item)
                return

              addri += 4l

            }

            val swapAddr = addri

            while (addri <= lastAddri) {

              if (UNSAFE.getInt(addri) == item) {

                UNSAFE.putInt(addri, UNSAFE.getInt(swapAddr))

                UNSAFE.putInt(swapAddr, item)

                return

              }

              addri += 4l

            }

          }

      }

      @inline def setupNewReducibleForExt2(newReducible: NogoodReducible): Unit = {

        assert(extReducibles == 2)

        updateLongInReducible(newReducible, intIndex = 1, newReducible + (offsetIntsOfNogoodInReducible << 2) + 8l /*because the first two are the watches*/)

        updateIntInReducible(newReducible, index = offsetIntsOfNogoodInReducible + getNogoodSizeFromReducible(newReducible), 0)

        updateIntInReducible(newReducible, index = offsetIntsOfNogoodInReducible + getNogoodSizeFromReducible(newReducible) + 1, 0)

      }

      @inline def setupNewReducibleForExt1(newReducible: NogoodReducible, beforeSolvingstarted: Boolean): Unit = {

        // Does nothing for extReducibles != 1

        // NB: initialization for other fields in the reducible should be done at end of conflictAnalysis()

        assert(extReducibles == 1)

        {

          updateIntInReducible(newReducible, index = offsetIntsOfNogoodInReducible + getNogoodSizeFromReducible(newReducible), 0) //FFF
          // println("setup " + newReducible + ", size = " + getNogoodSizeFromReducible(newReducible))

          updateLongInReducible(newReducible, intIndex = 1, newReducible + (offsetIntsOfNogoodInReducible << 2))

          if (beforeSolvingstarted) {

            updateIntInReducible(newReducible, 3, getEliFromNogoodInReducible(newReducible, 0) /*nogood.get(0)*/)

            if (extraChecks) assert(getIntFromReducible(newReducible, 3) != 0)

            if (getNogoodSizeFromReducible(newReducible) > 1) {

              updateIntInReducible(newReducible, 4, /*nogood.get(1)*/ getEliFromNogoodInReducible(newReducible, 1))

              if (extraChecks) assert(getIntFromReducible(newReducible, 4) != 0)

            } else
              updateIntInReducible(newReducible, 4, 0)

          } else {

            updateIntInReducible(newReducible, 3, 0)

            updateIntInReducible(newReducible, 4, 0)

            var highestDecLevel = Double.MinValue

            val start = 0

            var i = start

            while (true) {

              if (isNotSetInPass(getEliFromNogoodInReducible(newReducible, i))) {

                if (getIntFromReducible(newReducible, 3) == 0) {

                  updateIntInReducible(newReducible, 3, getEliFromNogoodInReducible(newReducible, i))

                  //if (extraChecks) assert(intArray.get(3) != 0)
                  if (extraChecks) assert(getIntFromReducible(newReducible, 3) != 0)

                } else if (getIntFromReducible(newReducible, 4) == 0 &&
                    getEliFromNogoodInReducible(newReducible, i) != getIntFromReducible(newReducible, 3)) {

                  if (true || highestDecLevel < decisionLevelOfEli(toAbsEli(getEliFromNogoodInReducible(newReducible, i)))) {

                    updateIntInReducible(newReducible, 4, getEliFromNogoodInReducible(newReducible, i))

                    if (extraChecks) assert(getIntFromReducible(newReducible, 4) != 0)

                    return // picking the one with highest decision level doesn't seem to be beneficial?

                    highestDecLevel = decisionLevelOfEli(toAbsEli(getEliFromNogoodInReducible(newReducible, i)))

                  }

                }

              }

              i += 1

              if (i == getNogoodSizeFromReducible(newReducible))
                i = 0

              if (i == start) {
                return

              }

            }

          }


        }

      }

    @inline def setItemIndicExt2(addr: NogoodReducible, item: Eli,
                                 pivotEliToReducibles: NogoodReduciblesSequenceUnsafe,
                                 pivotIndexInReduciblesSeqAddr: Long): Eli = { // similar to propagate in Minisat (but observe several differences)

      if (debug2) {

        println("\n---------------\nin setItemIndicExt2, start, item = " + item + ":")

        printInfoAboutReducible(addr)

      }

      assert(isSetInPass(item))

      val nogoodSize = getNogoodSizeFromReducible(addr)

      if (nogoodSize == 1) {

        0 // conflict

      } else if (nogoodSize == 2) {

        val e0 = getEliFromNogoodInReducible(addr, 0)

        if (item == e0) {

          val e1 = getEliFromNogoodInReducible(addr, 1)

          if (isSetInPass(e1))
            0
          else if (isNegSetInPass(e1))
            Int.MaxValue
          else
            e1

        } else {

          if (isSetInPass(e0))
            0
          else if (isNegSetInPass(e0))
            Int.MaxValue
          else
            e0

        }

      } else {

        @inline def acts(pivotIndex: Eli, possUnitEli: Eli): Eli = { // the most time consuming method in delSAT's SAT core

          if (isNegSetInPass(possUnitEli)) { // nogood cannot be true => nothing to do

            Int.MaxValue

          } else {

             var addri = addr + (offsetIntsOfNogoodInReducible << 2) + 8l // = address of literal_2 in nogood (literals _0 and _1 are the watches)

            val endAddr = addri + ((nogoodSize - 2) << 2)

            while (isSetInPass(UNSAFE.getInt(addri))) { // to make this loop terminate, there must be an end marker "literal"
              // 0 after the last literal for which isSetInPass returns false (which requires that vPass(0) != 0).

              addri += 4l

            }

            if (addri < endAddr) {

              val u = UNSAFE.getInt(addri)

              {

                pivotEliToReducibles.removeByAddrUS(pivotIndexInReduciblesSeqAddr)

                updateEliInNogoodInReducible(addr, pivotIndex, u)

                UNSAFE.putInt(addri, item)

                eliWatchedToReducibles(eliToJavaArrayIndex(u)).addReducibleUS(addr)

                return Int.MaxValue-1

              }

              if (debug2) println("  action 2: moved reducible to list of eli " + u)

              //updateLongInReducible(addr, intIndex = 1, addri)  // updates search start for next tome. If activated,
              // must also activate the if(false)... branch below

              Int.MaxValue

            } else {

               if (isSetInPass(possUnitEli)) // conflict
                0 // Remark: this is different from Minisat 1 where conflicts are discovered by a pos/neg literal clash,
                  // but alike Minisat 2
                  else { // Unit resulting

                  // now we know that all but one eli are true and the remaining eli is unassigned

                  if (debug2) println("  action 3: unit resulting, propagating neg of eli " + possUnitEli)

                  possUnitEli

                }

            }

          }

        }

        if (item == getEliFromNogoodInReducible(addr, 0))
          acts(pivotIndex = 0, getEliFromNogoodInReducible(addr, 1))
        else
          acts(pivotIndex = 1, getEliFromNogoodInReducible(addr, 0))

      }

    }

    @inline def findSpaceForLearnedNogoodReducibleForFreeMemoryApproach0(requiredSize: Eli): NogoodReducible /*slot address*/ = {

      noOfReducibleSpaceRequests += 1

      val it: ObjectBidirectionalIterator[Int2ObjectMap.Entry[LongArrayList]] = freeNogoodReducibleMemoryMap.int2ObjectEntrySet().iterator()

      while (it.hasNext) { // lowest key (smallest memory slot) comes first

        val s = it.next()

        val slotSize = s.getIntKey

        //println("in findSpace: " + s.getIntKey + ", " + s.getValue.size + ", requiredSize: " + requiredSize)

        if (slotSize >= requiredSize) {

          val listOfAddrs: LongArrayList = s.getValue

          if (listOfAddrs.size > 0) {

            val foundSpace = listOfAddrs.removeLong(listOfAddrs.size - 1)

            //assert(slotSize > 0)

            occupiedNogoodReducibleMemoryMap.put(foundSpace, slotSize)

            return foundSpace

          }

        }

      }

      noOfReducibleSpaceRequestsMisses += 1

      val newSpace = allocateOffHeapMem(requiredSize << 2)

      //assert(requiredSize > 0)

      occupiedNogoodReducibleMemoryMap.put(newSpace, requiredSize)

      newSpace

    }

    @inline def makeNogoodSpaceAvailable(reducible: NogoodReducible /*, fromReduceNogoods: Boolean = false*/): Unit = { // YYY

      assert(freeOrReassignDeletedNogoodMemory)

      if (freeDeletedNogoodMemoryApproach == 2) {

        if (extReducibles != 1 && extReducibles != 2)
          stomp(-5006, "freeDeletedNogoodMemoryApproach == 2 only allowed with extReducibles 1 or 2")

        //assert(!isClarkReducible(reducible))

        fmStackThreadLocal.append(reducible)

      } else if (freeDeletedNogoodMemoryApproach == 3) {  // TODO: remove? (also mode 1)

        assert(extReducibles == 0 || extReducibles == 1 || extReducibles == 2)

        sharedAmongSingleSolverThreads.fmStackGlobal.synchronized {

          sharedAmongSingleSolverThreads.fmStackGlobal.add(reducible)

          if (freeDeletedNogoodMemoryApproach == 3 && sharedAmongSingleSolverThreads.fmStackGlobal.size >= sharedAmongSingleSolverThreads.fmStackGlobalCapacity) {

            do {

              val red = sharedAmongSingleSolverThreads.fmStackGlobal.popLong()

              freeOffHeapMem(red, getTotalSizeOfReducibleInBytes(red))

            } while (sharedAmongSingleSolverThreads.fmStackGlobal.size > 0)

          }

        }

      } else if (freeDeletedNogoodMemoryApproach == 1) {

        freeOffHeapMem(reducible, getTotalSizeOfReducibleInBytes(reducible))

      } else if (freeDeletedNogoodMemoryApproach == 0) /*freeNogoodReducibleMemoryMap.synchronized*/ {

        val key = occupiedNogoodReducibleMemoryMap.remove(reducible)

        assert(key > 0)

        var notFound = false

        val listOfLongs = freeNogoodReducibleMemoryMap.getOrDefault(key, {

          notFound = true;

          new LongArrayList(16)

        })

        listOfLongs.add(reducible)

        if (notFound)
          freeNogoodReducibleMemoryMap.put(key, listOfLongs)

      }

    }

    @inline def reserveReducibleSpace(requiredReducibleSpaceSizeInNoOfInts: Eli): NogoodReducible = {

      val reducibleSpace = if (freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach == 0) {
        // firstly, we try to find space in the freed memory from deleted nogood reducibles:

        //println("\n\n------- required size: " + requiredSize)

        val foundSpace: NogoodReducible = findSpaceForLearnedNogoodReducibleForFreeMemoryApproach0(requiredReducibleSpaceSizeInNoOfInts)

        assert(foundSpace > 0l)

        foundSpace

        //println("---------------------")

      } else {

        if (freeOrReassignDeletedNogoodMemory && freeDeletedNogoodMemoryApproach == 2) {

          noOfReducibleSpaceRequests += 1

          // println("\nfmStackThreadLocal.size = " + fmStackThreadLocal.size)

          var i = 0

          while (i < fmStackThreadLocal.size) {

            val fmStackEntry = fmStackThreadLocal.get(i)

            val availableSpaceInInts = getIntFromReducible(fmStackEntry, offsetIntsOfNogoodInReducible - 3)

            if (availableSpaceInInts >= requiredReducibleSpaceSizeInNoOfInts) {

              if (i < fmStackThreadLocal.size - 1)
                fmStackThreadLocal.update(i, fmStackThreadLocal.popLast)
              else
                fmStackThreadLocal.removeByIndex(i)

              return fmStackEntry

            }

            i += 1

          }

          noOfReducibleSpaceRequestsMisses += 1

        }

        val r = allocateOffHeapMem(requiredReducibleSpaceSizeInNoOfInts << 2)

        r

      }

      reducibleSpace

    }

    @inline def initializeReducibleBitsetExt35(addr: NogoodReducible): Unit = {

      var tryToUseProduct = extReducibles == 5

      if (tryToUseProduct) {

        updateLongInReducible(addr, intIndex = 2, 1l) // product of the unset elis in nogood

        updateIntInReducible(addr, index = 1, value = 0)

        if (getNogoodSizeFromReducible(addr) <= ensuredMaxNoElisInNogoodForProductRepresentationWithExt5) {

          var i = getNogoodSizeFromReducible(addr) - 1

          do {

            if (isNotSetInPass(getEliFromNogoodInReducible(addr, i)))
              multiplyByFactorOrSetBitInReducibleBitsetExt5(addr, getEliFromNogoodInReducible(addr, i)) // this also updates the reducible length (#unset elis in nogood)

            i -= 1

          } while (i >= 0)

        } else { // we check whether the actual product overflows.

          var pForOverflowCheck = 1l // this becomes the product of ALL elis in nogood (both set and unset), for checking if we can use a product instead of a bitset

          try {

            var i = getNogoodSizeFromReducible(addr) - 1

            do {

              pForOverflowCheck = java.lang.Math.multiplyExact(pForOverflowCheck, getEliFromNogoodInReducible(addr, i).toLong)

              if (isNotSetInPass(getEliFromNogoodInReducible(addr, i))) {

                multiplyByFactorOrSetBitInReducibleBitsetExt5(addr, getEliFromNogoodInReducible(addr, i)) // this also updates the reducible length (#unset elis in nogood)

              }

              i -= 1

            } while (i >= 0)

          } catch {

            case e: ArithmeticException => tryToUseProduct = false

          }

        }

      }

      if (!tryToUseProduct) { // we have to use a bitset instead of the product

        updateLongInReducible(addr, intIndex = 2, 0l)

        var i = 0

        while (i < noOfLongsForBitsetWithExtReducibles345) {

          UNSAFE.putLong(addr + offsetBytesForBitsetWithExtReducibles345 + (i << 3), 0l)

          i += 1

        }

        updateIntInReducible(addr, index = 1, value = 0)

        i = getNogoodSizeFromReducible(addr) - 1

        do {

          if (isNotSetInPass(getEliFromNogoodInReducible(addr, i))) {

            setBitInReducibleBitsetExt3(addr, getEliFromNogoodInReducible(addr, i)) // this also updates the reducible length (#unset elis in nogood)

          }

          i -= 1

        } while (i >= 0)

      }

    }

    @inline def initializeReducibleBitsetExt4(addr: NogoodReducible): Unit = {

      var i = getNogoodSizeFromReducible(addr) - 1

      var noOfUnsetElisInNogood = 0

      do {

        if (isNotSetInPass(getEliFromNogoodInReducible(addr, i)))
          noOfUnsetElisInNogood += 1

        i -= 1

      } while (i >= 0)

      updateIntInReducible(addr, index = 1, value = noOfUnsetElisInNogood)

    }

    @inline def generateNogoodReducibleFromNogoodClarkOrSpecial(nogoodAddr: NogoodReducible, nogoodSize: Eli,
                                                                beforeSolvingstarted: Boolean /*,
                                                                  atReducibleAddress: Long = -1l*/): NogoodReducible = {

      // Mainly for setting up the meta information (but NOT the watches) of clark nogoods, and for some minor tasks (e.g., setting up transfer nogoods).
      // This method is NOT used to set up regular learned nogood reducibles, as these use a more efficient setup
      // in conflictAnalysis().
      // Also,

      //assert(atReducibleAddress == -1l || beforeSolvingstarted)

      assert(nogoodSize > 0)

      val reducibleSlotSize = offsetIntsOfNogoodInReducible + nogoodSize + offsetIntsOfNogoodInReducible

      val newReducible: NogoodReducible = {

          val reducibleSpace = reserveReducibleSpace(reducibleSlotSize)

          val targetAddr = reducibleSpace + (offsetIntsOfNogoodInReducible << 2)

          UNSAFE.copyMemory(nogoodAddr, targetAddr, nogoodSize << 2)

          reducibleSpace

      }

      setNogoodSizeInReducible(newReducible, nogoodSize)

      updateIntInReducible(newReducible, index = offsetIntsOfNogoodInReducible - 2, 1 /*<-to avoid NaN*/)

      updateIntInReducible(newReducible, index = offsetIntsOfNogoodInReducible - 3, reducibleSlotSize)

      if (extReducibles == 2)
        setupNewReducibleForExt2(newReducible)
      else if (extReducibles == 1)
        setupNewReducibleForExt1(newReducible, beforeSolvingstarted = false)
      else if (extReducibles == 4)
        initializeReducibleBitsetExt4(newReducible)
      else if (extReducibles == 5 || extReducibles == 3)
        initializeReducibleBitsetExt35(newReducible)

      updateIntInReducible(newReducible, offsetIntsOfNogoodInReducible - 1, -1) // actually the LBD slot for learned nogoods. For
      //"Clark" nogoods, we set this to -1 to distinguish "Clark" from learned nogoods.

      newReducible

    }

    @inline def getBinFromScoreForFreeEliSearchApproach15(score: Double): Eli = {

      assert(freeEliSearchApproach == 15)

      @inline def gbin(x: Double): Eli = {

        val r = if (absEliScoringApproach == 0) {

          // A skewed and shifted approximated Gaussian error function.
          // Purely heuristically assuming that scores have the highest density around 300, that is,
          // we allocate more bins to that range.
          // Upper bound for x~1000 (also see rescheduling threshold in setScoreOfAbsEli!)

          @inline def g0(x: Float): Float =
            1f - 1f / Math.pow(1 + 0.278393 * x + 0.230389 * x * x + 0.000972 * x * x * x + 0.078108 * x * x * x * x, 4).toFloat

          @inline def g1(x: Float): Float = {

            if (x >= 0)
              g0(x)
            else
              -g0(-x)

          }

          g1((Math.pow(x, 1.2f).toFloat - 1000f + 0f) * 0.0005f) *
            (unassignedAbsEliBinSet.length.toFloat - 15f) + (unassignedAbsEliBinSet.length.toFloat / 2f)

          // Try also:
          // java.lang.Math.log(x * 10000)
          // java.lang.Math.getExponent(x) * 37

        } else {

          x * unassignedAbsEliBinSet.length // here we assume that the scores are already normalized to [0,1]

        }

        r.toInt.min(unassignedAbsEliBinSet.length - 1).max(0)

      }

      val bin = gbin(score)

      bin

    }

    @inline def updateBinOfAbsEliInUnassignedAbsEliBinSet(absEli: Eli, newScore: Float) = {

      val oldBin = getBinFromScoreForFreeEliSearchApproach15(getAbsEliScore(absEli))

      if (unassignedAbsEliBinSet(oldBin).contains(absEli)) {

        //assert(isNotAbsSetInPass(absEli))

        val newBin = getBinFromScoreForFreeEliSearchApproach15(newScore)

        if (newBin != oldBin) {

          unassignedAbsEliBinSet(oldBin).remove(absEli)

          //assert(!unassignedAbsEliBinSet(oldBin).contains(absEli))

          //println("Moving " + absEli + " from bin " + oldBin + " to bin " + newBin)

          unassignedAbsEliBinSet(newBin).add(absEli)

          //assert(unassignedAbsEliBinSet(newBin).contains(absEli))

        }

      } //else
      //assert(isPosOrNegSetInPass(absEli))

    }

    @inline def setScoreOfAbsEli(absEli: Eli, newScoreR: Float, updateInHeap: Boolean = true/*, ign: Boolean = true*/): Unit = { {

      val newScore = if (newScoreR == 1.0f / 0.0f /*.isInfinite*/ ) { // .isInfinite is more costly (boxing)

        scheduleRescaleAbsElis = true

        Float.MaxValue

      } else if (newScoreR > (if (freeEliSearchApproach == 15) 1000f else 1e30f) /*1e30d*/ ) {
        // see getBinFromScoreForFreeEliSearchApproach15 for motivation of 1000f

        // TODO: the upper bound 1000 for freeEliSearchApproach == 15 doesn't work well with useScoresInSLS

        scheduleRescaleAbsElis = true

        newScoreR

      } else if (newScoreR.isNaN)
        0f
      else
        newScoreR

      if (!updateInHeap)
        updateAbsEliScore(absEli, newScore)
      else if (freeEliSearchApproach == 15) {

        updateBinOfAbsEliInUnassignedAbsEliBinSet(absEli, newScore)

        updateAbsEliScore(absEli, newScore)

      } else if (freeEliSearchApproach == 14 && unassignedAbsEliSet.contains(absEli))
        unassignedAbsEliSet.updateScoreSorted(absEli, newScore) // (this call also updates absEliScore)
      else if (freeEliSearchApproach == 11) {

        if (updateHeapInFreeElisPriorityQueueEvery == 1 ||
          fastModByPow2(incAbsEliScoreUpdates(absEli), updateHeapInFreeElisPriorityQueueEvery) == 0) {

          // The following is not required with absEliScoringApproach=0 as there the bumped up absEli aren't part of the the queue anyway
          if (absEliScoringApproach != 0 && unassignedScoredAbsElisPriorityQueue.containsElem(absEli)) {

            val oldScore = getAbsEliScore(absEli)

            updateAbsEliScore(absEli, newScore)

            if (updateHeapInFreeElisPriorityQueueEvery < 2) {

              if (oldScore > newScore)
                unassignedScoredAbsElisPriorityQueue.upHeap(absEli)
              else
                unassignedScoredAbsElisPriorityQueue.downHeap(absEli)

            } else if (newScore != oldScore)
              unassignedScoredAbsElisPriorityQueue.changed(absEli)

          } else
            updateAbsEliScore(absEli, newScore)

        } else
          updateAbsEliScore(absEli, newScore)

      } else
        updateAbsEliScore(absEli, newScore)

    }
    }

    @inline def bumpUpEVSIDSscoreOfAbsEli(absEli: Eli, absEliScoreBumpAmount: Float): Unit = { // for absEliScoringApproach = 0

      setScoreOfAbsEli(absEli, getAbsEliScore(absEli) + absEliScoreBumpAmount)

    }

    @inline def bumpUpEVSIDSscoreOfAbsEliMinimally(absEli: Eli): Unit = { // for absEliScoringApproach = 0

      val oldScore = getAbsEliScore(absEli)

      val r = Math.nextUp(getAbsEliScore(absEli))
      setScoreOfAbsEli(absEli, r)

    }

    @inline def updScoreInNgElis(involvedNogoodAddr: NogoodReducible, length: Eli): Float = {

      var ii = 0

      if (absEliScoringApproach == 2) {

        ii = 0

        while (ii < length) {

          incParticipatedAbsEli(toAbsEli(UNSAFE.getInt(involvedNogoodAddr + (ii << 2))))

          ii += 1

        }

        -1f

      } else if (absEliScoringApproach == 1) {

        ii = 0

        while (ii < length) {

          updateLastConflictOfAbsEli(toAbsEli(UNSAFE.getInt(involvedNogoodAddr + (ii << 2))), getNoOfConflictsForERWA)

          ii += 1

        }

        -1f

      } else if (absEliScoringApproach == 0) {

        val bump: Float = (if (evsids) /*powApproxInt*/ powFloat(absEliScoreScaleBaseAdaptive, noOfConflictsAfterRestart / 1000f)
          else
          /*powApproxInt*/ powFloat(1f / absEliScoreScaleBaseAdaptive, noOfConflictsTotal.toFloat / 10000000f)).toFloat

        // Approach is adaptVSIDS, i.e. a variant of EVSIDS (exponential MiniSAT variant of NVSIDS)
        // (we update absEliScoreScaleBaseAdaptive differently from MiniSAT, using adaptVSIDS, apart from working with nogoods instead of clauses).

        // See http://fmv.jku.at/papers/BiereFroehlich-SAT15.pdf
        // https://hriener.github.io/misc/lsss19/Biere-LSSS19-talk.pdf

        // NB: while EVSIDS makes regular rescoring of all absElis redundant (we only bump absElis involved in the current
        // conflict and can ignore other absElis), scores can still overflow, thus we still need to rescore all(!)
        // absElis occasionally (see possiblyRescaleAllAbsElis).

        //println("bump = " + bump)

        //println("noOfConflictsAfterRestart = " + noOfConflictsAfterRestart)

        ii = 0

        while (ii < length) {

          val absEli = toAbsEli(UNSAFE.getInt(involvedNogoodAddr + (ii << 2)))

          bumpUpEVSIDSscoreOfAbsEli(absEli, bump)

          ii += 1

        }

        bump

      } else
        -1f

    }


    @inline def setupWatchReduciblesForExtReducibles345(newNogoodReducible: NogoodReducible): Unit = {

      //printInfoAboutReducible(newNogoodReducible)

      var eliIndexInNogood = 0

      val s = getNogoodSizeFromReducible(newNogoodReducible)

      while (eliIndexInNogood < s) {

        val eliInNogood = getEliFromNogoodInReducible(newNogoodReducible, eliIndexInNogood)

        val reduciblesWithEliInNewNogood: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eliInNogood))

        reduciblesWithEliInNewNogood.addReducibleUS(newNogoodReducible)

        eliIndexInNogood += 1

      }

    }

    var triviallyUNSAT = false  // true if there is an empty clause

    // We add the "clark nogoods" (=nogoods which originate directly from DIMACS or ASPIF) to their reducible lists (akin watch lists):

    nii = 0

    while (nii < clarkNogoodsFinal.length) { // (observe that we couldn't store the clark part centralized (for all SAT solver threads)
      // since solver thread might manipulate the content of reducibles (depending on BCP method, see extReducibles)

      // We initialize the reducibles lists (watch lists):

        // TODO: use regular addNogoodReducible... method for adding to reducible lists?

        //println("clarkNogoodsFinal(nii).size = " + clarkNogoodsFinal(nii).size)

        if (clarkNogoodsFinal(nii).size == 0 || triviallyUNSAT) {

          triviallyUNSAT = true  // Important: we must later not enter the SAT solver loop, as it cannot work with empty nogoods

          nogiClarkToNogoodReducible.update(nii, null.asInstanceOf[NogoodReducible])

          if(debug2) println("\ntriviallyUNSAT!\n")

        } else {

          val reducible: NogoodReducible = generateNogoodReducibleFromNogoodClarkOrSpecial(
            nogoodAddr = clarkNogoodsFinal(nii).getAddr, nogoodSize = clarkNogoodsFinal(nii).sizev,
            beforeSolvingstarted = true)

          if (debug2)
            printInfoAboutReducible(reducible)

          nogiClarkToNogoodReducible.update(nii, reducible)

          if (allowEliToClarkReduciblesLookup) {

            var eliInNogoodI = 0

            val s = getNogoodSizeFromReducible(reducible)

            while (eliInNogoodI < s) {

              val eliInNogood = getEliFromNogoodInReducible(reducible, eliInNogoodI)

              eliToReduciblesClark(eliToJavaArrayIndex(eliInNogood)).addReducibleUS(reducible /*, incIfOverflow = initListsIncIfOverflow*/)

              eliInNogoodI += 1

            }

        }

        if(getNogoodSizeFromReducible(reducible) > 0) { // check required since we might encounter triviallyUNSAT later in the loop

        if (extReducibles == 1) {

          val hd = getIntFromReducible(reducible, 3)

          if (hd != 0) {

            eliWatchedToReducibles(eliToJavaArrayIndex(hd)).addReducibleUS(reducible)

          }

          if (getNogoodSizeFromReducible(reducible) > 1) {

            val tl = getIntFromReducible(reducible, 4)

            if (tl != 0) {

              eliWatchedToReducibles(eliToJavaArrayIndex(tl)).addReducibleUS(reducible /*, incIfOverflow = initListsIncIfOverflow*/)

            }

          }

        } else if (extReducibles == 4 || extReducibles == 5 || extReducibles == 3) {

          setupWatchReduciblesForExtReducibles345(reducible)

        } else if (extReducibles == 2) {

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(reducible, 0))).addReducibleUS(reducible)

          if (getNogoodSizeFromReducible(reducible) > 1) {

            eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(reducible, 1))).addReducibleUS(reducible)

          }

        } else if (extReducibles == 0) {

          val hd = getEliFromNogoodInReducible(reducible, 0)

          if (extraChecks) assert(isNotAbsSetInPass(hd))

          eliWatchedToReducibles(eliToJavaArrayIndex(hd)).addReducibleUS(reducible)

          if (getNogoodSizeFromReducible(reducible) > 1) {

            val tl = getEliFromNogoodInReducible(reducible, 1)

            if (extraChecks) assert(isNotAbsSetInPass(tl))

            eliWatchedToReducibles(eliToJavaArrayIndex(tl)).addReducibleUS(reducible)

          }

        }

        }

      }

      nii += 1

    }

    @inline def initializePhaseMemo(inverse: Boolean) = { // 0x00: literal absEli is true, !=0x00: literal -absEli is true
      // The initial phasePrevious values can make a huge difference, but hard to predict which value is best

      lazy val rndPhInit = if (rngLocal.nextBoolean()) 0x01.toByte else 0x00.toByte

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        val initPhase = if (initialPhaseMemo == 4) { // Jeroslow-Wang (approximation) (TODO: optimize implementation)

          val posOccReducibles: NogoodReduciblesSequenceUnsafe = if (allowEliToClarkReduciblesLookup) eliToReduciblesClark(eliToJavaArrayIndex(absEli)) else eliWatchedToReducibles(eliToJavaArrayIndex(absEli))

          val nti = negatePosEli(absEli)

          val negOccReducibles: NogoodReduciblesSequenceUnsafe = if (allowEliToClarkReduciblesLookup) eliToReduciblesClark(eliToJavaArrayIndex(nti)) else eliWatchedToReducibles(eliToJavaArrayIndex(nti))

          @inline def w(reducibles: NogoodReduciblesSequenceUnsafe): Float = {

            var s = 0f

            var k = 1

            while (k <= 16 /*256*/ ) { // TODO: optimize:

              val noOfKNogoodsInReducibles = reducibles.filterByReducibleUS((reducible: NogoodReducible) => getNogoodSizeFromReducible(reducible) == k).size

              s += noOfKNogoodsInReducibles.toFloat / Math.pow(2, k).toFloat

              k += 1

            }

            s

          }

          val r = w(posOccReducibles) >= /*<*/ w(negOccReducibles) // TODO: check; we are working with nogoods, not clauses

          //println(r)

          if (r) 0x01.toByte else 0x00.toByte

        } else if (initialPhaseMemo == 0)
          0x00.toByte
        else if (initialPhaseMemo == 1)
          0x01.toByte
        else if (initialPhaseMemo == 5)
          (if (rngLocal.nextBoolean()) 0x01.toByte else 0x00.toByte)
        else if (initialPhaseMemo == 6)
          rndPhInit
        else if(initialPhaseMemo == 2 || initialPhaseMemo == 3) {

          assert(allowEliToClarkReduciblesLookup)  // kind of works with false too but doesn't make much sense

          val noPosInNogoods = if (!allowEliToClarkReduciblesLookup) eliWatchedToReducibles(eliToJavaArrayIndex(absEli)).size
          else
            eliToReduciblesClark(eliToJavaArrayIndex(absEli)).size + eliWatchedToReducibles(eliToJavaArrayIndex(absEli)).size

          val nti = negatePosEli(absEli)

          val noNegInNogoods = if (!allowEliToClarkReduciblesLookup) eliWatchedToReducibles(eliToJavaArrayIndex(nti)).size
          else eliToReduciblesClark(eliToJavaArrayIndex(nti)).size + eliWatchedToReducibles(eliToJavaArrayIndex(nti)).size

          if (initialPhaseMemo == 2)
            if (noPosInNogoods > noNegInNogoods) 0x00.toByte else 0x01.toByte
          else if (noPosInNogoods < noNegInNogoods) 0x00.toByte else 0x01.toByte

        } else {

          stomp(-5009, "Invalid initialPhaseMemo value")

          0x00.toByte

        }

        updateInPhasePreviousForAbsElis(absEli,
          if (!inverse) initPhase else if (initPhase == 0x00.toByte) 0x01.toByte else 0x00.toByte)

        absEli += 1

      }

    }

    initializePhaseMemo(inverse = false)  // TODO: move before method declarations

    @inline def addToUnassignedAbsEliSet(absEli: Eli) = {

      unassignedAbsEliSet.addSorted(absEli)

    }

    @inline def addToUnassignedAbsEliBinSet(absEli: Eli) = {

      val bin = getBinFromScoreForFreeEliSearchApproach15(getAbsEliScore(absEli))

      //println("Adding " + absEli + " to bin " + bin)

      //assert(!unassignedAbsEliBinSet(bin).contains(absEli))

      unassignedAbsEliBinSet(bin).add(absEli)

      //assert(unassignedAbsEliBinSet(bin).contains(absEli))

    }

    @inline def removeFromUnassignedAbsEliBinSet(absEli: Eli): Unit = {

      val bin = getBinFromScoreForFreeEliSearchApproach15(getAbsEliScore(absEli))

      //println("Removing " + absEli + " from bin " + bin)

      //assert(unassignedAbsEliBinSet(bin).contains(absEli))

      unassignedAbsEliBinSet(bin).remove(absEli)

      //assert(!unassignedAbsEliBinSet(bin).contains(absEli))

    }

    @inline def initializeUnassignedScoredAbsElisSetOrPriorityQueue(beforeSolving: Boolean): Unit = {

      assert(freeEliSearchApproach11or14or15)

      assert(freeEliSearchApproach != 11 || unassignedScoredAbsElisPriorityQueue.isEmpty)

      assert(freeEliSearchApproach != 14 || unassignedAbsEliSet.isEmpty)

      var absEli = 1

      while (absEli <= noOfAbsElis) {

        val orderOfAbsEli = absElisSeqArranged.get(absEli - 1)

        setScoreOfAbsEli(absEli, absElisScoringPreservationFactorFromInit / orderOfAbsEli.toFloat, updateInHeap = false) // i.e., we use 1/position (scaled) in the
        // initial arrangement (see initAbsElisArrangement) as initial score (will be overridden of course,
        // but can have a significant - yet normally unpredictable - impact).

        if (freeEliSearchApproach == 15) {

          if (beforeSolving) {

            val bin = getBinFromScoreForFreeEliSearchApproach15(getAbsEliScore(absEli))

            unassignedAbsEliBinSet(bin).add(absEli)

          }

        } else if (freeEliSearchApproach == 14) {

          if (beforeSolving)
            unassignedAbsEliSet.addSorted(absEli)

        } else {

          if (beforeSolving)
            unassignedScoredAbsElisPriorityQueue.enqueue(absEli)
          else if (unassignedScoredAbsElisPriorityQueue.contains(absEli))
            unassignedScoredAbsElisPriorityQueue.changed(absEli)

        }

        absEli += 1

      }

    }

    if (freeEliSearchApproach11or14or15)
      initializeUnassignedScoredAbsElisSetOrPriorityQueue(beforeSolving = true)  // TODO: move before method decls

    @inline def possiblyRescaleAllAbsElis: Unit = {

      if (!neverRescaleAbsEliScores && (scheduleRescaleAbsElis || noOfConflictsTotal % enforceRescalingOfAbsEliScoresEvery == 0)) {

        rescalingsAbsEliScores += 1

        if (scheduleRescaleAbsElis)
          scheduleRescaleAbsElis = false

        if (freeEliSearchApproach == 11)
          unassignedScoredAbsElisPriorityQueue.clear()
        else if (freeEliSearchApproach == 15) {

          var i = 0

          while (i < unassignedAbsEliBinSet.length) {

            unassignedAbsEliBinSet(i).clear()

            i += 1

          }

        } else if (freeEliSearchApproach == 14)
          unassignedAbsEliSet.clear()

        var absEli = 1

        while (absEli <= noOfAbsElis) {

          val rescaledScore = getAbsEliScore(absEli) / 1e35f // NB: this may change positive scores to 0

          setScoreOfAbsEli(absEli, rescaledScore)

          if (isNotAbsSetInPass(absEli)) {

            if (freeEliSearchApproach == 11)
              unassignedScoredAbsElisPriorityQueue.enqueue(absEli)
            else if (freeEliSearchApproach == 14)
              unassignedAbsEliSet.addSorted(absEli)
            else if (freeEliSearchApproach == 15) {

              val bin = getBinFromScoreForFreeEliSearchApproach15(getAbsEliScore(absEli))

              unassignedAbsEliBinSet(bin).add(absEli)

            }

          }

          absEli += 1

        }

      }

    }

    @deprecated
    @inline def setInPassAfterSolvePhase(eli: Eli): Unit = { // this and setInPassIfUnassigned must be the only ways (besides initialization) of assigning True to an eli.
      // ^to be called only(!) after a complete assignment candidate has been found!

      assert(false) // works but not needed anymore

      //assert(!isAbsSetInPass(eli))  // must hold when calling this function!
      //assert(orderNo > 0)

      assert(isNotSetInPass(negateEli(eli))) // if this fails, first check that the branching eli and its negation are both unset after
      // findDecisionEli.
      // Another possible failure reason: if setting an eli in pass doesn't immediately reduce the nogood reducibles with that eli.
      //
      // (Remark: it's temporarily possible that both eli and its negation are set, when a conflict has stopped propagation of unit elis
      // (so that eli had been fired but not all set to "set" in all affected nogoods, so that neg(eli) could still fire). However,
      // in that case jumping back after the conflict unsets eli.)

      setInPass(eli)

      updateAbsEliToDl(toAbsEli(eli), dl)

      orderNumber += 1

    }


    @inline def setInPassIfUnassigned(eli: Eli): Boolean = { // ===> !! This and setInPassEntry and setInPassAfterSolvePhase must be the only ways of assigning True to an eli.

      if (isNotSetInPass(eli)) {

        setInPassEntry(eli)

        true

      } else // this legitimately can happen with certain BCP approaches
        false

    }

  @inline def setInPassEntry(eli: Eli): Unit = { // ===> !! This and setInPassIfUnassigned and setInPassAfterSolvePhase must be the only ways of assigning True to an eli.

    /*if (isNotSetInPass(eli))*/ {

      assert(isNotSetInPass(negateEli(eli)), eli + " (currently unset) about to be set but " + negateEli(eli) + " already set")

      setInPass(eli)

      val absEli = toAbsEli(eli)

      updateAbsEliToDl(absEli, dl)

      if (debug2) println("Set in pass: eli = *" + eli + "* on decLevel: " + decisionLevelOfEli(eli) + ", orderNumber = " + orderNumber)

      if (absEliScoringApproach == 2) {

        updateLastConflictOfAbsEli(absEli, getNoOfConflictsForERWA)

        updateParticipatedAbsEli(absEli, 0)

        if (includeReasonedCountsInAbsEliScoringApproach2)
          updateReasonedAbsEli(absEli, 0)

      }

      if (freeEliSearchApproach == 15)
        removeFromUnassignedAbsEliBinSet(absEli)
      else if (freeEliSearchApproach == 14) {

        unassignedAbsEliSet.removeSorted(absEli)

      } else if (freeEliSearchApproach == 11)
        unassignedScoredAbsElisPriorityQueue.remove(absEli)
      else if (freeEliSearchApproach == 9)
        unassignedScoredAbsEliTreeSet.remove(absEli)

      orderNumber += 1

    }

  }

    @inline def clearInPass(eli: Eli, calledWhen: Eli = 0 /*0: during conflict jumpback, 1: during restart,
      2: before solving*/): Unit = { // ====> !! This method must be the only way (after preprocessing/initialization) of assigning False to an eli.

      // TODO: optimize further (use info from caller about isPosEli etc)

      if (calledWhen <= 1) {

        if (debug2) println("Unsetting eli in pass: *" + eli + "*")

        assert(isSetInPass(eli))

        if (absEliScoringApproach == 2) { // here the absEli scores are Q-values whereas the values bumped up in conflict analysis
          // are the participation frequencies (...ParticipatedAbsEli)

          val absEli = toAbsEli(eli)

          if (calledWhen != 1) {

            val interval = getNoOfConflictsForERWA - getLastConflictOfAbsEli(absEli)

            val reward: Float = getParticipatedAbsEli(absEli).toFloat / interval.toFloat

            val rsr: Float = if (includeReasonedCountsInAbsEliScoringApproach2)
              getReasonedAbsEli(absEli).toFloat / interval.toFloat
            else
              0f

            val newQValue = (1f - alpha) * getAbsEliScore(absEli) + alpha * (reward + rsr)

            setScoreOfAbsEli(absEli, newQValue)

          }

        }

        if (isPosEli(eli)) {

          if (updatePhaseMemo) {

            updateInPhasePreviousForAbsElis(eli, 0x01.toByte)

          }

          if (freeEliSearchApproach == 15)
            addToUnassignedAbsEliBinSet(eli)
          else if (freeEliSearchApproach == 11)
            unassignedScoredAbsElisPriorityQueue.enqueue(eli)
          else if (freeEliSearchApproach == 14)
            addToUnassignedAbsEliSet(eli)
          else if (freeEliSearchApproach == 9)
            unassignedScoredAbsEliTreeSet.add(eli)

        } else {

          if (updatePhaseMemo) {

            updateInPhasePreviousForAbsElis(negateNegEli(eli), 0x00.toByte)

          }

          if (freeEliSearchApproach == 15)
            addToUnassignedAbsEliBinSet(negateNegEli(eli))
          else if (freeEliSearchApproach == 14)
            addToUnassignedAbsEliSet(negateNegEli(eli))
          else if (freeEliSearchApproach == 11)
            unassignedScoredAbsElisPriorityQueue.enqueue(negateNegEli(eli))
          else if (freeEliSearchApproach == 9)
            unassignedScoredAbsEliTreeSet.add(negateNegEli(eli))

        }

      }

      unassignInPass(eli)

      orderNumber -= 1

    }

    @scala.annotation.tailrec
    @inline final def setEliWithNogoodUpdatesNoHeapForExtRed1b(): Unit = {
      // Don't enter this method directly to set a single eli

      val rmiStorePosMax = rmiStorePos

      ri = rmiStorePosOld

      while (ri < rmiStorePosMax) {

        val eli = rmiStoreG.get(ri)

        if (debug2) println("\nAttempting to set " + eli + "...")

        if (setInPassIfUnassigned(eli)) {

          rmiStoreG.update(orderNumber - 1, eli) // necessary because the elis which are pushed for propagation on rmiStoreG
          // are not necessarily newly set to true in pass (as they might be true already), so we need to make sure that
          // the rmiStoreG (which is also used for clearing and conflict analysis) is "gapless" and represents
          // the actualy trail from index 1 up to index orderNumber-1.

          if (debug2)
            println("+++ Going through watch list for eli " + eli + "...")

          updateReasonOfEli(eli, reasonsForRmiStoreForNoHeap.get(ri)) //reasonOfEli.updateMid(eli, reasonsForRmiStoreForNoHeap.get(ri))

          //rmiStorePosOld = rmiStorePos

          val redList = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

          var rj = redList.size - 1 // NB: we must traverse from last to first

          while (rj >= 0) {

            val red: NogoodReducible = redList.getReducibleUS(rj)

              if (debug2) printInfoAboutReducible(red)

              val rmi = setItemIndicExt1(red, eli)

              if (rmi == 0) {

                violatedNogoodReducible = red

                eliWatchedToReducibles(eliToJavaArrayIndex(eli)).cutoffUS(rj) // that we clear the reducibles list in this bulk fashion
                // is the main difference compared to the approach extReducibles=0 (the price we pay is the need for eliToReduciblesDeficitResto)
                // Also observe the differences to the Minisat-style approach with extReducibles=2.

                return

              } else if (rmi != Int.MaxValue) {

                if (rmiStorePos >= maxBCPPush)
                  stomp(-5013, "Memory overflow, please increase maxBCPPushInit")

                rmiStoreG.update(rmiStorePos, negateEli(rmi))

                reasonsForRmiStoreForNoHeap.update(rmiStorePos, red)

                if (debug2) println("Scheduled " + negateEli(rmi) + " for propagation")

                rmiStorePos += 1

              }

            rj -= 1

          }

          eliWatchedToReducibles(eliToJavaArrayIndex(eli)).clearUS() // that we clear the reducibles list in this bulk fashion
          // is the main difference compared to the approach extReducibles=0 (the price we pay is the need for eliToReduciblesDeficitResto)

        }

        ri += 1

      }

      rmiStorePosOld = rmiStorePosMax

      if (rmiStorePos > rmiStorePosMax)
        setEliWithNogoodUpdatesNoHeapForExtRed1b()

    }


    @inline def setEliWithNogoodUpdatesNoHeapForExtRed2b(): Unit = {

      assert(extReducibles == 2)

      var riAddr = rmiStoreG.getAddr + (rmiStorePosOld << 2)

      var endRiAddr = rmiStoreG.getAddr + (rmiStorePos << 2)

      while (riAddr < endRiAddr ) {

        val eli = UNSAFE.getInt(riAddr)

        { // observe that setInPassIfUnassigned also modified rmiStoreG

          if (debug2) println("going through reducibles with eli " + eli + "...")

          val redList: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

          var rjAddr = redList.getAddrOfItem(redList.size - 1) // redList.getAddr

          while (rjAddr >= redList.getAddr) {

            val red: NogoodReducible = UNSAFE.getLong(rjAddr)

            /*blocker eli (see NogoodReduciblesSequenceUnsafe): if(!isNegSetInPass(UNSAFE.getInt(addrOfItemInRedList + 8l))) {*/ //{ //rrr

              val rmi = setItemIndicExt2(red, eli, redList, rjAddr)

              if (rmi == 0) { // conflict

                violatedNogoodReducible = red

                if (debug2) println("    conflict from setItemIndicExt2: " + red)

                /*  Doesn't work anymore since traversing from start:
                // Optional: We move the violated nogood closer to the end of the list in the hope that
                // this will lead to an earlier conflict detection the next time this list is traversed:

                val swapPos = redList.size - swapOffset // (observe that redList.size might decrease also)

                if (rj < swapPos) {

                  redList.swap(rj, swapPos, red)

                 // swapOffset += 1

                }*/

                rmiStorePos = ((endRiAddr - rmiStoreG.getAddr) >> 2).toInt

                return

              } else if (rmi < Int.MaxValue-1) { // unit resulting nogood:

                if (rmiStorePos >= maxBCPPush)
                  stomp(-5013, "Memory overflow, please increase maxBCPPushInit")

                UNSAFE.putInt(endRiAddr, negateEli(rmi))

                updateReasonOfEli(toAbsEli(rmi), red) //FLL

                setInPassEntry(negateEli(rmi))

                endRiAddr += 4l

                /* Doesn't work anymore since traversing from start:
                // Optional: We move the unit resulting nogood closer to the end of the list in the hope that
                // this will lead to an earlier conflict detection the next time this list is traversed:

                val swapPos = redList.size - swapOffset // (observe that redList.size might decrease also)

                if (rj < swapPos) {

                  redList.swap(rj, swapPos, red)

                  swapOffset += 1

                }*/

                //rjAddr += redList.getBytesPerElement //rj += 1

              }

              rjAddr -= redList.getBytesPerElement

          }

        }

        riAddr += 4l

      }

      rmiStorePos = ((endRiAddr - rmiStoreG.getAddr) >> 2).toInt

      rmiStorePosOld = rmiStorePos

    }

    @scala.annotation.tailrec
    @inline final def setEliWithNogoodUpdatesNoHeapForExtRed5(/*eli: Eli, reason: NogoodReducible /*must be 0l if eli is a branching literal*/ */
                                                        recursionDepth: Eli = 0): Unit = {
      //assert(extReducibles == 5)

      val rmiStorePosMax = rmiStorePos

      ri = rmiStorePosOld

      while (ri < rmiStorePosMax) {

        val eli = rmiStoreG.get(ri)

        if (debug2) println("Attempting to set eli " + eli + "...")

        if (violatedNogoodReducible == 0l && setInPassIfUnassigned(eli)) { // observe that setInPassIfUnassigned also modified rmiStoreG

          rmiStoreG.update(orderNumber - 1, eli) // necessary because the elis which are pushed for propagation on rmiStoreG
          // are not necessarily newly set to true in pass (as they might be true already), so we need to make sure that
          // the rmiStoreG (which is also used for clearing and conflict analysis) is "gapless" and represents
          // the actualy trail from index 1 up to index orderNumber-1.

          if (debug2) println("Setting reason for propagated eli " + eli + " to " + reasonsForRmiStoreForNoHeap.get(ri))

          updateReasonOfEli(eli, reasonsForRmiStoreForNoHeap.get(ri))

          val redList = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

          if (redList.size > 0) {

            var rj = redList.size - 1

            do {

              val red: NogoodReducible = redList.getReducibleUS(rj)

              if (getLongFromReducible(red, intIndex = 2) != 0l) {

                val newProduct = getLongFromReducible(red, intIndex = 2) / eli

                val noOfUnsetElisInNogood = setProductForExt5(red, newProduct)

                if (noOfUnsetElisInNogood == 0) { // conflict

                  if (violatedNogoodReducible == 0l /*|| // not useful(?) =>
                      getNogoodReducibleScore(red, 7) >
                        getNogoodReducibleScore(violatedNogoodReducible, 7) */ )
                  violatedNogoodReducible = red

                  //  return  // nope, since this would result in only incompletely updated unset length values in the reducibles

                } else if (noOfUnsetElisInNogood == 1 && violatedNogoodReducible == 0l) { // nogood is unit resulting

                  if (rmiStorePos >= maxBCPPush)
                    stomp(-10000, "Memory overflow. Increase maxBCPPush")

                  rmiStoreG.update(rmiStorePos, negateEli(newProduct.toInt))

                  reasonsForRmiStoreForNoHeap.update(rmiStorePos, red)

                  if (debug2) println("Scheduled eli " + newProduct.toInt + " for propagation")

                  rmiStorePos += 1

                }

              } else {

                val (noOfUnsetElisInNogood, isNotZeroNewLongValueInBitSet) = unsetBitInReducibleBitsetExt3(red, eli)
                // Observe that the UNset(!) bits in the bitset represent set(!) elis, and vice versa

                if (noOfUnsetElisInNogood == 0) { // conflict

                  if (violatedNogoodReducible == 0l)
                  violatedNogoodReducible = red

                  //  return  // nope, since this would result in only incompletely updated unset length values in the reducibles

                } else if (noOfUnsetElisInNogood == 1 && violatedNogoodReducible == 0l) { // nogood is unit resulting

                  val unitResEli: Eli = if (isNotZeroNewLongValueInBitSet)
                    findEliInUnitReducibleBitsetExt3(red, eli)
                  else
                    findEliInUnitReducibleBitsetExt3(red)

                  if (rmiStorePos >= maxBCPPush)
                    stomp(-10000, "Memory overflow. Increase maxBCPPush")

                  rmiStoreG.update(rmiStorePos, negateEli(unitResEli))

                  reasonsForRmiStoreForNoHeap.update(rmiStorePos, red)

                  if (debug2) println("Scheduled eli " + unitResEli + " for propagation")

                  rmiStorePos += 1

                }

              }

              rj -= 1

            } while (rj >= 0)

          }

        }

        ri += 1

      }

      rmiStorePosOld = rmiStorePosMax

      if (violatedNogoodReducible == 0l && rmiStorePos > rmiStorePosMax)
        setEliWithNogoodUpdatesNoHeapForExtRed5()

    }

    @inline def setEliWithNogoodUpdatesNoHeap(eli: Eli/*either a decision eli or a neg(sigmaEli)*/,
                                              reason: NogoodReducible /*must be 0l if branching eli*/): Unit = {

      rmiStorePos = orderNumber

      rmiStorePosOld = rmiStorePos

      rmiStoreG.update(rmiStorePos, eli)

      if (absEliScoringApproach == 1)
        playStackStartOrderNumber = rmiStorePos

      if (extReducibles == 2) {

        updateReasonOfEli(toAbsEli(eli), reason)

        rmiStorePos += 1

        assert(isNotAbsSetInPass(eli))

        setInPassEntry(eli)

        setEliWithNogoodUpdatesNoHeapForExtRed2b()

      } else {

        reasonsForRmiStoreForNoHeap.update(rmiStorePos, reason)

        rmiStorePos += 1

        if (extReducibles == 1)
          setEliWithNogoodUpdatesNoHeapForExtRed1b()
        else if (extReducibles == 5)
          setEliWithNogoodUpdatesNoHeapForExtRed5()
        /*else if (extReducibles == 2)
          ... // remark: there is no genuine reason why extReducible=2 couldn't work with the BCP algo style
        // using reasonsForRmiStoreForNoHeap, the adaptation would be trivial (but likely not useful)
        */ else
          stomp(-5009, "extReducibles=" + extReducibles + " is not a valid option")

      }

    }

  @inline def nopropSetEliWithNogoodUpdatesNoHeap(eli: Eli): Unit = {

    rmiStorePos = orderNumber

    rmiStoreG.update(rmiStorePos, eli)

    if (absEliScoringApproach == 1)
      playStackStartOrderNumber = rmiStorePos

    if (extReducibles == 2) {

      rmiStorePos += 1

      setInPassIfUnassigned(eli)

      if(false) {

      val redList: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

      var rj = redList.size - 1

      var swapOffset = 1

      while (rj >= 0) { // Must go from end to start (because of the way we delete reducibles from the list)

        val addr = redList.getReducibleUS(rj)

        /*blocker eli (see NogoodReduciblesSequenceUnsafe): if(!isNegSetInPass(UNSAFE.getInt(addrOfItemInRedList + 8l))) {*/
        if(isClarkReducible(addr)) {

          {

              val nogoodSize = getNogoodSizeFromReducible(addr)

              if (nogoodSize == 1) {

                { // conflict

                  violatedNogoodReducible = addr

                  return

                }

              } else if (nogoodSize == 2) {

                val e0 = getEliFromNogoodInReducible(addr, 0)

                if (eli == e0) {

                  val e1 = getEliFromNogoodInReducible(addr, 1)

                  if (isSetInPass(e1)) { // conflict

                    violatedNogoodReducible = addr

                    return

                  }


                } else {

                  if (isSetInPass(e0)) { // conflict

                    violatedNogoodReducible = addr

                    return

                  }

                }

              } else if (nogoodSize == 3) {

                val e0 = getEliFromNogoodInReducible(addr, 0)

                if (eli == e0) {  // pivot = 0, other = 1

                  val possUnitEli = getEliFromNogoodInReducible(addr, 1)

                  if (!isNegSetInPass(possUnitEli)) {

                    val u = getEliFromNogoodInReducible(addr, 2)

                    if (isNotSetInPass(u)) {

                      redList.removeByIndexUS(rj)

                      updateEliInNogoodInReducible(addr, 0, u)

                      updateEliInNogoodInReducible(addr, 2, eli)

                      eliWatchedToReducibles(eliToJavaArrayIndex(u)).addReducibleUS(addr)

                    } else {

                      if (isSetInPass(possUnitEli)) // conflict
                        { // conflict

                          violatedNogoodReducible = addr

                          return

                        }

                    }

                  }

                } else {  // pivot = 1, other = 0

                  val possUnitEli = e0

                  if (!isNegSetInPass(possUnitEli)) {

                    val u = getEliFromNogoodInReducible(addr, 2)

                    if (isNotSetInPass(u)) {

                      redList.removeByIndexUS(rj)

                      updateEliInNogoodInReducible(addr, 1, u)

                      updateEliInNogoodInReducible(addr, 2, eli)

                      eliWatchedToReducibles(eliToJavaArrayIndex(u)).addReducibleUS(addr)

                    } else {

                      if (isSetInPass(possUnitEli)) // conflict
                        { // conflict

                          violatedNogoodReducible = addr

                          return

                        }

                    }

                  }

                }

              } else {

                @inline def acts(pivotIndex: Eli, /*otherIndex: Int*/possUnitEli: Eli): Eli = { // the most time consuming method in delSAT's SAT core

                  if (isNegSetInPass(possUnitEli)) { // nogood cannot be true => nothing to do

                    Int.MaxValue

                  } else {

                    val firstAddr = addr + (offsetIntsOfNogoodInReducible << 2) + 8l // = address of literal_2 in nogood (literals _0 and _1 are the watches)

                    var addri = firstAddr

                    while (isSetInPass(UNSAFE.getInt(addri))) { // to make this loop terminate, there must be an end marker "literal"
                      // 0 after the last literal for which isSetInPass returns false (which requires that vPass(0) != 0).

                      addri += 4l

                    }

                    if (addri < firstAddr + ((nogoodSize - 2) << 2)) {

                      val u = UNSAFE.getInt(addri)

                        redList.removeByIndexUS(rj)

                        updateEliInNogoodInReducible(addr, pivotIndex, u)

                        UNSAFE.putInt(addri, eli)

                        eliWatchedToReducibles(eliToJavaArrayIndex(u)).addReducibleUS(addr)

                      if (debug2) println("  action 2: moved reducible to list of eli " + u)

                      // updateLongInReducible(addr, intIndex = 1, addri)  // updates search start for next tome. If activated,
                      // must also activate the if(false)... branch below

                      Int.MaxValue

                    } else {

                      {

                        if (isSetInPass(possUnitEli)) // conflict
                        0 // Remark: this is different from Minisat 1 where conflicts are discovered by a pos/neg literal clash,
                          // but alike Minisat 2
                          else { // Unit resulting

                          // now we know that all but one eli are true and the remaining eli is unassigned

                          if (debug2) println("  action 3: unit resulting, propagating neg of eli " + possUnitEli)

                          possUnitEli

                        }

                      }

                    }

                  }

                }

                val r = if (eli == getEliFromNogoodInReducible(addr, 0))
                  acts(pivotIndex = 0, /*otherIndex = 1*/getEliFromNogoodInReducible(addr, 1))
                else
                  acts(pivotIndex = 1, /*otherIndex = 0*/getEliFromNogoodInReducible(addr, 0))

                if(r == 0) { // conflict

                  violatedNogoodReducible = addr

                  return

                }

              }


            }

        }

        rj -= 1

      }

    }

    } else
      assert(false)

  }

    @inline def scoreUpd(eli: Eli, bump: Float): Unit = {

      // assert(isSetInPass(eli) || isSetInPass(negateEli(eli)))

      if (absEliScoringApproach == 2)
        incParticipatedAbsEli(toAbsEli(eli))
      else if (absEliScoringApproach == 1)
        updateLastConflictOfAbsEli(toAbsEli(eli), getNoOfConflictsForERWA)
      else if (absEliScoringApproach == 0)
        bumpUpEVSIDSscoreOfAbsEli(toAbsEli(eli), bump)

    }

    /*
    // We used ConflictAnalysisResult to avoid the boxing which comes with Tuple3 return values (but still too expensive)
    case class ConflictAnalysisResult (newDecisionLevel: Int /*new decision level to jump to*/ ,
                                       sigmaEli: Eli /*whose negation we assign next*/ ,
                                       conflictNogoodReducible: NogoodReducible /*the learned reducible (but only with the nogood elis and the nogood size set, rest undefined)*/ )
*/
    var conflictAnalysisResult_newDecisionLevel = 0
    var conflictAnalysisResult_sigmaEli = 0
    var conflictAnalysisResult_conflictNogoodReducible = 0l

    /** Follows largely Minisat 1/2 (Minisat 2 without putting highest decision level literals in nogood position 0 and 1) but
      * using nogoods instead of clauses (so in some places we need to apply/omit negateEli())
      *
      */
    def conflictAnalysis(violatedNogoodReducible: NogoodReducible,
                         outSpaceInitial: NogoodReducible, newReducibleInitialSpaceSlotSize: Eli): Unit /*ConflictAnalysisResult*/
    = {

      // if (debug2)
      //  println("\nConflict analysis... conflicting nogood (reducible " + violatedNogoodReducible + ") = " + generateNogoodFromReducible(violatedNogoodReducible).toArray.mkString(","))

      val absEliBump = updScoreInNgElis(getAddrOfNogoodInReducible(violatedNogoodReducible), getNogoodSizeFromReducible(violatedNogoodReducible))

      conflictAnalysisResult_conflictNogoodReducible = outSpaceInitial

      var newReducibleSpaceSlotSize = newReducibleInitialSpaceSlotSize

      var maxOutSize = newReducibleSpaceSlotSize - offsetIntsOfNogoodInReducible - closingIntsAfterNogoodInReducible // number of Ints
      // available to store the literals of the nogood

      conflictAnalysisResult_newDecisionLevel = 0

      var confl = violatedNogoodReducible

      var outSize = 1

      var index = orderNumber - 1

      var indexOfHighestDl = -1

      conflictAnalysisResult_sigmaEli = 0

      var pathC = 0

      val trail = rmiStoreG // TODO: rename rmiStoreG to "trail"

      do {

        if(confl == 0l)  // important consistency check
          stomp(-10000, "confl == 0l")

        if (!isClarkReducible(violatedNogoodReducible) && scoringForRemovalOfLearnedNogoods == 1 || scoringForRemovalOfLearnedNogoods == 10 || scoringForRemovalOfLearnedNogoods == 11)
          bumpNogoodReducibleActivity(confl)

        var j = 0

        while (j < getNogoodSizeFromReducible(confl)) {

          val q = negateEli(getEliFromNogoodInReducible(confl, j))

          if (q != conflictAnalysisResult_sigmaEli) {

            if (getFromSeen(toAbsEli(q)) == 0x00.toByte && decisionLevelOfEli(toAbsEli(q)) > 0) {

              updateInSeen(toAbsEli(q), 0x01.toByte)

              if (conflictAnalysisResult_sigmaEli /*<--sic!*/ != 0)
                scoreUpd(q, absEliBump)

              if (decisionLevelOfEli(toAbsEli(q)) == dl) {

                pathC += 1

              } else if (decisionLevelOfEli(toAbsEli(q)) > 0) {

                updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, outSize, negateEli(q))

                if (decisionLevelOfEli(toAbsEli(q)) > conflictAnalysisResult_newDecisionLevel) {

                  conflictAnalysisResult_newDecisionLevel = decisionLevelOfEli(toAbsEli(q))

                  indexOfHighestDl = outSize

                }

                outSize += 1

                if (outSize >= maxOutSize) {

                  val maxOutSizeOld = maxOutSize

                  maxOutSize = maxOutSize << 1

                  val newReducibleSpaceSlotSizeOld = newReducibleSpaceSlotSize

                  newReducibleSpaceSlotSize = offsetIntsOfNogoodInReducible + maxOutSize + closingIntsAfterNogoodInReducible

                  val newRed: NogoodReducible = reserveReducibleSpace(requiredReducibleSpaceSizeInNoOfInts = newReducibleSpaceSlotSize /*offsetIntsOfNogoodInReducible + maxOutSize + offsetIntsOfNogoodInReducible*/)

                  UNSAFE.copyMemory(conflictAnalysisResult_conflictNogoodReducible, newRed, (outSize + offsetIntsOfNogoodInReducible) << 2)

                  if (freeOrReassignDeletedNogoodMemory) {

                    updateIntInReducible(conflictAnalysisResult_conflictNogoodReducible, index = offsetIntsOfNogoodInReducible - 3, newReducibleSpaceSlotSizeOld)

                    makeNogoodSpaceAvailable(conflictAnalysisResult_conflictNogoodReducible)

                  }

                  conflictAnalysisResult_conflictNogoodReducible = newRed

                }

              }

            }

          }

          j += 1

        }

        while (getFromSeen(toAbsEli(trail.get(index))) == 0x00.toByte)
          index -= 1

        conflictAnalysisResult_sigmaEli = trail.get(index)

        confl = getReasonOfEli(toAbsEli(conflictAnalysisResult_sigmaEli))

        updateInSeen(toAbsEli(conflictAnalysisResult_sigmaEli), 0x00.toByte)

        pathC -= 1

      } while (pathC > 0)

      updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, 0, conflictAnalysisResult_sigmaEli)

      scoreUpd(conflictAnalysisResult_sigmaEli, absEliBump)

      /*if (outSize > 1) {  // not needed in delSAT: (but see below for optional similar procedure)

        var max_i = 1

        // Find the first literal assigned at the next-highest level:

        var i = 2

        while (i < outSize) {

          if (decisionLevelOfEli(toAbsEli(getEliFromNogoodInReducible(outSpace, i))) > decisionLevelOfEli(toAbsEli(getEliFromNogoodInReducible(outSpace, max_i))))
            max_i = i

          i += 1

        }

        val pp = negateEli(getEliFromNogoodInReducible(outSpace, max_i))

        updateEliInNogoodInReducible(outSpace, max_i, (getEliFromNogoodInReducible(outSpace, 1)))

        updateEliInNogoodInReducible(outSpace, 1, pp)

        newDecLevel = decisionLevelOfEli(pp)

      } */

      setNogoodSizeInReducible(conflictAnalysisResult_conflictNogoodReducible, outSize)

      reducibleSlotSizeEnlargementsEMA -= reducibleSlotSizeEnlargementsEMA / 500f

      if (newReducibleSpaceSlotSize > newReducibleInitialSpaceSlotSize)
        reducibleSlotSizeEnlargementsEMA += 1f / 500f

      if (conflictNogoodSelfSubsumption) { // as ccmin_mode 1 from Minisat 2. See Sörensson, Een: MiniSat v1.13 – A SAT Solver with Conflict-Clause Minimization

        cloneNogoodInReducibleTo(conflictAnalysisResult_conflictNogoodReducible, targetArrayUnsafeForNogoodInConfA)

        val cng = targetArrayUnsafeForNogoodInConfA

        cng.sizev = outSize

        var removedByOnTheFlySelfSubsumption = 0

        var i = 1

        var j = 1

        while (i < outSize) {

          var x = toAbsEli(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, i))

          val reasonX = getReasonOfEli(x)

          if (reasonX <= 0l) {

            updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, j, getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, i))

            j += 1

          } else {

            var k = 1

            while (k < getNogoodSizeFromReducible(reasonX)) {

              if ( /*cannot use this in lieu of !contains: getFromSeen(toAbsEli(getEliFromNogoodInReducible(reasonX, k))) == 0x00.toByte*/
              !cng.contains(getEliFromNogoodInReducible(reasonX, k)) &&
                decisionLevelOfEli(toAbsEli(getEliFromNogoodInReducible(reasonX, k))) > 0) {

                //updateInSeen(toAbsEli(getEliFromNogoodInReducible(outSpace, j)), 0x00.toByte)
                updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, j, getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, i))

                j += 1

                k = Int.MaxValue

              } else
                k += 1

            }

          }

          i += 1

        }

        removedByOnTheFlySelfSubsumption = i - j

        outSize -= i - j

        // if (removedByOnTheFlySelfSubsumption > 0)
          //println("\nremovedByOnTheFlySelfSubsumption = " + removedByOnTheFlySelfSubsumption + ", outSize = " + outSize)

        setNogoodSizeInReducible(conflictAnalysisResult_conflictNogoodReducible, outSize)

        var k = 0

        while (k < cng.sizev) {

          updateInSeen(toAbsEli(cng.get(k)), 0x00.toByte)

          k += 1

        }

      } else {

        var k = 0

        while (k < outSize) {

          updateInSeen(toAbsEli(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, k)), 0x00.toByte)

          k += 1

        }

      }

      if(moveElisWithHighDecisionLevelToFront) {  //doesn't seem to be useful:

        if (false) {
          // optional - we move the eli eith the highest decision level into the second watch position (nogood[1]):

          if (true) {

            if (conflictNogoodSelfSubsumption) {

              indexOfHighestDl = 1

              var i = 2

              while (i < outSize) {

                if (getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, i) > getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, indexOfHighestDl))
                  indexOfHighestDl = i

                i += 1

              }

            }

            if (indexOfHighestDl > 1) {

              val h = getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, 1)

              updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, 1, getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, indexOfHighestDl))

              updateEliInNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, indexOfHighestDl, h)

            }

          } else {
            /*
                      IntArrayUnsafeS.sortByAtAddr(UNSAFE, getAddrOfNogoodInReducible(outSpace),
                        eliInNogood => {

                          //decisionLevelOfEli(toAbsEli(eliInNogood)).toFloat

                          //-getAbsEliScore(toAbsEli(eliInNogood))

                          if(getFromPhasePreviousForAbsElis(toAbsEli(eliInNogood)) == 0x00.toByte) 1f else 0f
                          // TODO: unclear amortized beneficiality. Beneficial for 4pipe_k, not for, e.g., aes_24_4_keyfind_2-sc2013


                        }, outSize)

            */
          }


        } else {  // alternatively, we can sort the entire nogood:

          IntArrayUnsafeS.sortByInplace(UNSAFE, getAddrOfNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible),
            eliInNogood => {

              val r = -decisionLevelOfEli(toAbsEli(eliInNogood)).toFloat

              r

            }, outSize)

        }

      }

      if (absEliScoringApproach == 2 && includeReasonedCountsInAbsEliScoringApproach2) {

        var iii = 0

        while (iii < outSize) {

          val eliInNogood = getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, iii)

          val reason = getReasonOfEli(eliInNogood)

          if (reason != 0l) {

            var i = 0

            while (i < getNogoodSizeFromReducible(reason)) {

              val eliInReason = getEliFromNogoodInReducible(reason, i)

              if (!nogoodInReducibleContainsAbs(conflictAnalysisResult_conflictNogoodReducible, eliInReason))
                incReasonedAbsEli(toAbsEli(eliInReason))

              i += 1

            }

          }

          iii += 1

        }

      }


      if (useLBD) {

          val lbd = computeLBD(conflictAnalysisResult_conflictNogoodReducible)

          setLBDInReducible(conflictAnalysisResult_conflictNogoodReducible, lbd)

      } else
        updateIntInReducible(conflictAnalysisResult_conflictNogoodReducible, offsetIntsOfNogoodInReducible - 1, 0) // even if no LBDs are used, we must set
        // this to a value >= 0, because this entry is also used to distinguish clark from learned nogoods.

      updateIntInReducible(conflictAnalysisResult_conflictNogoodReducible, index = offsetIntsOfNogoodInReducible - 2, 1 /*<-to avoid NaN*/)

      updateIntInReducible(conflictAnalysisResult_conflictNogoodReducible, index = offsetIntsOfNogoodInReducible - 3, newReducibleSpaceSlotSize)

      setLearnedNogoodReducibleActivity(conflictAnalysisResult_conflictNogoodReducible, 0f)

      if (scoringForRemovalOfLearnedNogoods == 1 || scoringForRemovalOfLearnedNogoods == 10 || scoringForRemovalOfLearnedNogoods == 11)
        bumpNogoodReducibleActivity(conflictAnalysisResult_conflictNogoodReducible) // (observe that the nogood activity bump increases over time)

      totalNoElisInLearnedNogoods += getNogoodSizeFromReducible(conflictAnalysisResult_conflictNogoodReducible)

      //println("Learned nogood: " + generateNogoodFromReducible(outSpace).toArray.mkString(","))

    }

    val noOfConflictsBeforeRestartFact = if (glucoseRestarts)
      restartTriggerConf._3 * -restartsFactModifier
    else
      restartTriggerConf._3 * restartsFactModifier

    var noOfConflictsBeforeRestart: Double = if (restartTriggerConf._1 != 3) restartTriggerConf._2 else noOfConflictsBeforeRestartFact

    if (debug2)
      println("noOfConflictsBeforeRestart = " + noOfConflictsBeforeRestart)

    var noOfConflictsBeforeNextRephasing = rephasePhaseMemoIntervalInit.max(minNoConflictsBeforeFirstRephasing)

    var lubyU = 1

    var lubyV = 1

    var noOfNogoodRemovalPhases: Eli = 0

    var nogoodRemovalAdjustNoOfConflicts: Float = nogoodRemovalAdjustStartNoOfConflicts

    var nogoodRemovalThreshAdjustConflictCount: Eli = nogoodRemovalAdjustNoOfConflicts.toInt

    val reduceScoreOfPassiveAbsElisEvery = next2Pow(8) // determines the downscaling frequency for absEli scores
    // (higher = scale down less often but with larger scaling amount at each scaling event. NB: resacling is very costly,
    // in particular with freeEliSearchApproach == 14)

    val scaleFromUpdSc: Float = Math.pow(updSc, reduceScoreOfPassiveAbsElisEvery.toDouble).toFloat

    var deficientReduciblesForEli: NogoodReduciblesSequenceUnsafe = null.asInstanceOf[NogoodReduciblesSequenceUnsafe]

    @inline def jumpBack(newLevel: Eli /*-1: restart from scratch*/ , trials: Eli): Unit = {

      assert(newLevel < dl)

      if (debug2)
        println("\n\n*** Jumping back to decision level " + newLevel + " from current level " + dl + "...\n")

      possiblyRescaleAllAbsElis // to avoid overflows

      // We remove everything with a decision level > newLevel. NB: Level newLevel itself won't be cleared, new elis are assigned
      // in additions to any which are on level newLevel already.

      violatedNogoodReducible = 0l

      val XXX = false

      @inline def clearForExt01(eli: Eli): Unit = { // also see clearForExt2345!

        //if (deepChecks) assert(!isDummyAbsEli(eli))

        if (extReducibles == 1) {

          deficientReduciblesForEli = eliToReduciblesDeficitResto(eliToJavaArrayIndex(eli)) //if (useNogoodNotsets) eliToNogoodRemainders(eli) else eliToNogoodRemaindersDeficitResto(eli)

          clearInPass(eli, calledWhen = if (newLevel == -1) 1 else 0)

          var i = 0

          while (i < deficientReduciblesForEli.size) {

            unSetItemExt01(deficientReduciblesForEli.getReducibleUS(i), eli)

            i += 1

          }

          deficientReduciblesForEli.clearUS()

        } else if (extReducibles == 0) {

          if (!XXX) {

            clearInPass(eli, calledWhen = if (newLevel == -1) 1 else 0)

            assert(isNotAbsSetInPass(eli))

            updateReasonOfEli(eli, 0l)

            if (debug2)
              println("pass and reason for eli " + eli + " cleared")

          } else {

            assert(false)

            clearInPass(eli, calledWhen = if (newLevel == -1) 1 else 0)

            assert(isNotAbsSetInPass(eli))

          }

        } else
          assert(false)

      }

      /*for useRmiStoreForBacktracking only:*/ val firstOrderNoToClear = -1 // dlToFirstOrder can be Int.MinValue for dlOi=0 (because it's unsure that level 0 contains
      // any elis)

      if (extReducibles == 2 || extReducibles == 5 || extReducibles == 4 || extReducibles == 3) {

        @inline def clearForExt2345(eli: Eli) = {

          //assert(isSetInPass(eli))

          clearInPass(eli, calledWhen = if (newLevel == -1) 1 else 0)

          updateReasonOfEli(eli, 0l)

          if (extReducibles != 2) {

            if (extReducibles == 3) {

              val allReduciblesWithEli: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

              var i = 0

              while (i < allReduciblesWithEli.size) {

                setBitInReducibleBitsetExt3(allReduciblesWithEli.getReducibleUS(i), eli) // we restore the bit for eli
                // (and we also update the unsets length)

                i += 1

              }

            } else if (extReducibles == 5) {

              val allReduciblesWithEli: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

              var i = 0

              while (i < allReduciblesWithEli.size) {

                multiplyByFactorOrSetBitInReducibleBitsetExt5(allReduciblesWithEli.getReducibleUS(i), eli) // we multiple current product with eli
                // (and we also update the unsets length)

                i += 1

              }

            } else if (extReducibles == 4) {

              val allReduciblesWithEli: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eli))

              var i = 0

              while (i < allReduciblesWithEli.size) {

                increaseLengthInReducibleExt4(allReduciblesWithEli.getReducibleUS(i), eli)

                i += 1

              }

            }

          }

        }

        if (debug2) println("in clear, orderNumber = " + orderNumber)

        orderNumber = orderNumber

        var i = orderNumber - 1

        while (i >= 1 /*because the lowest order number is 1, which means the lowest index into rmiStoreG (with
              rmiStoreG.get(orderNumber) is also 1*/ ) {

          val eliToClear = rmiStoreG.get(i)

          var dlCleared = decisionLevelOfEli(eliToClear)

          if (dlCleared > newLevel) {

            //  println("Eli " + eliToClear + " at rmiStore index " + i)

            assert(isSetInPass(eliToClear))

            clearForExt2345(eliToClear)

            i -= 1

          } else
            i = -1

        }

      } else { // for extReducibles 0 and 1

        var i = orderNumber - 1

        while (i >= 1 /*because the lowest order number is 1, which means the lowest index into rmiStoreG (with
              rmiStoreG.get(orderNumber) is also 1*/ ) {

          val eliToClear = rmiStoreG.get(i)

          var dlCleared = decisionLevelOfEli(eliToClear)

          if (dlCleared > newLevel) {

            //  println("Eli " + eliToClear + " at rmiStore index " + i)

            assert(isSetInPass(eliToClear))

            clearForExt01(eliToClear)

            i -= 1

          } else
            i = -1

        }

      }

      if (localityExt && (absEliScoringApproach == 2 || absEliScoringApproach == 1) &&
        fastModByPow2(noOfConflictsTotal, reduceScoreOfPassiveAbsElisEvery) == 0) {

        if (freeEliSearchApproach == 11) {

          val heap = unassignedScoredAbsElisPriorityQueue.getHeap

          var heapI = 0

          while (heapI < unassignedScoredAbsElisPriorityQueue.size) {

            val absEli = heap(heapI)

            setScoreOfAbsEli(absEli, getAbsEliScore(absEli) * scaleFromUpdSc, updateInHeap = false /*since we scale uniformly there is no need to update the heap order*/)

            heapI += 1

          }

        } else if (freeEliSearchApproach == 14) {

          var i = 0

          while (i < unassignedAbsEliSet.size) {

            val absEli = unassignedAbsEliSet.get(i)

            setScoreOfAbsEli(absEli, getAbsEliScore(absEli) * scaleFromUpdSc, updateInHeap = false /*since we scale uniformly there is no need to update the heap order*/)

            i += 1

          }

        } else if (freeEliSearchApproach == 15) {

          var bin = 0

          while (bin < unassignedAbsEliBinSet.length) {

            var i = 0

            while (i < unassignedAbsEliBinSet(bin).size) {

              val absEli = unassignedAbsEliBinSet(bin).get(i)

              setScoreOfAbsEli(absEli, getAbsEliScore(absEli) * scaleFromUpdSc, updateInHeap = true /*here we need the update since the bin of the absEli might change*/)

              i += 1

            }

            bin += 1

          }


        }

      }

      var oldDl = dl

      if (newLevel == -1) { // we restarted from scratch, i.e., including removal of level 0 assignments

        setDecisionLevelTo(0)

      } else {

        setDecisionLevelTo(newLevel)

      }

    }

    /** The exponential moving average of the learnt clauses LBDs */
    @inline def lbdema: Float = /*(emaLBD_fast / 125l).toFloat / */
    /*(emaLBD_slow / 100l).toFloat*/ lbdEmaSlow.toFloat

  @inline def decideDoRegularRestart: Boolean = {

        val f = noOfConflictsBeforeRestart

        val r = noOfConflictsAfterRestart >= f &&
          restartTriggerConf._1 != 0 &&
          (!glucoseRestarts ||
            glucoseRestarts /*-> activates lbdEmaFast/Slow computation*/ &&
              /*emaLBD_fast / 125l > emaLBD_slow / 100l*/ lbdEmaFast > lbdEmaSlow * /*1.25d*/ 1.1d)

        r

    }

    def possibleRephasing(trials: Eli): Boolean /*true: SAT assignment found by SLS (e.g., WalkSAT). Observe that
      SLS currently cannot do any cost minimization, so this is only useful for rephasing or when delSAT is used as a plain SAT solver*/ = {

      // Uses ideas from RSAT and CaDiCaL

      if (noOfConflictsAfterLastRephasing >= noOfConflictsBeforeNextRephasing /*&& noOfConflictsTotal > 500*/ ) {

        if (rephaseLock != null)
          rephaseLock.lock() // observe that the SLS assignment (phasePreviousForAbsElis) is also mutated elsewhere in threads, so blocking just here doesn't synchronize on it everywhere

        noOfRephasings += 1

        noOfConflictsAfterLastRephasing = 0

        val delta = rephasePhaseMemoIntervalInit * (noOfRephasings + 1)

        noOfConflictsBeforeNextRephasing = /*(noOfConflictsBeforeRestart * 3).toInt*/ noOfConflictsTotal / rephasingPhaseMemoIntervalDiv + delta

        if (debug2) println("\nnoOfConflictsBeforeNextRephasing= " + noOfConflictsBeforeNextRephasing)

        val sw = noOfRephasings % 12 // we use a remotely similar modulo scheme as cadical's "unstable + walk" rephasing, but observe
        // that we also rephase by using pos/neg polarity ratio (initialPhase >= 2) and that cadical uses a different Stochastic
        // Local Search solver (probSAT/YalSAT) and rephases at different occasions.

        if (((sw == 1 || sw == 4 || sw == 7 || sw == 10 || (!useSLSinPhaseMemoRephasing && (sw == 2 || sw == 5 || sw == 8 || sw == 11)))) && !bestPhasesQueue.isEmpty) {

          var absEli = 1

          while (absEli <= noOfAbsElis) {

            updateInPhasePreviousForAbsElis(absEli, bestPhasesQueue.front.get(absEli))

            absEli += 1

          }

          if (debug2) println("\nRephased to greedy-best")

        } else if (sw == 6) {

          var absEli = 1

          while (absEli <= noOfAbsElis) {

            updateInPhasePreviousForAbsElis(absEli, if (rngLocal.nextBoolean()) 0x01.toByte else 0x00.toByte)

            absEli += 1

          }

          if (debug2) println("\nRephased to random")

        } else if (sw == 3) {

          var absEli = 1

          while (absEli <= noOfAbsElis) {

            updateInPhasePreviousForAbsElis(absEli, if (getFromPhasePreviousForAbsElis(absEli) == 0x00.toByte) 0x01.toByte else 0x00.toByte)

            absEli += 1

          }

          if (debug2) println("\nRephased by flipping")

        } else if (sw == 0) {

          initializePhaseMemo(inverse = true)

          if (debug2) println("\nRephased by inversion of initial phase")

        } else if (sw == 9) {

          initializePhaseMemo(inverse = false)

          if (debug2) println("\nRephased by reset to initial phase")

        } else if (useSLSinPhaseMemoRephasing && (sw == 2 || sw == 5 || sw == 8 || sw == 11)) {

          if (debug2) println("\nRephasing by Stochastic Local Search (SLS)...")

          val remainingViolatedNogoodsAfterSLS = StochasticLocalSearch.stochasticLocalSearch(singleSolverThreadData = this,
            solverThreadSpecificSettings = singleSolverConf,
            sharedAmongSingleSolverThreads = sharedAmongSingleSolverThreads,
            preparation = prep)

          if (debug2) println("Rephasing by Stochastic Local Search done. remainingViolatedNogoodsAfterSLS = " + remainingViolatedNogoodsAfterSLS)

          noOfRephasingsUsingSLS += 1

          if (remainingViolatedNogoodsAfterSLS == 0 && parameterAtomsElis.length == 0) {
            // SLS found an assignment, so we stop with SAT

            //if (debug)
              println("\nStochastic Local Search (SLS) has found an assignment. Stopping inner SAT solver loop in thread " + threadNo + ".\n")

            dl = 0

            violatedNogoodReducible = 0l

            orderNumber = 1

            while (orderNumber <= noOfAbsElis) {

              if (getFromPhasePreviousForAbsElis(orderNumber) != 0x00.toByte) {

                setInPass(orderNumber)

                unsetInPass(negateEli(orderNumber))

              } else {

                setInPass(negateEli(orderNumber))

                unsetInPass(orderNumber)

              }

              orderNumber += 1

            }

            if (rephaseLock != null)
              rephaseLock.unlock()

            return true

          }

        }

        if(debug && useSLSinPhaseMemoRephasing)
          printStatusLine(" ")  // just to clear any SLS progress line

        if (rephaseLock != null)
          rephaseLock.unlock()

      }

      false

    }

    @deprecated
    @inline def getApproxNoOfLearnedNogoods: Eli = noOfCurrentlyKeptLearnedNogoods

    @inline def isReducibleDeletable(reducible: NogoodReducible, checkByReason: Boolean = true): Boolean = {

      if (!isClarkReducible(reducible) && reducible != violatedNogoodReducible &&
        (nogoodShareNumberMax == 0f || !sharedAmongSingleSolverThreads.nogoodReducibleExchangePool.containsKey(reducible))) {

        //assert(!clarkNogoodReduciblesChecker.contains(reducible))

        if ((!removeLearnedNogoodAtRegularRestarts || reusedTrailRestarts /*<- nope*/ || true) && freeOrReassignDeletedNogoodMemory) {
          // We needed this check to avoid that conflict analysis fails (avoiding materially deleting learned nogoods which are so-called reasons for eli propagations).
          // Alternatively to this check, we can investigate whether the deleted
          // nogood is still required in conflict analysis as a "reason" from unit prop (as in Minisat), see below.

          var k = getNogoodSizeFromReducible(reducible) - 1

          while (k >= 0) {

            if (!checkByReason) {

              if (!isNotAbsSetInPass(getEliFromNogoodInReducible(reducible, k)) &&
                decisionLevelOfEli(getEliFromNogoodInReducible(reducible, k)) <= dl)
                return false

            } else {

              val eliInNogoodToDelete = getEliFromNogoodInReducible(reducible, k)

              if (!isNotAbsSetInPass(getEliFromNogoodInReducible(reducible, k)) &&
                getReasonOfEli(negateEli(eliInNogoodToDelete)) == reducible &&
                decisionLevelOfEli(getEliFromNogoodInReducible(reducible, k)) <= dl) {

                return false

              }

            }

            k -= 1

          }

        }

        true

      } else
        false

    }

    @inline def deleteLearnedNogoodReducible(reducible: NogoodReducible, lazyApproach: Boolean = false): Boolean = {

      if (isReducibleDeletable(reducible, checkByReason = !lazyApproach)) {

        if (!lazyApproach) {

          var i = 0

          while (i < getNogoodSizeFromReducible(reducible)) {

            val eliInNogood = getEliFromNogoodInReducible(reducible, i)

            val reduciblesWithEli: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eliInNogood))

            val indexOfReducible = reduciblesWithEli.findReducibleUS(reducible)

            if (indexOfReducible >= 0)
              reduciblesWithEli.removeByIndexUS(indexOfReducible)

            if (extraChecks)
              assert(reduciblesWithEli.findReducibleUS(reducible) == -1)

            if (extReducibles == 1) {

              val deficientReduciblesForEli = eliToReduciblesDeficitResto(eliToJavaArrayIndex(eliInNogood))

              val indexOfDeficitReducible = deficientReduciblesForEli.findReducibleUS(reducible)

              if (indexOfDeficitReducible >= 0)
                deficientReduciblesForEli.removeByIndexUS(indexOfDeficitReducible)

            }

            i += 1

          }

          if (freeOrReassignDeletedNogoodMemory)
            makeNogoodSpaceAvailable(reducible)

        }

        true

      } else
        false

    }


    val intersect = new NogoodReduciblesSequenceUnsafe(initialCapacity = 2048)

    @deprecated @inline def possiblyAddLearnedNogoodToReducibleLists(trials: Eli, newLearnedNogoodReducible: NogoodReducible,
                                                                     appendToTotalList: Boolean = true): Unit = {

        addLearnedNogoodReducibleToReducibleLists(newLearnedNogoodReducible = newLearnedNogoodReducible,
            violatedNogoodReducible = violatedNogoodReducible, appendToTotalList)

    }

    def possiblyRemoveLearnedNogoods(trials: Eli, all: Boolean = false): Unit = {

      @inline def findRedundantNogoodsWrt(reducibleA: NogoodReducible): NogoodReduciblesSequenceUnsafe = {

        if (getNogoodSizeFromReducible(reducibleA) > 1) { // TODO: optimize further

          val eliToRed = if (false && allowEliToClarkReduciblesLookup) eliToReduciblesClark else eliWatchedToReducibles // TODO: unclear which is best choice (eliToReduciblesAll or subset eliToReducibles)

          val rl: NogoodReduciblesSequenceUnsafe = eliToRed(eliToJavaArrayIndex(getEliFromNogoodInReducible(reducibleA, 0)))

          intersect.cutoffUS(0)

          var k = 0

          while (k < rl.size) {

            val reducible = rl.getReducibleUS(k)

            if (!isClarkReducible(reducible) &&
              getNogoodSizeFromReducible(reducible) > getNogoodSizeFromReducible(reducibleA))
              intersect.addReducibleUS(reducible)

            k += 1

          }

          var i = 1

          while (i < getNogoodSizeFromReducible(reducibleA) && intersect.size > 0) {

            val nextReducibles = eliToRed(eliToJavaArrayIndex(getEliFromNogoodInReducible(reducibleA, i))).toHashSetOfReduciblesIncompl

            var j = intersect.size - 1

            while (j >= 0) {

              if (!nextReducibles.contains(intersect.getReducibleUS(j)))
                intersect.removeByIndexUS(j)

              j -= 1

            }

            i += 1

          }

          intersect

        } else {

          intersect.cutoffUS(0)

          intersect

        }

      }

      var oldNoOfLearnedNogoods = getApproxNoOfLearnedNogoods

      //println("oldNoOfLearnedNogoods = " + oldNoOfLearnedNogoods + ", nogoodRemovalThreshAdapted = " + nogoodRemovalThreshAdapted.toInt)

      if ((all || removeLearnedNogoodAtRegularRestarts && noOfRestarts % removeLearnedNogoodEveryNthRestart == 0  ||
        !removeLearnedNogoodAtRegularRestarts && (
          (nogoodRemovalThreshInit != 0 &&
            (oldNoOfLearnedNogoods >= nogoodRemovalThreshAdapted.toInt &&
              maxPercentToRemoveOfLearnedNogoods != 0d )) ||
            (/*Glucose-style -->*/ nogoodRemovalThreshInit == 0 &&
              (noOfConflictsTotal % (baseGlucoseStyleNogoodRemovalStrategy + factorGlucoseStyleNogoodRemovalStrategy * noOfNogoodRemovalPhases) == 0)))) &&
      !stopSolverThreads) {

        noOfNogoodRemovalPhases += 1

        val recycleFromTotalList = !all && (nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0 &&  // TODO: unclear benefit, remove?
          noOfNogoodRemovalPhases % nogoodRemovalUsingRecyclingFromTotalHistoryEvery == 0)

        if(recycleFromTotalList) { // Instead of removing a percentage x of the current set of learned nogoods,
          // we make the (1-x) percent highest scored learned nogoods from all times(*) the current set. // TNT
          // (*) requires that !freeOrReassignDeletedNogoodMemory, otherwise we might recycle "old" nogoods
          // which in fact have been already replaced with newer nogoods.

          //assert(!freeOrReassignDeletedNogoodMemory)  // with freeOrReassignDeletedNogoodMemory this branch still works but
          // doesn't do what intended.

          oldNoOfLearnedNogoods = noOfCurrentlyKeptLearnedNogoods

          var actuallyRemoved = 0

          val oss = learnedNogoodReduciblesListCurrent.size

          var i = learnedNogoodReduciblesListCurrent.size - 1 // must traverse from last to first

          while (i >= 0) {  // we remove all currently kept learned nogood (except where deletion isn't possible
            // because they are unit prop reasons)

            val reducibleToRemoveCand: NogoodReducible = learnedNogoodReduciblesListCurrent.get(i) // the nogoods with the lowest scores are deleted with priority

            if (deleteLearnedNogoodReducible(reducibleToRemoveCand, lazyApproach = false)) {

              learnedNogoodReduciblesListCurrent.removeByIndex(i)

              noOfDeletedLearnedNogoods += 1

              noOfCurrentlyKeptLearnedNogoods -= 1

              actuallyRemoved += 1


            }

            i -= 1

          }

          val noOfReduciblesToTakeFromTotalList = ((100.min(learnedNogoodReduciblesListTotal.size).toFloat * (1d - maxPercentToRemoveOfLearnedNogoods))).toInt

          val scoringApproach = 0 // scoringForRemovalOfLearnedNogoods

          val thresholdForTakingOfNogoodsFromTotalListIndex = learnedNogoodReduciblesListTotal.buffer.asInstanceOf[LongArrayUnsafeS].floydRivest(0,
            learnedNogoodReduciblesListTotal.size - 1,
            noOfReduciblesToTakeFromTotalList.toInt,
            by = (reducible: NogoodReducible) => -getNogoodReducibleScore(reducible, scoringForRemovalOfLearnedNogoods = scoringApproach))

          val thresholdForTakingOfNogoodsFromTotalList = getNogoodReducibleScore(learnedNogoodReduciblesListTotal.get(thresholdForTakingOfNogoodsFromTotalListIndex), scoringForRemovalOfLearnedNogoods = scoringApproach)

          var taken = 0

          var j = 0

          while(j < learnedNogoodReduciblesListTotal.size && taken < noOfReduciblesToTakeFromTotalList) {

            val newOldNogoodReducible = learnedNogoodReduciblesListTotal.get(j)

            val score = getNogoodReducibleScore(newOldNogoodReducible, scoringForRemovalOfLearnedNogoods = scoringApproach)

            val flip = false //rngLocal.nextFloat() < 0.1f

            if(!flip && score >= thresholdForTakingOfNogoodsFromTotalList ||
              flip && score < thresholdForTakingOfNogoodsFromTotalList) {

              val red = cloneNogoodReducible(newOldNogoodReducible)

              possiblyAddLearnedNogoodToReducibleLists(trials, red, appendToTotalList = false)

              taken += 1

            }

            j += 1

          }

          noOfRecycledLearnedNogoodsFromTotal += taken

          //  println("taken = " + taken)

          // println("\nnoOfCurrentlyKeptLearnedNogoods = " + noOfCurrentlyKeptLearnedNogoods)

        } else {

          assert(all || maxPercentToRemoveOfLearnedNogoods < 1d)

          oldNoOfLearnedNogoods = getApproxNoOfLearnedNogoods

          //println("\n\noldNoOfLearnedNogoods = " + oldNoOfLearnedNogoods)

          //println("  removeLearnedNogoods = " + removeLearnedNogoods)

          val maxNoOfLearnedNogoodsToRemove = if(all) oldNoOfLearnedNogoods else (oldNoOfLearnedNogoods.toDouble * maxPercentToRemoveOfLearnedNogoods).toInt

          //println("\n Planning to remove " + oldNoOfLearnedNogoods + " learned nogoods...")

          if (maxNoOfLearnedNogoodsToRemove > 0) {

            var actuallyRemoved = 0

            // We use the following threshold to avoid having to sort all the learned nogoods by their scores, but
            // it's not a 100% precise way to split the nogoods into two halfs, can lead to removal ratios different
            // from 0.5:

            /*println("\n=============================================================================")
                      learnedNogoodReduciblesList.buffer.toArray.take(learnedNogoodReduciblesList.size).foreach(red =>

                        println("red: " + red + ", score = " + getNogoodReducibleScore(red, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods))
                      )*/

            val thresholdForRemovalOfNogoodsIndex = learnedNogoodReduciblesListCurrent.buffer.asInstanceOf[LongArrayUnsafeS].floydRivest(0,
              learnedNogoodReduciblesListCurrent.size - 1,
              (learnedNogoodReduciblesListCurrent.size.toFloat * maxPercentToRemoveOfLearnedNogoods).toInt,
              by = (reducible: NogoodReducible) => getNogoodReducibleScore(reducible, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods))

            val thresholdForRemovalOfNogoodsItem = learnedNogoodReduciblesListCurrent.buffer.get(thresholdForRemovalOfNogoodsIndex)

            thresholdForRemovalOfNogoods = getNogoodReducibleScore(thresholdForRemovalOfNogoodsItem, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods)

            var i = learnedNogoodReduciblesListCurrent.size - 1 // must traverse from last to first

            while (i >= 0 && actuallyRemoved < maxNoOfLearnedNogoodsToRemove) {

              val reducibleToRemoveCand: NogoodReducible = learnedNogoodReduciblesListCurrent.get(i) // the nogoods with the lowest scores are deleted with priority

              if (getNogoodReducibleScore(reducibleToRemoveCand, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods) <=
                thresholdForRemovalOfNogoods) {

                if (deleteLearnedNogoodReducible(reducibleToRemoveCand, lazyApproach = false)) {

                  learnedNogoodReduciblesListCurrent.removeByIndex(i)

                  noOfDeletedLearnedNogoods += 1

                  noOfCurrentlyKeptLearnedNogoods -= 1

                  actuallyRemoved += 1

                }

              }

              i -= 1

            }

          }

        }

        if (inProcessingSubsumption && noOfRestarts % inProcessingSubsumptionEvery == 0) { // TODO: optimize further:

          var removedBySubsumption = 0

          var snogiA = 0

          val removedIndicesInLearnedNogoodReduciblesList = ArrayBuffer[Eli]()

          while (snogiA < learnedNogoodReduciblesListCurrent.size) {

            val reducibleA: NogoodReducible = learnedNogoodReduciblesListCurrent.get(snogiA)

            if (true) {

              val nogoodReduciblesWhichContainNogoodA: NogoodReduciblesSequenceUnsafe = findRedundantNogoodsWrt(reducibleA)

              var j = 0

              while (j < nogoodReduciblesWhichContainNogoodA.size) {

                val subsumingReducibleToBeDeleted = nogoodReduciblesWhichContainNogoodA.getReducibleUS(j)

                if (deleteLearnedNogoodReducible(subsumingReducibleToBeDeleted, lazyApproach = false)) {

                  removedBySubsumption += 1

                  removedIndicesInLearnedNogoodReduciblesList.append(learnedNogoodReduciblesListCurrent.indexOf(subsumingReducibleToBeDeleted))

                }

                j += 1

              }


            }

            snogiA += 1

          }

          if (!removedIndicesInLearnedNogoodReduciblesList.isEmpty)
            removedIndicesInLearnedNogoodReduciblesList.sorted.reverse.foreach(index => learnedNogoodReduciblesListCurrent.removeByIndex(index))

          if (debug && removedBySubsumption > 0)
            println("\nremovedBySubsumption = " + removedBySubsumption)

        }

        // After reduction, we feed (some of) the k-top scored remaining learned nogood into the sharing pool (NB: not all of
        // these will necessarily be fetched by other threads, see fetchLearnedNogoodsFromOtherThreads):
        {

          /*nogoodReducibleExchangePool.synchronized*/
          {
            if (nogoodShareNumberMax != 0f && maxCompetingSolverThreads > 1 && learnedNogoodReduciblesListCurrent.size > 0 &&
              !stopSolverThreads) {

              var i = 1

              while (i <= nogoodShareTopKPutIntoSharingPool && i < learnedNogoodReduciblesListCurrent.size) {

                val red = learnedNogoodReduciblesListCurrent. /*getFromHeap*/ get(learnedNogoodReduciblesListCurrent.size - i)

                if (getNogoodSizeFromReducible(red) <= nogoodShareSizeLimit /*rngLocal.nextFloat() < 0.1f*/) {

                  if (sharedAmongSingleSolverThreads.nogoodReducibleExchangePoolSourceThreadsForCyclicSharingPrevention. /*contains(red)*/ getOrDefault(red, -1) != threadNo) {
                    // we need to ensure that a nogood isn't shared in a cyclic fashion to the same thread (would lead to exponential increase
                    // in nogoods, as there is no dubplicate check). Alternatively, we prevent that a nogood is
                    // shared more than once in total. TODO: Observe that in both cases, we cannot recognize reassigned
                    // nogood memory addresses.

                    sharedAmongSingleSolverThreads.nogoodReducibleExchangePool.put(red, threadNo)

                    sharedAmongSingleSolverThreads.nogoodReducibleExchangePoolSourceThreadsForCyclicSharingPrevention.put(red, threadNo)

                    //println("\nPut into nogood exchange pool: " + red)

                  } //else
                  //println("\nResharing of nogood prevented for " + red)

                }

                i += 1

              }

            }

          }

        }


      }

      fetchSharedLearnedNogoodsFromOtherThreads // was previously in restart but position doesn't seem to make a difference (?)

    }

    intersect.addToGarbage()

    def weaklyRephase = {

      // println("\n" + noOfConflictsTotal)

      if (weakRephasingAtRestartEvery > 0 &&
        noOfRestarts % weakRephasingAtRestartEvery == 0 /* noOfConflictsTotal % 200 == 0 */ &&
        bestPhasesQueue != null) {

        val (continue, bp) = bestPhasesQueue.synchronized {

          val c = bestPhasesQueue.isEmpty

          if (c)
            (false, null)
          else
            (true, bestPhasesQueue.randomElement(bestPhasesQueue.size))

        }

        if (continue) {

          noOfWeakRephasings += 1

          var absEli = 1

          while (absEli <= noOfAbsElis) {

            if (rngLocal.nextFloat() > 0.01f)
              updateInPhasePreviousForAbsElis(absEli, bp.get(absEli).toByte)

            absEli += 1

          }

        }

      }
    }

    def restart(trials: Int, jumpBackLevelFromConflict: Int = -1 /*-1 = full restart*/,
                temporaryDisableReusedTrailRestarts: Boolean = false): Unit = {

      if (debug2) println("\nRestart...")

      if(resetLocalPRNGonRestart == 1)
        rngLocal.setSeed(rngGlobal.nextLong()) else if(resetLocalPRNGonRestart == 2)
          rngLocal.setSeed(seed)
      //(NB: even setting the same seed at each restart (which also resets the PRNG), we would normally not replay the same decisions, as learned nogoods and various other accumulated things will be different)

      if(adaptNoisePhaseMemo != 0 && noisePhaseMemo > 0d && noOfConflictsTotal > 1) {

        if(adaptNoisePhaseMemo == 1)
          noisePhaseMemo = noisePhaseMemoR / Math.log(noOfConflictsTotal).toFloat
        else if(adaptNoisePhaseMemo == 2) {

          val sqrtc = math.sqrt(noOfConflictsTotal)

          noisePhaseMemo = noisePhaseMemoR * ((math.sin(sqrtc / 10d) + 1d) / sqrtc * 100d).toFloat

        } else if(adaptNoisePhaseMemo == 3) {

          val sqrtt = math.sqrt(noOfRestarts * 100)

          noisePhaseMemo = noisePhaseMemoR * ((math.sin(sqrtt / 10d) +1d) / sqrtt * 100d).toFloat

        }

      }

      val restartToLevel = if (reusedTrailRestarts && !temporaryDisableReusedTrailRestarts) { // based on van der Tak et al '11

        rndmBranchProb = 0f

        assert(freeEliSearchApproach11or14or15)

        val nextDecisionAbsEli = {

          var nextDecisionAbsEli = 0

          if (freeEliSearchApproach == 14) { // TODO: redundant remove/re-adds below:

            while (unassignedAbsEliSet.size > 0 && nextDecisionAbsEli == 0) {

              val pe = unassignedAbsEliSet.getRemoveLast()

              if (isNotAbsSetInPass(pe))
                nextDecisionAbsEli = pe

            }

            if (nextDecisionAbsEli != 0)
              unassignedAbsEliSet.addSorted(nextDecisionAbsEli)

          } else if (freeEliSearchApproach == 11) { // TODO: redundant remove/re-adds below:

            while (unassignedScoredAbsElisPriorityQueue.size > 0 && nextDecisionAbsEli == 0) {

              val pe = unassignedScoredAbsElisPriorityQueue.dequeue()

              if (isNotAbsSetInPass(pe))
                nextDecisionAbsEli = pe

            }

            if (nextDecisionAbsEli != 0)
              unassignedScoredAbsElisPriorityQueue.enqueue(nextDecisionAbsEli)

          } else if (freeEliSearchApproach == 15) {

            var bin = unassignedAbsEliBinSet.length - 1

            while (bin >= 0 && nextDecisionAbsEli == 0) {

              if (!unassignedAbsEliBinSet(bin).isEmpty) {

                val freeAbsEli = unassignedAbsEliBinSet(bin).getLast()

                assert(isNotAbsSetInPass(freeAbsEli))

                nextDecisionAbsEli = freeAbsEli

              }

              bin -= 1

            }

          }

          nextDecisionAbsEli

        }

        val r = if (nextDecisionAbsEli == 0)
        -1
        else {

          var bjLevel = 1

          var cont = true

          while (bjLevel <= jumpBackLevelFromConflict && cont) {

            if (getAbsEliScore(toAbsEli(getDecisionAbsEliSeqForRTR(bjLevel))) < getAbsEliScore(nextDecisionAbsEli)) {

              cont = false

            } else
              bjLevel += 1

          }

          bjLevel - 1

        }

        r

      } else
        jumpBackLevelFromConflict


      noOfRestarts += 1

      noOfConflictsAfterRestart = 0

      timeOfLastRestartNs = System.nanoTime()

      weaklyRephase

      if (absEliClusteredLocal != null && (freeEliSearchApproach == 7 || freeEliSearchApproach == 8)) { // TODO: remove?

        shuffleArray(absEliClusteredLocal, rngLocal)

        var i = 0

        while (i < absEliClusteredLocal.length) {

          absEliClusteredLocal(i) = absEliClusteredLocal(i).reverse

          i += 1

        }

      }

      if (restartTriggerConf._1 == 2) {

        if (noOfConflictsBeforeRestart >= outerGeom) {

          outerGeom *= noOfConflictsBeforeRestartFact

          noOfConflictsBeforeRestart = restartTriggerConf._2

        } else
          noOfConflictsBeforeRestart *= noOfConflictsBeforeRestartFact

      } else if (restartTriggerConf._1 == 3) {

        if ((lubyU & -lubyU) == lubyV) { // Luby as a reluctant doubling sequence (Knuth'12)

          lubyU += 1

          lubyV = 1

        } else {

          lubyV *= 2

        }

        noOfConflictsBeforeRestart = lubyV * noOfConflictsBeforeRestartFact

        if (debug2)
          println("\nnoOfConflictsBeforeRestart = " + noOfConflictsBeforeRestart)

      }

      if (noOfConflictsBeforeRestart < lowerBoundForNoOfConflictsBeforeRestart)
        noOfConflictsBeforeRestart = lowerBoundForNoOfConflictsBeforeRestart

      val jbt: Eli = restartToLevel

      jumpBack(jbt, trials)

      if (rndmBranchProbR < 0) {

        rndmBranchProb = (1f - orderNumber.toFloat / noOfAbsElis.toFloat) / -rndmBranchProbR

      }

    }


    @inline def addLearnedNogoodReducibleToReducibleLists(newLearnedNogoodReducible: NogoodReducible,
                                                          violatedNogoodReducible: NogoodReducible,
                                                          appendToTotalList: Boolean = true): Unit = {
      // Called for conflict nogoods, but also nogoods acquired by sharing and loops.
      // ! NOT used for adding initial ("clark") nogoods !

      assert(newLearnedNogoodReducible != 0l)

      if (getNogoodSizeFromReducible(newLearnedNogoodReducible) == 0)
        return

      learnedNogoodReduciblesListCurrent.append(newLearnedNogoodReducible) // (this is not a watch list, but just used when all learned nogoods need to be examined)

      noOfCurrentlyKeptLearnedNogoods += 1

      if(appendToTotalList && learnedNogoodReduciblesListTotal != null)  // the only reason not to do this is if the nogood is already in learnedNogoodReduciblesListTotal (recycled nogood)
      learnedNogoodReduciblesListTotal.append(newLearnedNogoodReducible)

      if (debug2)
        println("\naddLearnedNogoodReducibleToReducibleLists " + newLearnedNogoodReducible + " (" + nogoodInReducibleToString(newLearnedNogoodReducible) + ")")

      if (extReducibles == 2) {

        if (getNogoodSizeFromReducible(newLearnedNogoodReducible) > 1) {

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(newLearnedNogoodReducible, 0))).addReducibleUS(newLearnedNogoodReducible)

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(newLearnedNogoodReducible, 1))).addReducibleUS(newLearnedNogoodReducible)

        } else {

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(newLearnedNogoodReducible, 0))).addReducibleUS(newLearnedNogoodReducible)

        }

        if (debug2)
          printInfoAboutReducible(newLearnedNogoodReducible)

      } else if (extReducibles == 1) {

        var i = getNogoodSizeFromReducible(newLearnedNogoodReducible) - 1

        if (violatedNogoodReducible != 0l && getNogoodSizeFromReducible(violatedNogoodReducible) == 1 && i == 0 &&
          getEliFromNogoodInReducible(newLearnedNogoodReducible, 0) == getEliFromNogoodInReducible(violatedNogoodReducible, 0)) {

          return

        }

        while (i >= 0) {

          val eliInNewNogood = getEliFromNogoodInReducible(newLearnedNogoodReducible, i)

          if (extraChecks) assert(eliInNewNogood != 0)

          val reduciblesWithEliInNewNogood: NogoodReduciblesSequenceUnsafe = eliWatchedToReducibles(eliToJavaArrayIndex(eliInNewNogood))

          if ((eliInNewNogood == getIntFromReducible(newLearnedNogoodReducible, 3) ||
            getNogoodSizeFromReducible(newLearnedNogoodReducible) > 1 && eliInNewNogood == getIntFromReducible(newLearnedNogoodReducible, 4))) {

            reduciblesWithEliInNewNogood.addReducibleUS(newLearnedNogoodReducible)

          }

          eliToReduciblesDeficitResto(eliToJavaArrayIndex(eliInNewNogood)).addReducibleUS(newLearnedNogoodReducible)

          i -= 1

        }

      } else if (extReducibles == 3 || extReducibles == 5) { // in this case all(!) elis in the nogood are watched

        initializeReducibleBitsetExt35(newLearnedNogoodReducible)

        setupWatchReduciblesForExtReducibles345(newLearnedNogoodReducible)

      } else if (extReducibles == 4) { // in this case all(!) elis in the nogood are watched

        initializeReducibleBitsetExt4(newLearnedNogoodReducible)

        setupWatchReduciblesForExtReducibles345(newLearnedNogoodReducible)

      } else {  // TODO: the following branch is deprecated: remove

        // !! If maintainEliToFullReducibles = false, one of the elis for which this nogood is entered into its reducible (~watch) list must
        // be a absunassigned eli (i.e., sigmaEli), which is ensured by pre-sorting the learned nogood.
        // Otherwise, conflict analysis might fail to find reason nogoods.
        // In any case (regardless of maintainEliToFullReducibles), we need to add the nogood to reducible lists for two elis (or none, but
        // then the learned nogood would of course have no effect at all), except for singleton nogood.

        if (getNogoodSizeFromReducible(newLearnedNogoodReducible) == 1) {

          val eli = getEliFromNogoodInReducible(newLearnedNogoodReducible, 0)

          eliWatchedToReducibles(eliToJavaArrayIndex(eli)).addReducibleUS(newLearnedNogoodReducible)

        } else {

          assert(newLearnedNogoodReducible != 0l)

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(newLearnedNogoodReducible, 0))).addReducibleUS(newLearnedNogoodReducible)

          eliWatchedToReducibles(eliToJavaArrayIndex(getEliFromNogoodInReducible(newLearnedNogoodReducible, 1))).addReducibleUS(newLearnedNogoodReducible)

        }

      }

    }
        @inline def fetchSharedLearnedNogoodsFromOtherThreads: Unit = {

      if (nogoodShareNumberMax != 0f && maxCompetingSolverThreads > 1 && !stopSolverThreads) {

        import scala.collection.JavaConverters._

        val moveoverNogoods: mutable.Set[Map.Entry[NogoodReducible, Eli]] = sharedAmongSingleSolverThreads.nogoodReducibleExchangePool.entrySet().asScala.
          filter((value: Map.Entry[NogoodReducible, Eli]) => {

            //println("\n" + getNogoodReducibleScore(value.getKey, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods))

            val r = value.getValue != threadNo

            r

          })

        /*nogoodReducibleExchangePool.synchronized*/
        {

          //if(moveoverNogoods.size > 0)
          //println("\n moveoverNogoods = " + moveoverNogoods.size)

          if (moveoverNogoods.size > 0) {

            val t = ((getApproxNoOfLearnedNogoods.toFloat * nogoodShareNumberMax).toInt).min(moveoverNogoods.size)

            noOfSharedNogoods += t

            // println("\n  This thread: $" + threadNo + ", fetching " + t + " nogoods from other threads...")

            moveoverNogoods.take(t).foreach { case (value: Map.Entry[NogoodReducible, Eli]) => {

              /*nogoodReducibleExchangePool.synchronized*/
              {

                sharedAmongSingleSolverThreads.nogoodReducibleExchangePool.remove(value.getKey)

                val red = cloneNogoodReducible(value.getKey)

                /* crash:

                                  val reducible = generateNogoodReducibleFromNogoodClarkOrSpecial(
                                    nogoodAddr = generateRefToNogoodInReducible(red/*value.getKey*/), nogoodSize =
                                      getNogoodSizeFromReducible(red/*value.getKey*/),
                                    beforeSolvingstarted = false) // we can't use the shared reducible directly because of its thread-specific meta-data
                */
                //println("thread $" + threadNo + ", took over nogood reducible: " + reducible)

                addLearnedNogoodReducibleToReducibleLists(red, violatedNogoodReducible = 0l)

              }

            }

            }

          }

        }

      }

    }

    var modelOpt: Option[(Array[Eli], IntOpenHashSet)] = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

    var noisePhaseMemo: Float = noisePhaseMemoR

    var uncertainEliSearchStart = 0

    tempFacts.foreach(tempFactEli => {

      val factNogood = new IntArrayUnsafeS(Array(negateEli(tempFactEli)))

      val newFactNogoodReducible = generateNogoodReducibleFromNogoodClarkOrSpecial(nogoodAddr = factNogood.getAddr,
        nogoodSize = factNogood.sizev /*, flags = 1*/ , beforeSolvingstarted = false)

      addLearnedNogoodReducibleToReducibleLists(newFactNogoodReducible, 0l)
      // TODO: sicherstellen dass diese Fact-nogoods nicht später gelöscht werden!!!
      // Wie verhält sich das zu cngs3 in Preparation.scala?

    })

    @inline def phasedEli(absEli: Eli): Eli = {

      if (noisePhaseMemo >= 0f) {

        if (noisePhaseMemo == 0f || rngLocal.nextFloat() >= noisePhaseMemo) {

          if (getFromPhasePreviousForAbsElis(absEli) != 0x00.toByte) // don't check using "== 0x01.toByte" (isn't what it seems to be, see byte code)
            absEli
          else
            negatePosEli(absEli)

        } else {

          if (getFromPhasePreviousForAbsElis(absEli) == 0x00.toByte) // don't check using "== 0x01.toByte" (isn't what it seems to be)
            absEli
          else
            negatePosEli(absEli)

        }

      } else {

        if (noisePhaseMemo == -1f || rngLocal.nextFloat() < -noisePhaseMemo)
          absEli
        else
          negatePosEli(absEli)

      }

    }

    def findDecisionEli: Eli = {  // heuristic or probabilistic branching

      //rndmBranchProb *= rndmBranchProbDecay
      //       rndmBranchProb = //(1f - (noOfConflictsTotal.toFloat / trials.toFloat))/ 50f
      //        (lbdema - 3) / 500f // the higher (i.e., worse) the average LBD, the higher the randomness of the branching decisions

      //Thread.`yield`

      // Branching decision heuristics & parameter eli decision using symbolic or automatic differentiation (partial derivative)

      if (!ignoreParamVariables) {

        // We check the parameter atoms (random variables) in the order provided by the sorted partial derivatives (over multiple atoms, this
        // implicitly gives the gradient):

        var i = uncertainEliSearchStart // if there wasn't a conflict after the previous parameter eli assignment, we
        // don't need to start searching from start again.

        while (i < deficitOrderedUncertainLiteralsHalf) {

          val uncertainEli = deficitOrderedUncertainLiteralsForJava(i)

          if (isNotAbsSetInPass(uncertainEli)) {

            uncertainEliSearchStart = if (i + 1 >= deficitOrderedUncertainLiteralsHalf) 0 else i + 1

            return /*literally*/ (uncertainEli)

          }

          i += 1

        }

      }

      @inline def findFreeVarUsingLinearSearch(ignoreAbsEliScoresInLinearSearch: Boolean /*useActivities: Boolean*/): Eli = {
        // only makes sense if the variables and nogoods are (or have been brought) in a "lucky" order

        var freeVarActiv = -Double.MaxValue

        var freeEli = 0

        if (absEliClusteredLocal != null) {

          var clusterIndex = 0

          while (clusterIndex < absEliClusteredLocal.length) {

            var i = 0

            while (i < absEliClusteredLocal(clusterIndex).length) {

              val absEliInCluster = absEliClusteredLocal(clusterIndex)(i)

              if (getAbsEliScore(absEliInCluster) > freeVarActiv && isNotAbsSetInPass(absEliInCluster)) {

                freeVarActiv = getAbsEliScore(absEliInCluster)

                freeEli = absEliInCluster

              }


              i += 1

            }

            clusterIndex += 1

          }

        } else {

          var i = 0

          while (i < noOfAbsElis) {

            val absEli = absElisSeqArranged.get(i)

            if (isNotAbsSetInPass(absEli) && getAbsEliScore(absEli) > freeVarActiv) {

              if (ignoreAbsEliScoresInLinearSearch)
                return phasedEli(absEli)

              freeVarActiv = getAbsEliScore(absEli)

              freeEli = absEli

            }


            i += 1

          }


        }

        return freeEli

      }

      if (((orderNumber > 1 /*<- i.e., not directly after restarts or in trial 1*/ || !diversifyLight) && !diversify &&
        (rndmBranchProb == 0 || rngLocal.nextFloat() > rndmBranchProb))) {

        if (freeEliSearchApproach == 15) {

          var bin = unassignedAbsEliBinSet.length - 1

          while (bin >= 0) {

            if (!unassignedAbsEliBinSet(bin).isEmpty) {

              val freeAbsEli = if (absEliScoringApproach != 0 /*<- because of less accurate bin mapping with approach 0*/ ||
                unassignedAbsEliBinSet(bin).size == 1) {

                unassignedAbsEliBinSet(bin).getLast()

              } else { // optional: linear search within the bin

                var maxAbsEliScore = Float.MinValue

                var maxAbsEli = -1

                var i = 0

                while (i < unassignedAbsEliBinSet(bin).size) {

                  val absEli = unassignedAbsEliBinSet(bin).get(i)

                  if (getAbsEliScore(absEli) > maxAbsEliScore) {

                    maxAbsEliScore = getAbsEliScore(absEli)

                    maxAbsEli = absEli

                  }

                  i += 1

                }

                maxAbsEli

              }

              assert(isNotAbsSetInPass(freeAbsEli))

              return phasedEli(freeAbsEli)

            }

            bin -= 1

          }

        } else if (freeEliSearchApproach == 14) {

          if (false) {

            if (unassignedAbsEliSet.size > 0 && unassignedAbsEliSet.size < 50)
              println("\n------------------ + unassignedAbsEliSet.size = " + unassignedAbsEliSet.size)


            dtaIndexOfMaxScoredInUnassignedAbsEliSet = -1

            var i = unassignedAbsEliSet.size - 1

            while (i >= 0) {

              if (unassignedAbsEliSet.size > 0 && unassignedAbsEliSet.size < 50) println("i: " + i + ", unassignedAbsEliSet.get(i) = " + unassignedAbsEliSet.get(i) + ", score = " + getAbsEliScore(unassignedAbsEliSet.get(i)))

              if (dtaIndexOfMaxScoredInUnassignedAbsEliSet < 0 || getAbsEliScore(unassignedAbsEliSet.get(i)) > getAbsEliScore(unassignedAbsEliSet.get(dtaIndexOfMaxScoredInUnassignedAbsEliSet))) {

                dtaIndexOfMaxScoredInUnassignedAbsEliSet = i

              }

              i -= 1

            }

            if (dtaIndexOfMaxScoredInUnassignedAbsEliSet != -1) {

              assert(isNotAbsSetInPass(unassignedAbsEliSet.get(dtaIndexOfMaxScoredInUnassignedAbsEliSet)))

              return phasedEli(unassignedAbsEliSet.get(dtaIndexOfMaxScoredInUnassignedAbsEliSet))

            }

          } else if (!unassignedAbsEliSet.isEmpty) { // if unassignedAbsEliSet is kept sorted:

            val freeAbsEli = unassignedAbsEliSet.getLast()

            assert(isNotAbsSetInPass(freeAbsEli))

            return phasedEli(freeAbsEli)

          }


        } else if (freeEliSearchApproach == 11) { // heap / priority queue-based search, similar (but not identical) to, e.g., MiniSAT

          /*if(trials % 50000 == 0) {  // for debugging purposes:

            println("\n\n" + unassignedScoredAbsElisPriorityQueue.size)

            while (unassignedScoredAbsElisPriorityQueue.size > 0) {

              val absEli = unassignedScoredAbsElisPriorityQueue.dequeue()

              println(getAbsEliScore(absEli))


            }

          } else*/
          {

            while (unassignedScoredAbsElisPriorityQueue.size > 0) {

              val absEli = if (rndmBranchProb > 0 && rngLocal.nextFloat() < rndmBranchProb)
                unassignedScoredAbsElisPriorityQueue.getHeap(rngLocal.nextInt(unassignedScoredAbsElisPriorityQueue.getHeap.length))
              else
                unassignedScoredAbsElisPriorityQueue.dequeue()

              //println(getAbsEliScore(absEli))

              if (isNotAbsSetInPass(absEli))
                return phasedEli(absEli)

            }

          }

        } else if (freeEliSearchApproach == 9) {

          if (!unassignedScoredAbsEliTreeSet.isEmpty) {

            val absEli = unassignedScoredAbsEliTreeSet.firstInt

            //assert(isNotAbsSetInPass(absEli)) // If this fails, firstly check if the sorting order of elements which are
            // already in the tree might have changed after adding them to the tree (as this would violate the tree contract).

            if (isNotAbsSetInPass(absEli))
              return absEli

          }

        } else if (freeEliSearchApproach == 12) {

          var pivotEli_ = 0

          var uu = if (dl == 0)
            0
          else
            usedUpInLevel.get(dl - 1)

          while (pivotEli_ == 0 && uu < noOfAbsElis) {

            if (isNotAbsSetInPass(absElisSeqArranged.get(uu))) { // NB: the elis in elisArranged are not necessarily abs/pos

              pivotEli_ = absElisSeqArranged.get(uu)

            } else
              uu += 1

          }

          usedUpInLevel.update(dl, uu) // carrying over uu to the next level

          if (pivotEli_ != 0)
            return phasedEli((pivotEli_))

        } else if (freeEliSearchApproach == 13) {

          var pivotEli_ = 0

          var uu = if (dl == 0) {

            0

          } else {

            usedUpInLevel.get(dl - 1)

          }

          var maxAbsEliScore = Double.MinValue

          while (uu < noOfAbsElis) {

            val candAbsEli = absElisSeqArranged.get(uu)

            if (isNotAbsSetInPass(candAbsEli) && getAbsEliScore(candAbsEli) > maxAbsEliScore) { // NB: the elis in elisArranged are not necessarily abs/pos

              maxAbsEliScore = getAbsEliScore(candAbsEli)

              pivotEli_ = candAbsEli

              uu += 1

              usedUpInLevel.update(dl, uu)

            } else
              uu += 1

          }

          if (pivotEli_ == 0) {

            uu = 0

            usedUpInLevel.update(dl, uu) // carrying over uu to the next level

          }

          if (pivotEli_ != 0)
            return phasedEli(pivotEli_)

        }

        else if (freeEliSearchApproach == 7) {

          val freeEli = findFreeVarUsingLinearSearch(ignoreAbsEliScoresInLinearSearch = true)

          if (freeEli != 0)
            return freeEli

        } else if (freeEliSearchApproach == 8) {

          val freeEli = findFreeVarUsingLinearSearch(ignoreAbsEliScoresInLinearSearch = false)

          if (freeEli != 0)
            return freeEli

        } else
          stomp(-1, "Nonexistent free literal search heuristics: " + freeEliSearchApproach)

      } else { // random selection (enforced by --solverarg diversify true)

        assert(noOfAllElis > 0)

        var freeEliCand = 0

        do {

          freeEliCand = rngLocal.nextInt(noOfAllElis + 1) - noOfAbsElis

        } while (isPosOrNegSetInPass(freeEliCand) || freeEliCand == 0)

        return freeEliCand

      }

      // If the prev approach didn't succeed, we end up here:

      do {

        val freeEliCand = rngLocal.nextInt(noOfAbsElis) + 1

        if (isNotAbsSetInPass(freeEliCand))
          return phasedEli(freeEliCand) // the difference to a purely random decision is that the polarity is
        // taken from phasePreviousForAbsElis

      } while (true)

      0

    }

    val noOfPosElisPlus1 = noOfAbsElis + 1

  }  // ´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´´
