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

import java.lang.management.ManagementFactory
import java.util
import java.util.Map
import java.util.concurrent._

import sun.misc.Contended

import aspIOutils._

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.DifferentialFunction

import sharedDefs._

import commandline.delSAT._

import diff.UncertainAtomsSeprt

import it.unimi.dsi.fastutil.ints._
import it.unimi.dsi.fastutil.objects.ObjectArrayList

import utils.{LongArrayUnsafe, Tarjan, XORShift32}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * @author Matthias Nickles
  *
  */
class SolverMulti(prep: Preparation) {

  import prep._

  val noPassBits = 64

  val ORDERBITS: Long = 42 // number of bits for storing the assignment orderOfEli of an eli within a positive int (32bit) value

  val maxOrderNo = 1l << ORDERBITS

  val maxDecisions = 1l << (noPassBits - ORDERBITS)

  /** This computes both the total cost and all inner costs.
    * Call only after updating the measured atom frequencies.
    *
    * Notice that this function does not update the costs with the current counts of measured atoms in the sample.
    *
    */
  @inline def currentCosts(costFctsInner: Array[DifferentialFunction[DoubleReal]]): (Double /*total cost*/ ,
    Array[Double /*inner costs*/ ]) = {

    if (costFctsInner.length == 0)
      (0d, Array[Double]())
    else {

      var costUnnorm = 0d

      val innerCosts = costFctsInner.map((costFctInner: DifferentialFunction[DoubleReal]) => {

        val costInner = costFctInner.getReal

        costUnnorm += costInner

        costInner

      })

      (costUnnorm / costFctsInner.length.toDouble, innerCosts)

    }

  }

  val uncertainAtomsUpdateExecutorService = new ThreadPoolExecutor(2, 2, 3, TimeUnit.SECONDS, new LinkedBlockingQueue[Runnable])

  var maxCompetingSolverThreads = if (maxCompetingSolverThreadsR == -1) (if (noOfPosElis < 2000 && clarkNogoods.length < 5000)
    1
  else
    Runtime.getRuntime().availableProcessors() / (if (abandonThreadsThatFellBehind) 1 else 2)).toInt else maxCompetingSolverThreadsR

  val localSolverParallelThresh = if (skipNogisHTElisInBCP) localSolverParallelThreshMax else localSolverParallelThreshR

  @inline def updateAtomsFreqs(mOpt: Option[IntOpenHashSet],
                               measuredAtomElis: Array[Eli],
                               uncertainAtomEliToStatisticalProb: Array[Double],
                               sampledModels /*after adding new model m*/ : mutable.ArrayBuffer[Array[Eli]],
                               fromScratch: Boolean = false) = {

    assert(!fromScratch)

    mOpt.foreach(m => {
      val newModelsCount: Double = sampledModels.length.toDouble

      if (measuredAtomElis.length > localSolverParallelThresh * 5) {

        val tasks = new util.ArrayList[Runnable]()

        val cdl = new CountDownLatch(2)

        tasks.add(new Runnable() {

          override def run(): Unit = {

            var i = 0

            val il = measuredAtomElis.length / 2

            while (i < il) {

              val measuredAtomEli = measuredAtomElis(i)

              uncertainAtomEliToStatisticalProb(measuredAtomEli) = (uncertainAtomEliToStatisticalProb(measuredAtomEli) * (newModelsCount - 1d) +
                (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount

              i += 1

            }

            cdl.countDown()

          }

        })

        tasks.add(new Runnable() {

          override def run(): Unit = {

            var i = measuredAtomElis.length / 2

            val il = measuredAtomElis.length

            while (i < il) {

              val measuredAtomEli = measuredAtomElis(i)

              uncertainAtomEliToStatisticalProb(measuredAtomEli) = (uncertainAtomEliToStatisticalProb(measuredAtomEli) * (newModelsCount - 1d) +
                (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount

              i += 1

            }

            cdl.countDown()

          }

        })

        uncertainAtomsUpdateExecutorService.execute(tasks.get(0))

        uncertainAtomsUpdateExecutorService.execute(tasks.get(1))

        cdl.await()

      } else {

        var i = 0

        val il = measuredAtomElis.length

        while (i < il) {

          val measuredAtomEli = measuredAtomElis(i)

          uncertainAtomEliToStatisticalProb(measuredAtomEli) = (uncertainAtomEliToStatisticalProb(measuredAtomEli) * (newModelsCount - 1d) +
            (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount

          i += 1

        }

      }

    })

  }

  @inline def updateMeasuredAtomsFreqsAndComputeCost(mOpt: Option[IntOpenHashSet],
                                                     measuredAtomElis: Array[Eli],
                                                     measuredAtomEliToStatisticalFreq: Array[Double],
                                                     sampledModels /*after adding new model m*/ : mutable.ArrayBuffer[Array[Eli]],
                                                     costFctsInner: Array[DifferentialFunction[DoubleReal]],
                                                     fromScratch: Boolean = false,
                                                     computeCosts: Boolean = true,
                                                     partDerivativeComplete: Boolean,
                                                     update_parameterAtomVarForParamEli_forPartDerivCompl: => Unit
                                                    ):
  Option[(Double /*total cost*/ , Array[Double /*inner costs*/ ])] = {

    // We firstly update the measured uncertainty atoms (which, for now, need to be identical with the parameter atoms):

    updateAtomsFreqs(mOpt,
      measuredAtomElis,
      measuredAtomEliToStatisticalFreq,
      sampledModels,
      fromScratch)

    if (partDerivativeComplete)
      update_parameterAtomVarForParamEli_forPartDerivCompl

    if (!computeCosts)
      None
    else
      Some(currentCosts(costFctsInner))

  }

  case class SampleMultiConf(costsOpt: Option[UncertainAtomsSeprt],
                             requestedNoOfModelsBelowThresholdOrAuto: Int,
                             prep: Preparation,
                             requestedNumberOfModels: Int /*-1: stopSolverThreads at minimum number of models required to reach threshold*/ ,
                             threshold: Double,
                             maxIt: Int);

  /**
    * @author Matthias Nickles
    *
    */
  def sampleMulti(sampleMultiConf: SampleMultiConf): (mutable.Seq[Array[Pred]]) = {

    import sampleMultiConf._

    //@deprecated val competingSolversExecutorServiceR: ExecutorService = null.asInstanceOf[ExecutorService] /*new ThreadPoolExecutor(maxCompetingSolverThreads, maxCompetingSolverThreads,
    // 60, TimeUnit.SECONDS, new LinkedBlockingQueue[Runnable])*/

    val sampledModels = ArrayBuffer[Array[Eli]]()

    var totalCost: Double = Double.MaxValue

    var it = 1

    val samplingTimer = System.nanoTime()

    var prevModelSetOpt: Option[IntOpenHashSet] = None

    do { // outer sampling loop

      val newModelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing(costsOpt, prevModelSetOpt)

      prevModelSetOpt = newModelOpt.map(_._2)

      if (newModelOpt.isEmpty)
        return mutable.Seq[Array[Pred]]()

      sampledModels.append(newModelOpt.get._1)

      totalCost = if (ignoreParamVariables) Double.NegativeInfinity else updateMeasuredAtomsFreqsAndComputeCost(Some(newModelOpt.get._2),
        measuredAtomElis = measuredAtomsElis,
        measuredAtomEliToStatisticalFreq,
        sampledModels,
        costFctsInner = costFctsInner,
        computeCosts = true, // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
        partDerivativeComplete = true,
        update_parameterAtomVarForParamEli_forPartDerivCompl = update_parameterAtomVarForParamEli_forPartDerivCompl
      ).get._1

      if (!ignoreParamVariables) {

        java.util.Arrays.sort(deficitOrderedUncertainLiterals, deficitOrdering)

      }

      if (showProgressStats)
        println("\nSampling iteration " + it + " (of max " + maxIt + ") complete. " +
          "Current cost: " + totalCost + " (threshold: " + threshold + ")")

      it += 1

    } while (it < maxIt && (requestedNumberOfModels == -1 && totalCost > threshold ||
      requestedNumberOfModels >= 0 && sampledModels.length < requestedNumberOfModels))

    if (totalCost < threshold)
      println("Sampling complete; specified threshold reached. " + sampledModels.length + " models sampled (with replacement)\n")
    else
      stomp(-5008)

    println("Time for multi-model sampling: " + timerToElapsedMs(samplingTimer) + " ms\n")

    val sampledModelsSymbolic = sampledModels.map(model => model.map(eli => symbols(eli)))

    log("sampledModelsSymbolic:\n" + sampledModelsSymbolic.map(_.mkString(" ")).mkString("\n"))

    sampledModelsSymbolic

  }

  //@Contended
  var nogoodExchangePool = new java.util.concurrent.ConcurrentHashMap[ArrayEliUnsafe, Int /*producing thread*/ ]()

  var prevUnassi = Int.MaxValue // not precise; for statistics/debugging only

  val savePhases = savePhasesR && !diversify

  @Contended
  val passPrevious = if (savePhases) new LongArrayUnsafe(noOfAllElis, 0l, true) else null.asInstanceOf[LongArrayUnsafe]

  case class SingleSolverConf(threadNo: Int /*>=1*/ ,
                              costsOpt: Option[UncertainAtomsSeprt],
                              dependencyGraph: Int2ObjectOpenHashMap[List[Eli]],
                              progIsTight: Boolean,
                              freeEliSearchApproach: Int,
                              restartTriggerConfR: (Boolean, Int, Double, Int),
                              noHeapR: Int,
                              prep: Preparation /*<-for debugging/crosschecks only*/ ,
                              candEliCheckCapFac: Int,
                              prearrangeEliPoolR: Int,
                              rndmBranchR: Float);

  def sampleSingleRacing(costsOpt: Option[UncertainAtomsSeprt],
                         //prep: Preparation,
                         prevModelSetOpt: Option[IntOpenHashSet]): Option[(Array[Eli], IntOpenHashSet)] /*None = UNSAT */ = {

    @volatile var stopSolverThreads = false

    val progressNormalizedPerThread = mutable.HashMap[Int, Double]()

    /**
      * @author Matthias Nickles
      */
    def sampleSingle(singleSolverConf: SingleSolverConf): Option[(Array[Eli], IntOpenHashSet)] /*None: UNSAT, null = aborted */ = {

      import singleSolverConf._

      def unsat = println("\nUNSAT" + (if (verbose) "\n  (reporting: solver thread " + threadNo + ")" else ""))

      val solverTimer = System.nanoTime()

      val rngLocalL: java.util.Random = new XORShift32() // not thread-safe

      val rngLocal: RandomGen = new java.util.SplittableRandom()

      @inline def nextFloatRngLocal() = rngLocal.nextDouble()

      val sccCache = mutable.HashMap[mutable.Seq[Eli], ArrayBuffer[ArrayBuffer[Eli]]]()

      val noHeap = if (noHeapR == -1) clarkNogoods.length < 20000 && noOfPosElis < 100000 else noHeapR == 1

      val prearrangeEliPool = if (prearrangeEliPoolR <= 3) prearrangeEliPoolR else
        Math.floor(nextFloatRngLocal() / 0.25)

      var elisArranged = if (prearrangeEliPool == 0) elisArrangedR else if (prearrangeEliPool == 3) {

        val elisArrangedRClone = elisArrangedR.clone

        shuffleArray(elisArrangedRClone, rngLocal)

        elisArrangedRClone

      } else {

        elisArrangedR.sortBy({ case ((eli: Eli)) =>

          eliToNogisClark(eli).length * (if (prearrangeEliPool == 1) 1 else -1)

        })

      }

      var absElisArranged = (0 until noOfPosElis).toArray

      if (prearrangeEliPool == 3) {

        val posElisArrangedClone = absElisArranged.clone

        shuffleArray(posElisArrangedClone, rngLocal)

        posElisArrangedClone

      } else if (prearrangeEliPool != 0) {

        absElisArranged = absElisArranged.sortBy({ case ((eli: Eli)) =>

          (eliToNogisClark(eli).length + eliToNogisClark(negatePosEli(eli)).length) * (if (prearrangeEliPool == 1) 1 else -1)

        })

      }

      val nogiToNogood: ObjectArrayList[ArrayEliUnsafe] = new ObjectArrayList(clarkNogoods)

      val eliToNogis: Array[ArrayValExtensibleIntUnsafe] = eliToNogisClark.clone().map(ausf => new ArrayValExtensibleIntUnsafe(ausf.getContent.clone()))

      val activUpdateBase = initialActivBaseValue

      assert(activUpdateBase > 0f)

      val activPows = Array.ofDim[Float](5000)

      activPows(0) = 1f

      activPows(1) = activUpdateBase

      var activPow = activUpdateBase

      var exp = 2

      while (exp < activPows.length) {

        activPow *= activUpdateBase

        activPows(exp) = activPow

        exp += 1

      }

      /**
        * Float power for integral non-negative exponent (not checked) and base activUpdateBase > 0 (not checked).
        *
        * @param exponent must be >= 0
        * @return activUpdateBase to the power of exponent
        */
      @inline def powIntegralExp(exponent: Int): Float = {

        if (exponent < activPows.length)
          activPows(exponent)
        else
          Math.pow(activUpdateBase, exponent).toFloat

      }

      val restartTriggerConf: (Boolean, Int, Double, Int) = if (restartTriggerConfR._3 < 0d || restartTriggerConfR._2 == -1)
        (restartTriggerConfR._1, if (restartTriggerConfR._2 == -1) (100000 / noOfAllElis.max(1)).max(5) else
          restartTriggerConfR._2,
          if (restartTriggerConfR._3 < 0d) rngLocalL.nextGaussian() * .15d - restartTriggerConfR._3 else restartTriggerConfR._3, restartTriggerConfR._4)
      else restartTriggerConfR

      val localSingleSamplerThreadPool = if (localSolverParallelThresh == localSolverParallelThreshMax) null.asInstanceOf[ThreadPoolExecutor] else
        new ThreadPoolExecutor(2, 2, 600, TimeUnit.SECONDS,
          new LinkedBlockingQueue[Runnable]) // used for various local (within a solver thread) multithreading

      val freeEliSearchApproach4or1or5 = freeEliSearchApproach == 4 || freeEliSearchApproach == 1 // includes approach 5 (= 1 with capping)

      val unassignedAbsElisPool = if (freeEliSearchApproach == 3) {

        new IntHeapPriorityQueue(noOfPosElis * 10, new IntComparator {

          @inline override def compare(o1: Eli, o2: Eli): Int = (absEliActiv.get(o2) - absEliActiv.get(o1)).toInt

        })

      } else null.asInstanceOf[IntHeapPriorityQueue]

      if (freeEliSearchApproach == 3) (0 until noOfPosElis).foreach(unassignedAbsElisPool.enqueue(_))

      var someFreeEli1: Eli = rngLocal.nextInt(noOfAllElis.max(1)) //0.min(noOfAllElis - 1)
      var someFreeEli2: Eli = rngLocal.nextInt(noOfAllElis.max(1)) //1.min(noOfAllElis - 1)
      var someFreeEli3: Eli = rngLocal.nextInt(noOfAllElis.max(1)) //2.min(noOfAllElis - 1)
      var someFreeEli4: Eli = rngLocal.nextInt(noOfAllElis.max(1)) //3.min(noOfAllElis - 1)

      //@Contended
      //val passPrevious = if (savePhases) new LongArrayUnsafe(noOfAllElis, 0l, true) else null.asInstanceOf[LongArrayUnsafe]

      //clarkNogoods.copyToBuffer(nogiToNogood)  slower!?

      val pass: LongArrayUnsafe = new LongArrayUnsafe(noOfAllElis, 0l, true) // the partial assignment. Item == 0: eli is unassignedPosElis or doesn't hold,
      // != 0: eli holds, with orderOfEli in the ORDERBITS least significant bits, followed by decision level.

      log("solverTimer 1: " + timerToElapsedMs(solverTimer) + " ms")

      var dl = 0l // decision level (increased at each nondeterministic branching literal decision)

      var orderNo = 1l // sequence number of next eli assignment (not necessarily consecutive)

      var avgNormProgress = 0d

      val threadmxBean = ManagementFactory.getThreadMXBean()

      class NogoodRemainder(var pool: ArrayEliUnsafe) {
        // NB: constructor doesn't set the two lits, so we need to call reset (unless we know both lits must be -1)

        type V = Int

        private var hdNotsetItem: V = -1 // not used if |pool| = 2. NB: observe the order of the two lits and their treatment at jump backs after conflicts.

        private var tlNotsetItem: V = -1 // not used if |pool| = 2

        /*@inline def sortPoolBySet: Unit = {

          if (pool.size() == 2) {

            val eli0 = pool.get(0)

            if (isSetInPass(eli0)) {

              val eli1 = pool.get(1)

              if (isNotSetInPass(eli1)) {

                pool.update(1, eli0)

                pool.update(0, eli1)

              }

            }

          } else {

            var tIndex = 0

            var fIndex = pool.size - 1

            while (tIndex != fIndex) {

              val eli = pool.get(tIndex)

              if (isNotSetInPass(eli))
                tIndex += 1
              else {

                val h = pool.get(fIndex)

                pool.update(fIndex, eli)

                pool.update(tIndex, h)

                fIndex -= 1

              }

            }

          }

        }*/

        @inline def reset: Unit = { // fills hdNotsetItem and tlNotsetItem lits with UNset items (e.g., unassignedPosElis elis), unless |pool| = 2.

          //if (sortRemainderPoolProb > 0f && pool.size > 2)
          // sortPoolBySet

          if (pool.size_ != 2) {

            val ps = pool.size_

            hdNotsetItem = -1

            tlNotsetItem = -1

            var i = ps - 1

            do {

              if (isNotSetInPass(pool.get(i))) {

                if (hdNotsetItem == -1)
                  hdNotsetItem = pool.get(i)
                else if (pool.get(i) != hdNotsetItem)
                  tlNotsetItem = pool.get(i)

              }

              i -= 1

            } while (tlNotsetItem == -1 && i >= 0)

          }

        }

        @inline def getRemainingItemsCase2: (V, V) = {

          // assert(pool.size_ == 2)

          if (isSetInPass(pool.get(0))) {

            if (isSetInPass(pool.get(1)))
              (-1, -1)
            else
              (pool.get(1), -1)

          } else if (isSetInPass(pool.get(1)))
            (pool.get(0), -1)
          else
            (pool.get(0), pool.get(1))

        }

        @inline def getRemainingItems: (V, V) = {

          if (pool.size_ == 2)
            getRemainingItemsCase2
          else
            (hdNotsetItem, tlNotsetItem)

        }

        @inline def unSetItem(item: V): Boolean = {

          if (pool.size_ == 2)
            true
          else {

            if (hdNotsetItem == -1 && item != tlNotsetItem) {

              hdNotsetItem = item

              true

            } else if (tlNotsetItem == -1 && item != hdNotsetItem) {

              tlNotsetItem = item

              true

            } else
              false

          }

        }

        @inline def fillUp: Unit = {

          /*if (pool.size_ <= 2)
            tlNotsetItem = -1
          else if (pool.size_ == 3) {

            if (isNotSetInPassAndNotEq(pool.get(2), hdNotsetItem))
              tlNotsetItem = pool.get(2)
            else if (isNotSetInPassAndNotEq(pool.get(1), hdNotsetItem))
              tlNotsetItem = pool.get(1)
            else if (isNotSetInPassAndNotEq(pool.get(0), hdNotsetItem))
              tlNotsetItem = pool.get(0)
            else
              tlNotsetItem = -1

          } else*/  {

            tlNotsetItem = -1

            if (pool.size_ >= 2) {

              //if (sortRemainderPoolProb > 0f && pool.size > 2 && nextFloatRngLocal() < sortRemainderPoolProb)
              // sortPoolBySet

              var i = pool.size_ - 1

              do {

                if (pool.get(i) != hdNotsetItem && isNotSetInPass(pool.get(i))) {

                  tlNotsetItem = pool.get(i)

                  return

                }

                i -= 1

              } while (tlNotsetItem == -1 && i >= 0)

            }

          }

        }

        @inline def setItem(item: V): (V, V) = {

          if (pool.size_ == 2)
            getRemainingItemsCase2
          else {

            setItemPure(item)

            (hdNotsetItem, tlNotsetItem)  // recall that these aren't meaningful if pool.size_ == 2

          }

        }

        @inline def setItemPure(item: V): Unit = {

          if (pool.size_ == 2)
            getRemainingItemsCase2
          else {

            if (item == hdNotsetItem) {

              if (tlNotsetItem != -1) {

                hdNotsetItem = tlNotsetItem

                fillUp

              } else
                hdNotsetItem = -1

            } else if (item == tlNotsetItem) {

              fillUp

            }

          }

        }

      }

      @inline def isSetInPass(eli: Eli): Boolean = pass.get(eli) != 0l

      @inline def isNotSetInPass(eli: Eli): Boolean = pass.get(eli) == 0l

      //@inline def isNotSetInPassAndNotEq(eli: Eli, celi: Eli): Boolean = eli != celi && pass.get(eli) == 0l

      @inline def isAbsSetInPass(eli: Eli): Boolean = {

        pass.get(eli) != 0l || {

          if (eli < posNegEliBoundary)
            pass.get(eli + posNegEliBoundary) != 0l
          else
            pass.get(eli - posNegEliBoundary) != 0l

        }

      }

      @inline def isAbsNotSetInPassInt(eli: Eli): Int = {

        if (pass.get(eli) != 0l || {

          if (eli < posNegEliBoundary)
            pass.get(eli + posNegEliBoundary) != 0l
          else
            pass.get(eli - posNegEliBoundary) != 0l

        }) 0 else 1

      }

      @inline def setInPass(eli: Eli) = { // must be the only way (after preprocessing/initialization) of assigning True

        //assert(!isSetInPass(eli))  // must hold when calling this function!

        //assert(orderNo > 0)

        pass.update(eli, orderNo + (dl << ORDERBITS))

        orderNo += 1l

        if (freeEliSearchApproach4or1or5) {

          if (eli == someFreeEli1)
            someFreeEli1 = rngLocal.nextInt(noOfAllElis)
          else if (eli == someFreeEli2)
            someFreeEli2 = rngLocal.nextInt(noOfAllElis)
          else if (eli == someFreeEli3)
            someFreeEli3 = rngLocal.nextInt(noOfAllElis)
          else if (eli == someFreeEli4)
            someFreeEli4 = rngLocal.nextInt(noOfAllElis)

        }

      }

      @inline def clearInPass(eli: Eli) = { // must be the only way (after preprocessing/initialization) of assigning False

        //assert(isSetInPass(eli))  // must hold when calling this function!

        if (savePhases)
          passPrevious.update(eli, pass.get(eli))

        pass.update(eli, 0l)

        orderNo -= 1l

        if (freeEliSearchApproach == 3)
          unassignedAbsElisPool.enqueue(absEli(eli))
        else if (freeEliSearchApproach4or1or5) {

          if (absEliActiv.get(absEli(eli)) > absEliActiv.get(absEli(someFreeEli1)))
            someFreeEli1 = eli
          else if (absEliActiv.get(absEli(eli)) > absEliActiv.get(absEli(someFreeEli2)))
            someFreeEli2 = eli
          else if (absEliActiv.get(absEli(eli)) > absEliActiv.get(absEli(someFreeEli3)))
            someFreeEli3 = eli
          else if (absEliActiv.get(absEli(eli)) > absEliActiv.get(absEli(someFreeEli4)))
            someFreeEli4 = eli

        }

      }

      @inline def orderOfEli(eli: Eli) = pass.get(eli) & ((1l << ORDERBITS) - 1l)

      @inline def decisionLevelOfEli(eli: Eli) = pass.get(eli) >>> ORDERBITS // for large bulk compare operations, use, e.g., pass(eli) > dl << ORDERBITS

      var forceElis = new it.unimi.dsi.fastutil.ints.IntRBTreeSet() /*new ArrayEliUnsafe(noOfAllElis * 100)*/
      // ^ on the heap, the next batch of deductively inferable literals. Not used if noHeap
      //var forceElisSize = 0

      var conflictNogi = -1

      class ObjectArrayListUS[K] extends it.unimi.dsi.fastutil.objects.ObjectArrayList[K] {

        @inline def get_(index: Int): K = a(index)

      }

      val nogiToRemainder = new ObjectArrayListUS[NogoodRemainder]() /* per each nogood */

      val htEliToNogis = if (skipNogisHTElisInBCP) new Int2ReferenceOpenHashMap[IntOpenHashSet]() else null.asInstanceOf[Int2ReferenceOpenHashMap[IntOpenHashSet]]

      if (skipNogisHTElisInBCP) {

        var i = noOfAllElis - 1

        while (i >= 0) {

          htEliToNogis.put(i, new IntOpenHashSet())

          i -= 1

        }

      }

      @inline def addNogiToHT2Nogis(htEli: Eli, nogi: Nogi): Unit = {

        if (htEli != -1)
          htEliToNogis.get(htEli).add(nogi)

      }

      @inline def checkFireNogood(remaining2InNogood: (Eli, Eli), nogi: Nogi): Unit = {

        if (remaining2InNogood._1 == -1)
          conflictNogi = nogi
        else if (remaining2InNogood._2 == -1) { // the only remaining unassignedPosElis eli ._1 is unit resulting

          if (noHeap)
            setEliWithNogoodUpdates(negateEli(remaining2InNogood._1))
          else {

            forceElis.add(negateEli(remaining2InNogood._1))
            //forceElis.update(forceElisSize, negateEli(rem._1))
            //forceElisSize += 1

          }

        }

      }

      @inline def setEliWithNogoodUpdatesPar(eli: Eli, il: Int) = {

        // TODO (possible?): skipNogisHTElisInBCP with parallel traversal of nogisWithHTEli (note: there is a spliterator for nogisWithHTEli but might not be easy to effectively linearize results into hts)

        val nweh = il / 2

        var i = 0

        val cdl = new CountDownLatch(2)

        localSingleSamplerThreadPool.execute(new Runnable() {
          @inline override def run(): Unit = {

            while (i < nweh) {

              nogiToRemainder.get_(eliToNogis(eli).buffer.get(i)).setItemPure(eli)

              i += 1

            }

            cdl.countDown()

          }
        })

        localSingleSamplerThreadPool.execute(new Runnable() {
          @inline override def run(): Unit = {

            var j = nweh

            while (j < il) {

              nogiToRemainder.get_(eliToNogis(eli).buffer.get(j)).setItemPure(eli)

              j += 1

            }

            cdl.countDown()

          }
        })

        cdl.await()

        i = 0

        while (i < il && conflictNogi == -1) { // with noHeap = false, we need a separate loop here as otherwise checkFireNogood would operate with incompletely updated remainders,
          // which would lead to wrong results (also see same pattern in method jumpBack)

          //checkFireNogood(nogiToRemainder.get_(eliToNogisTemp(eli).buffer.get(i)).getRemainingItems, eliToNogisTemp(eli).buffer.get(i))
          val remaining2InNogood = nogiToRemainder.get_(eliToNogis(eli).buffer.get(i)).getRemainingItems

          if (remaining2InNogood._1 == -1)
            conflictNogi = eliToNogis(eli).buffer.get(i)
          else if (remaining2InNogood._2 == -1) { // the only remaining unassignedPosElis eli ._1 is unit resulting

            if (noHeap)
              setEliWithNogoodUpdates(negateEli(remaining2InNogood._1))
            else {

              forceElis.add(negateEli(remaining2InNogood._1))
              //forceElis.update(forceElisSize, negateEli(rem._1))
              //forceElisSize += 1

            }

          }

          i += 1

        }

      }

      @inline def setEliWithNogoodUpdates(eli: Eli): Unit = {

        if (isNotSetInPass(eli)) {

          setInPass(eli)

          //assert(eli < eliToNogis.length, "FFFThread = "  + threadNo)

          val il = eliToNogis(eli).length

          if (il < localSolverParallelThresh) {

            var i = 0

            if (noHeap) {

              if (!skipNogisHTElisInBCP) {

                while (i < il) {

                  nogiToRemainder.get_(eliToNogis(eli).buffer.get(i)).setItemPure(eli)

                  i += 1

                }

                i = 0

                while (i < il && conflictNogi == -1) { // with noHeap, we need a separate loop here as otherwise we would possibly operate
                  // with incompletely updated remainders which would lead to wrong results (also see same pattern in method jumpBack)

                  val remainder: (NogoodRemainder#V, NogoodRemainder#V) =
                    nogiToRemainder.get_(eliToNogis(eli).buffer.get(i)).getRemainingItems

                  if (remainder._1 == -1)
                    conflictNogi = eliToNogis(eli).buffer.get(i)
                  else if (remainder._2 == -1)
                    setEliWithNogoodUpdates(negateEli(remainder._1))

                  i += 1

                }

              } else {

                val nogisWithHTEli = htEliToNogis.get(eli)

                if (nogisWithHTEli != null) {

                  val hts = Array.ofDim[(Eli, Eli, Nogi)](nogisWithHTEli.size())

                  val it: IntIterator = nogisWithHTEli.iterator

                  while (it.hasNext) {

                    val nogiWithHTEli: Nogi = it.nextInt()

                    val remainder: (NogoodRemainder#V, NogoodRemainder#V) = nogiToRemainder.get_(nogiWithHTEli).setItem(eli)

                    hts(i) = (remainder._1, remainder._2, nogiWithHTEli)
                    //assert(newcomer != eli)

                    addNogiToHT2Nogis(remainder._2, nogiWithHTEli)

                    i += 1

                  }

                  htEliToNogis.put(eli, new IntOpenHashSet())

                  i = 0

                  while (i < hts.length && conflictNogi == -1) {

                    if (hts(i)._1 == -1)
                      conflictNogi = hts(i)._3
                    else if (hts(i)._2 == -1)
                      setEliWithNogoodUpdates(negateEli(hts(i)._1))

                    i += 1

                  }

                }

              }

            } else { // TODO?: Make skipNogisHTElisInBCP work with !noHeap (tricky - attempt 24-11-2018 11:21 lead to out-of-order errors in conflict handling)

              while (i < il && conflictNogi == -1) {

                val remainder: (NogoodRemainder#V, NogoodRemainder#V) = nogiToRemainder.get_(eliToNogis(eli).buffer.get(i)).setItem(eli)

                if (remainder._1 == -1)
                  conflictNogi = eliToNogis(eli).buffer.get(i)
                else if (remainder._2 == -1) { // the only remaining unassignedPosElis eli ._1 is unit resulting

                  forceElis.add(negateEli(remainder._1))
                  //forceElis.update(forceElisSize, negateEli(rem._1))
                  //forceElisSize += 1

                }

                i += 1

              }

            }

          } else
            setEliWithNogoodUpdatesPar(eli, il)

        }

      }

      var nogi: Nogi = 0

      val ntngl = nogiToNogood.size

      while (nogi < ntngl) {

        val nogood = nogiToNogood.get(nogi)

        if (nogood.size_ == 0) {

          unsat

          return None

        }

        nogiToRemainder.add {

          if (!noHeap && resolveFactsInitially && nogood.size() == 1) { // getting facts out of the way

            forceElis.add(negateEli(nogood.get(0)))
            //forceElis.update(forceElisSize, negateEli(nogood.get(0)))
            //forceElisSize += 1

          }

          val remainder = new NogoodRemainder(pool = nogood)

          remainder.reset

          if (skipNogisHTElisInBCP) {

            val (remEliH, remEliT) = remainder.getRemainingItems

            addNogiToHT2Nogis(remEliH, nogi)

            addNogiToHT2Nogis(remEliT, nogi)

          }

          //checkFireNogood(rem, nogi = nogi)  // we can't do this here since the remainders aren't completely known yet, which would
          // lead to errors if checkFireNogood actually fires.

          remainder

        }

        nogi += 1

      }

      if (noHeap && resolveFactsInitially) {

        nogi = 0

        while (nogi < ntngl) {

          val nogood = nogiToNogood.get(nogi)

          if (nogood.size() == 1) {

            setEliWithNogoodUpdates(negateEli(nogood.get(0)))

          }

          nogi += 1

        }

      }

      var firstRecordedNogi = -1

      var noOfConflictsTotal = 0

      var noOfConflictsAfterRestart = 0

      var noOfTrialsAtLastRestart = 0

      var recentConflictsCount = 0

      log("solverTimer 2: " + timerToElapsedMs(solverTimer) + " ms")

      @inline def activUpVar(posEli: sharedDefs.Eli) = {

        absEliActiv.update(posEli, absEliActiv.get(posEli) + powIntegralExp(/*noOfConflictsTotal*/ noOfConflictsAfterRestart))

      }

      @inline def incActivNogoodVarsUnsafe(nogood: ArrayEliUnsafe, nogi: Nogi, until: Long) = {

        if (activUpdateBase != 1f) {

          var i = until - 1

          while (i >= 0) {

            if (nogood.get(i) != -1)
              activUpVar(absEli(nogood.get(i)))

            i -= 1

          }

        }

      }

      def conflictAnalysis(pivotNogi: Nogi):
      (Long /*new decision level to jump to*/ , ArrayEliUnsafe /*learned nogood*/ , Int /*sigmaEli*/ ) = {

        var pivotNogood = nogiToNogood.get(pivotNogi)

        val accumulatedNogoodBuilder = new ArrayValExtensibleIntUnsafe(pivotNogood.clone(0))

        var lp = true

        var sigmaEli = -1

        var k = -1l

        while (lp) {

          var accI = accumulatedNogoodBuilder.length - 1

          var sigmaOrder = -1l

          while (accI >= 0) {

            val eli = accumulatedNogoodBuilder.get(accI)

            if (eli != -1) {

              val orderEli = orderOfEli(eli)

              if (orderEli > sigmaOrder) {

                sigmaOrder = orderEli

                sigmaEli = eli

              }

            }

            accI -= 1

          }

          k = 0

          var pi = accumulatedNogoodBuilder.length - 1

          var shotOutSigma = -1l

          while (pi >= 0) {

            val eliInPivotNogood = accumulatedNogoodBuilder.get(pi)

            if (eliInPivotNogood != -1) {

              if (eliInPivotNogood != sigmaEli) {

                val dl = decisionLevelOfEli(eliInPivotNogood)

                if (dl > k)
                  k = dl

              } else {

                shotOutSigma = pi

                accumulatedNogoodBuilder.buffer.update(pi, -1)

              }

            }

            pi -= 1

          }

          val levelOfSigma = decisionLevelOfEli(sigmaEli)

          //log(" levelOfSigma: " + levelOfSigma)

          if (k == levelOfSigma) { // we haven't found a UIP yet

            val sigmaNot = negateEli(sigmaEli)

            //log(" sigmaNot: " + sigmaNot)

            val orderOfSigma = sigmaOrder

            //val orderOfSigma = if (sigmaSeq0 < 0) 0 else sigmaSeq0

            //log(" orderOfSigma: " + orderOfSigma)

            //log(" pass: " + pass.mkString(","))

            assert(orderOfSigma != 0)

            //since current sigmaEli is not a decision literal, so there must have been some nogood which has "fired" sigmaEli:

            val candNogis = eliToNogis(sigmaNot).buffer

            val candNogisLength = eliToNogis(sigmaNot).length

            var candNogisI = 0 //rngLocal.nextInt(candNogisLength)

            val candNogisIStart = candNogisI

            var eps: Nogi = -1

            while (candNogisI < candNogisLength && eps == -1) {

              val candNogi: Nogi = candNogis.get(candNogisI)

              val candNogood: ArrayEliUnsafe = nogiToNogood.get(candNogi)

              incActivNogoodVarsUnsafe(candNogood, candNogi, candNogood.size_) // inspired by BerkMin

              val fa: Boolean = {

                var i = 0

                val cl = candNogood.size_

                while (i < cl) {

                  val eli = candNogood.get(i)

                  if (eli == sigmaNot)
                    i += 1
                  else {

                    val eliOrder = orderOfEli(eli)

                    if (eliOrder == 0 /*<- effectively isSetInPass(eli)*/ || eliOrder >= orderOfSigma)
                      i = Int.MaxValue
                    else
                      i += 1

                  }

                }

                i < Int.MaxValue

              }

              if (fa)
                eps = candNogi
              else
                candNogisI += 1

              if (candNogisI >= candNogisLength)
                candNogisI = 0

              assert(eps != -1 || candNogisI != candNogisIStart) // important check, don't disable! If this check fails,
              // this typically (but not necessarily) indicates that elis are assigned out of order, e.g., an neg(eli) is set to True before
              // the other elis within a unit-resulting nogood have been set to True.

            }

            val ngEps = nogiToNogood.get(eps)

            val accLenOld = accumulatedNogoodBuilder.length

            var ngEpsI = ngEps.size() - 1

            while (ngEpsI >= 0) {

              val ngEpsEli = ngEps.get(ngEpsI)

              if (ngEpsEli != sigmaNot && !accumulatedNogoodBuilder.contains(ngEpsEli, until = accLenOld.toInt))
                accumulatedNogoodBuilder.append(ngEpsEli)

              ngEpsI -= 1

            }

          } else {

            accumulatedNogoodBuilder.buffer.update(shotOutSigma, sigmaEli) // we restore sigmaEli

            lp = false

          }
        }

        val nogoodFinal = accumulatedNogoodBuilder.getContentUnsafeExceptInt(except = -1)

        ((k, nogoodFinal, sigmaEli))

      }

      var geomNoOfConflictsBeforeRestart = restartTriggerConf._2

      var noOfRestarts = 0

      val clearInJumpBackTasks = new util.ArrayList[Runnable]()

      var nogisWithEliToClear: ArrayValExtensibleIntUnsafe = null

      var nweh = -1

      var eliToClear = -1

      var cdlcl = null.asInstanceOf[CountDownLatch]

      clearInJumpBackTasks.add(new Runnable {

        override def run(): Unit = {

          var i = nweh - 1

          while (i >= 0) {

            nogiToRemainder.get_(nogisWithEliToClear.get(i)).unSetItem(eliToClear)

            i -= 1

          }

          cdlcl.countDown()

        }

      })

      clearInJumpBackTasks.add(new Runnable {
        override def run(): Unit = {

          var i = nweh

          var il = nogisWithEliToClear.length

          while (i < il) {

            nogiToRemainder.get_(nogisWithEliToClear.get(i)).unSetItem(eliToClear)

            i += 1

          }

          cdlcl.countDown()

        }
      })

      @inline def jumpBack(newLevel: Long) = {

        log("Jumping back to decision level " + newLevel)

        // We remove everything with a decision level > newLevel

        conflictNogi = -1

        //forceElisSize = 0
        forceElis.clear()

        if (newLevel == -1) { // we restart from scratch

          dl = 0

          noOfConflictsAfterRestart = 0

          /*var eli = 0

          while (eli < noOfPosElis) {

            absEliActiv.update(eli, 0f)

            eli += 1

          }*/

        } else {

          dl = newLevel

          noOfConflictsAfterRestart += 1

          noOfConflictsTotal += 1

        }

        recentConflictsCount += 1

        //nogisToReset.clear()

        val resetNogisHTElis = newLevel == -1 && noOfRestarts % 5 == 0

        var eli = 0

        while (eli < noOfPosElis) {

          @inline def clear(eli: Eli) = {

            //assert(isSetInPass(eli))

            clearInPass(eli)

            val nogisWithEli: ArrayValExtensibleIntUnsafe = eliToNogis(eli)

            if (nogisWithEli.length < localSolverParallelThresh) {

              var i = nogisWithEli.length - 1

              while (i >= 0) {

                val nogi = nogisWithEli.get(i)

                val rem = nogiToRemainder.get_(nogi)

                if (rem.unSetItem(eli))
                  if (skipNogisHTElisInBCP && !resetNogisHTElis) { // this block never removes any nogis from htEliToNogis, so htEliToNogis might contain
                    // redundancies. But we remove and rebuild at certain restart-jumpBacks (see below)

                    val (hdNotsetItem, tlNotsetItem) = rem.getRemainingItems

                    if (hdNotsetItem != -1) {

                      htEliToNogis.get(hdNotsetItem).add(nogi)

                      if (tlNotsetItem != -1)
                        htEliToNogis.get(tlNotsetItem).add(nogi)

                    }

                  }

                i -= 1

              }

            } else {

              nogisWithEliToClear = nogisWithEli

              nweh = nogisWithEli.length / 2

              eliToClear = eli

              cdlcl = new CountDownLatch(2)

              localSingleSamplerThreadPool.execute(clearInJumpBackTasks.get(0))

              localSingleSamplerThreadPool.execute(clearInJumpBackTasks.get(1))

              cdlcl.await()

            }

          }

          if (decisionLevelOfEli(eli) > newLevel && isSetInPass(eli)) // NB: decisionLevelOfEli doesn't check if eli is set
            clear(eli)
          else if (decisionLevelOfEli(negatePosEli(eli)) > newLevel && isSetInPass(negatePosEli(eli)))
            clear(negatePosEli(eli))

          eli += 1

        }

        if (resetNogisHTElis && skipNogisHTElisInBCP) {

          log(" Clearing htEliToNogis...")

          htEliToNogis.clear()

          var eli = 0

          while (eli < noOfAllElis) {

            htEliToNogis.put(eli, new IntOpenHashSet())

            eli += 1

          }

          var nogi = nogiToNogood.size - 1

          while (nogi >= 0) {

            val (hdNotsetItem, tlNotsetItem) = nogiToRemainder.get_(nogi).getRemainingItems

            if (hdNotsetItem != -1) {

              htEliToNogis.get(hdNotsetItem).add(nogi)

              if (tlNotsetItem != -1)
                htEliToNogis.get(tlNotsetItem).add(nogi)

            }

            nogi -= 1

          }

        }


      }

      @inline def addNogood(newNogood: ArrayEliUnsafe): Nogi = {

        //assert(!newNogood.contains(-1))

        val newNogi = nogiToNogood.size

        if (firstRecordedNogi == -1)
          firstRecordedNogi = newNogi

        nogiToNogood.add(newNogood)

        var i = newNogood.size() - 1

        while (i >= 0) {

          eliToNogis(newNogood.get(i)).append(newNogi)

          i -= 1

        }

        val newNogoodRemainder = new NogoodRemainder(pool = newNogood)

        nogiToRemainder.add(newNogoodRemainder)

        newNogoodRemainder.reset

        val (remEliT, remEliH) = newNogoodRemainder.getRemainingItems

        if (skipNogisHTElisInBCP) {

          addNogiToHT2Nogis(remEliT, nogi)

          addNogiToHT2Nogis(remEliT, nogi)

        }

        checkFireNogood((remEliT, remEliH), newNogi)

        if (maxCompetingSolverThreads > 1 && nogoodExchangeProbability > 0.00001f)
          nogoodExchangePool.put(newNogood, threadNo)

        incActivNogoodVarsUnsafe(newNogood, newNogi, newNogood.size_)

        newNogi

      }

      @inline def removeRecordedNogoods(firstNogi: Nogi, lastNogi: Nogi) = { // TODO: improve speed

        assert(firstRecordedNogi >= 0 && firstNogi >= firstRecordedNogi && lastNogi >= firstNogi && lastNogi < nogiToNogood.size)

        val noToRemove = lastNogi - firstNogi + 1

        var nogiToRemove = lastNogi

        while (nogiToRemove >= firstNogi) {

          nogiToNogood.remove(nogiToRemove) // expensive but not as expensive as it seems

          nogiToRemainder.remove(nogiToRemove)

          nogiToRemove -= 1

        }

        var eli = 0

        while (eli < noOfAllElis) {

          val nogisWithEli: ArrayValExtensibleIntUnsafe = eliToNogis(eli)

          nogisWithEli.removeIntItemsRange(firstNogi, lastNogi)

          var k = 0

          while (k < nogisWithEli.length) {

            if (nogisWithEli.buffer.get(k) > lastNogi)
              nogisWithEli.buffer.update(k, nogisWithEli.buffer.get(k) - noToRemove)

            k += 1

          }

          if (skipNogisHTElisInBCP) {

            val nogisWithHTEli = htEliToNogis.get(eli)

            val nogisWithHTEliNew = new IntOpenHashSet()

            if (nogisWithHTEli != null) {

              val nogisWithHTEliIt = nogisWithHTEli.iterator

              while (nogisWithHTEliIt.hasNext) {

                val nx = nogisWithHTEliIt.nextInt()

                if (nx < firstNogi)
                  nogisWithHTEliNew.add(nx)
                else if (nx > lastNogi)
                  nogisWithHTEliNew.add(nx - nogiToRemove)

              }

              htEliToNogis.put(eli, nogisWithHTEliNew)

            } else
              htEliToNogis.put(eli, nogisWithHTEliNew)

          }

          eli += 1

        }

      }

      var modelOpt: Option[(Array[Eli], IntOpenHashSet)] = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

      val noOfElisInAllNogoods = new Int2IntOpenHashMap()

      @inline def noOfConflictsBeforeRestart = ((nogiToNogood.size - firstRecordedNogi) * restartTriggerConf._3).max(2)

      while (modelOpt == null && !stopSolverThreads) { // bounce-back loop; if program is tight or sat-mode, there is only a single iteration

        var completeModuloConflict = false

        var trials = 0

        var entryFreeEliSearch = 0 //rngLocal.nextInt(noOfPosElis)

        def findFreeEli: (Int, Float) = { // decision heuristics & parameter eli decision using differentiation (partial derivatives)

          val removedElisFreeOpt = if (!variableOrNogoodElimConfig._1 || variableOrNogoodElimConfig._5) None
          else
            removedNogoodsPerAtomOpt.flatMap(_.keys.find(!isAbsSetInPass(_)))

          if (removedElisFreeOpt.isDefined)
            return (removedElisFreeOpt.get, 1f)
          else {

            if (!ignoreParamVariables) {

              // We check the parameter atoms (random variables) in the order provided by the sorted partial derivatives (over multiple atoms, this
              // implicitly gives the gradient):

              var i = 0

              val il = deficitOrderedUncertainLiterals.length / 2 // each variable appears twice, we only need their lowest ranked literals

              while (i < il) {

                val uncertainEli = deficitOrderedUncertainLiterals(i)

                if (!isAbsSetInPass(uncertainEli))
                  return (uncertainEli, 1f)

                i += 1

              }

            }

            // We can let rndmBranchR depend from some statistics, such as #conflicts, e.g. like this:
            // rndmBranchR = 0.2f - 1f / Math.sqrt(noOfConflictsAfterRestart + 300).toFloat
            // But in initial experiments no such expression was found that'd lead to better results.

            val rndmBranch = if (rndmBranchR >= 0f)
              rndmBranchR
            else if ((System.currentTimeMillis() / 1000) % 3 == 0) -rndmBranchR else 0.00001f

            if (nextFloatRngLocal() < rndmBranch) {

              val freeEli = rngLocal.nextInt(noOfPosElis)

              if (!isAbsSetInPass(freeEli))
                return (freeEli, 1f)

            } else {

              var freeEli = -1

              var freeVarActiv = Float.MinValue

              val noise = 0.0001f // note: noise = 0 overrides phase saving

              val tol = 0.1f

              @inline def findFreeVarInAbsElisArranged = {

                var posEliI = 0

                var maxIt = (candEliCheckCapFac * noOfConflictsAfterRestart).max(1) //if (noOfConflictsAfterRestart == 0) 1 else candEliCheckCapFac * noOfPosElis

                while (posEliI < noOfPosElis && (maxIt > 0 || freeEli == -1)) {

                  val posEli = absElisArranged(posEliI)

                  if (!isAbsSetInPass(posEli) && absEliActiv.get(posEli) > freeVarActiv) {

                    freeEli = posEli

                    freeVarActiv = absEliActiv.get(posEli)

                    maxIt -= 1

                  }

                  posEliI += 1

                }

              }

              @inline def findFreeVarInElisArranged = {

                var eliI = 0

                var maxIt = (candEliCheckCapFac * noOfConflictsAfterRestart).max(1) // if (noOfConflictsAfterRestart == 0) 1 else candEliCheckCapFac * noOfPosElis

                while (eliI < noOfAllElis && (maxIt > 0 || freeEli == -1)) {

                  val eli = elisArranged(eliI)

                  if (!isAbsSetInPass(eli) && absEliActiv.get(absEli(eli)) > freeVarActiv) {

                    freeEli = eli

                    freeVarActiv = absEliActiv.get(absEli(eli))

                    maxIt -= 1

                  }

                  eliI += 1

                }

              }

              @inline def findFreeVarInNogoods(ignoreActiv: Boolean) = {

                // if ignoreActiv=true, we count elis in all(!) nogoods (Clark nogoods and any new ones)

                var nogi = firstRecordedNogi

                var nogil = nogiToNogood.size()

                noOfElisInAllNogoods.clear()

                if (firstRecordedNogi != -1) {

                  while (nogi < nogil) { // if ignoreActiv = false: similarly to BerkMin (but not identical), we first consider activity
                    // levels of variables (not literals) in the most recently added nogoods

                    val nogood = nogiToNogood.get(nogi)

                    var eliInNogoodIndex = nogood.size_ - 1

                    while (eliInNogoodIndex >= 0) {

                      val candEli: Eli = nogood.get(eliInNogoodIndex)

                      if (ignoreActiv)
                        noOfElisInAllNogoods.put(candEli, noOfElisInAllNogoods.getOrDefault(candEli, 0) + 1)

                      if (!ignoreActiv && !isAbsSetInPass(candEli) && absEliActiv.get(absEli(candEli)) > freeVarActiv) {

                        freeEli = candEli

                        freeVarActiv = absEliActiv.get(absEli(candEli))

                      }

                      eliInNogoodIndex -= 1

                    }

                    nogi += 1

                  }

                }

                if (freeEli == -1) {

                  nogi = 0

                  if (firstRecordedNogi != -1) nogil = firstRecordedNogi

                  while (nogi < nogil) { //similar to BerkMin (but not identical), we look at most recently added nogoods first

                    val nogood = nogiToNogood.get(nogi)

                    var eliInNogoodIndex = nogood.size_ - 1

                    while (eliInNogoodIndex >= 0) {

                      val candEli: Eli = nogood.get(eliInNogoodIndex)

                      if (ignoreActiv)
                        noOfElisInAllNogoods.put(candEli, noOfElisInAllNogoods.getOrDefault(candEli, 0) + 1)

                      if (!ignoreActiv && !isAbsSetInPass(candEli) && absEliActiv.get(absEli(candEli)) > freeVarActiv) {

                        freeEli = candEli

                        freeVarActiv = absEliActiv.get(absEli(candEli))

                      }

                      eliInNogoodIndex -= 1

                    }

                    nogi += 1

                  }


                }

                if (ignoreActiv && !noOfElisInAllNogoods.isEmpty) {

                  freeEli = -1 // noOfElisInAllNogoods.values.toIntArray.maxBy((tuple: (sharedDefs.Eli, Int)) => tuple._2 * ( if(isAbsSetInPass(tuple._1)) 0 else 1))._1

                  var freeEliCount = 0

                  val elisCountsIt = noOfElisInAllNogoods.int2IntEntrySet().iterator()

                  while (elisCountsIt.hasNext) {

                    val eliCount: Int2IntMap.Entry = elisCountsIt.next()

                    if (!isAbsSetInPass(eliCount.getIntKey)) {

                      if (eliCount.getIntValue > freeEliCount) {

                        freeEli = eliCount.getIntKey

                        freeEliCount = eliCount.getIntValue

                      }

                    }

                  }

                }

              }

              if (freeEliSearchApproach == 6) {

                freeEli = rngLocal.nextInt(noOfAllElis)

                if (!isAbsSetInPass(freeEli))
                  return (freeEli, 1f - noise) // we need noise > 0 to consider any saved phase

              } else if (freeEliSearchApproach4or1or5) {

                val r1 = isAbsNotSetInPassInt(someFreeEli1) * absEliActiv.get(absEli(someFreeEli1))

                val r2 = isAbsNotSetInPassInt(someFreeEli2) * absEliActiv.get(absEli(someFreeEli2))

                val r3 = isAbsNotSetInPassInt(someFreeEli3) * absEliActiv.get(absEli(someFreeEli3))

                val r4 = isAbsNotSetInPassInt(someFreeEli4) * absEliActiv.get(absEli(someFreeEli4))

                if (r1 > r2 && r1 > r3 && r1 > r4) return (someFreeEli1, 0.5f)
                if (r2 > r1 && r2 > r3 && r2 > r4) return (someFreeEli2, 0.5f)
                if (r3 > r1 && r3 > r2 && r3 > r4) return (someFreeEli3, 0.5f)
                if (r4 > r1 && r4 > r2 && r4 > r3) return (someFreeEli4, 0.5f)

                if (freeEliSearchApproach == 1) { // this is also the branch used with freeEliSearchApproachR = 5

                  findFreeVarInAbsElisArranged

                  if (freeEli != -1)
                    return (freeEli, 0.5f)

                } else {

                  findFreeVarInNogoods(ignoreActiv = false)

                  if (freeEli != -1)
                    return (freeEli, 0.5f)

                }

              } else if (freeEliSearchApproach == 8) {

                findFreeVarInNogoods(ignoreActiv = true)

                if (freeEli != -1)
                  return (freeEli, 1f - noise)

              } else if (freeEliSearchApproach == 2) {

                findFreeVarInAbsElisArranged

                if (freeEli != -1)
                  return (freeEli, 0.5f)

              } else if (freeEliSearchApproach == 7) {

                findFreeVarInElisArranged

                if (freeEli != -1)
                  return (freeEli, 1f - noise) // see above

              } else if (freeEliSearchApproach == 0) {

                findFreeVarInNogoods(ignoreActiv = false)

                if (freeEli != -1)
                  return (freeEli, 0.5f)

              } else if (freeEliSearchApproach == 8) {

                findFreeVarInNogoods(ignoreActiv = true)

                if (freeEli != -1)
                  return (freeEli, 0.5f)

              } else if (freeEliSearchApproach == 3) {

                while (freeEli == -1 && !unassignedAbsElisPool.isEmpty) {

                  val pe = unassignedAbsElisPool.dequeueInt() //.dequeueLastInt()

                  if (!isAbsSetInPass(pe))
                    freeEli = pe

                }

                if (freeEli == -1)
                  freeEli = rngLocal.nextInt(noOfPosElis)

                if (!isAbsSetInPass(freeEli))
                  return (freeEli, 0.5f)

              } else
                stomp(-5009, "Non-existing free eli search approach: " + freeEliSearchApproach)

            }

          }

          (-1, 0f)

        }

        @inline def unitProps = { // BCP

          while (!forceElis.isEmpty && conflictNogi == -1) {

            val eli = forceElis.lastInt()

            forceElis.remove(eli) //removeLastInt()

            setEliWithNogoodUpdates(eli)


          }

          /*while (forceElisSize > 0 && conflictNogi == -1) {

            forceElisSize -= 1

            val eli = forceElis.get(forceElisSize)

            setEliWithNogoodUpdates(eli)

          }*/

        }

        var restartTimerMS = if (restartTriggerConf._4 >= 0) System.currentTimeMillis() else -1

        while (!completeModuloConflict && !stopSolverThreads) { // inner loop (assignments) ----------------------------

          trials += 1

          //assert(orderNo + forceElisSize <= maxOrderNo, "Error: Maximum order exceeded")

          if (!noHeap)
            unitProps

          if (conflictNogi == -1) {

            completeModuloConflict = orderNo - 1l == noOfPosElis

            if (!completeModuloConflict) {

              // Branching...

              val (freeEli, enforceProb) = findFreeEli // invokes heuristics or finds free parameter literal using differentiation

              if (freeEli != -1) {

                val branchingEli: Eli = if (savePhases && enforceProb < 1f) {

                  if (passPrevious.get(freeEli) != 0l)
                    freeEli
                  else
                    negateEli(freeEli)

                } else if (diversify) {

                  if (nextFloatRngLocal() <= 0.5f /*rngLocal.nextBoolean() <- inaccurate */ )
                    freeEli
                  else
                    negateEli(freeEli)

                } else if (enforceProb == 1f || nextFloatRngLocal() < enforceProb)
                  freeEli
                else
                  negateEli(freeEli)

                dl += 1

                //assert(dl < maxDecisions, "ERROR: Maximum number of decision levels exceeded: " + dl)

                if (!stopSolverThreads) {

                  setEliWithNogoodUpdates(branchingEli)

                  if (restartTriggerConf._2 != -2 && ((restartTriggerConf._1 && noOfConflictsAfterRestart > 0 &&
                    Math.sqrt(dl + noOfConflictsAfterRestart) > geomNoOfConflictsBeforeRestart ||
                    !restartTriggerConf._1 && noOfConflictsAfterRestart > noOfConflictsBeforeRestart || restartTriggerConf._4 >= 0 && System.currentTimeMillis() - restartTimerMS > restartTriggerConf._4))) {

                    if (showProgressStats)
                      println("Restarting... (Thread: " + threadNo + "$, #conflicts: " + noOfConflictsTotal +
                        ", #restarts: " + noOfRestarts + " @ " + timerToElapsedMs(solverTimer) / 1000 + " sec, rndmBranchR = " + rndmBranchR +
                        ", thread time: " + (if (threadmxBean.isCurrentThreadCpuTimeSupported) (threadmxBean.getCurrentThreadCpuTime / 1e9).toInt + "sec" else "??") + ")")

                    noOfRestarts += 1

                    noOfTrialsAtLastRestart = trials

                    if (restartTriggerConf._4 >= 0)
                      restartTimerMS = System.currentTimeMillis()

                    if (restartTriggerConf._1)
                      geomNoOfConflictsBeforeRestart = Math.pow(restartTriggerConf._3, noOfRestarts.toDouble).toInt

                    if (removeLearnedNogoods > 0 && firstRecordedNogi >= 0 && firstRecordedNogi < nogiToNogood.size) {

                      val noOfNogoodsToRemove = (Math.sqrt(nogiToNogood.size - firstRecordedNogi) * removeLearnedNogoods).toInt.max(1).min(nogiToNogood.size - firstRecordedNogi)

                      log("Removing " + noOfNogoodsToRemove + " learned nogoods...")

                      val removeNogisByActivityRank = false

                      if (removeNogisByActivityRank) {

                        val nogisToRemove = scala.util.Random.shuffle((firstRecordedNogi until nogiToNogood.size).toVector).sortBy(nogi => {

                          -nogiToNogood.get(nogi).toArray.map { case eli: Eli => absEliActiv.get(absEli(eli)) }.sum //- nogi

                        }).take(noOfNogoodsToRemove)

                        nogisToRemove.foreach(nogiToRemove => {

                          removeRecordedNogoods(firstNogi = nogi, lastNogi = nogi)

                        })

                      } else // we remove the oldest learned nogoods:
                        removeRecordedNogoods(firstNogi = firstRecordedNogi, lastNogi = firstRecordedNogi + noOfNogoodsToRemove - 1)
                      //removeRecordedNogoods(firstNogi = nogiToNogood.size - noOfNogoodsToRemove, lastNogi = nogiToNogood.size - 1)

                    }

                    if (nogoodExchangeProbability > 0f && maxCompetingSolverThreads > 1 && !stopSolverThreads) {

                      import scala.collection.JavaConverters._
                      val moveoverNogoods = nogoodExchangePool.entrySet().asScala.filter((value: Map.Entry[ArrayEliUnsafe, Int]) => {

                        nextFloatRngLocal() <= nogoodExchangeProbability && value.getValue != threadNo && value.getKey.size() < nogoodExchangeSizeThresh

                      })

                      if (moveoverNogoods.size > 0) {

                        log("  This thread: $" + threadNo + ", fetching " + moveoverNogoods.size + " nogoods from other threads...")

                        moveoverNogoods.foreach { case (value: Map.Entry[ArrayEliUnsafe, Int]) => {

                          nogoodExchangePool.remove(value.getKey)

                          addNogood(value.getKey)

                        }
                        }

                      }

                    }

                    if (shuffleNogoodsOnRestart) {

                      var k = 0

                      while (k < nogiToRemainder.size) {

                        shuffleArray(nogiToRemainder.get_(k).pool, rngLocal)

                        k += 1

                      }

                      var j = 0

                      while (j < nogiToNogood.size) {

                        val nogood = nogiToNogood.get(j)

                        shuffleArray(nogood, rngLocal)

                        j += 1

                      }

                    }

                    jumpBack(-1)

                    entryFreeEliSearch = rngLocal.nextInt(noOfPosElis)

                  } else if (abandonThreadsThatFellBehind && noOfPosElis > 500) {

                    if (trials % (noOfPosElis / 1000).max(1) == 0) { // we sample and average progress

                      val norm = (if (false && threadmxBean.isCurrentThreadCpuTimeSupported) threadmxBean.getCurrentThreadCpuTime() / 100000000 else trials).toDouble

                      val normalizedProgress = orderNo.toDouble / norm

                      val n = trials.toDouble / (noOfPosElis / 1000).toDouble

                      avgNormProgress = (normalizedProgress + n * avgNormProgress) / (n + 1) // cumulative moving average

                    }

                    if (trials % (noOfPosElis / 80).max(1) == 0) {

                      progressNormalizedPerThread.put(threadNo, avgNormProgress)

                      if (avgNormProgress > 0) {

                        val remainingSolverThreads = progressNormalizedPerThread.keySet.filterNot(progressNormalizedPerThread.get(_) == -1d)

                        lazy val avgNormProgressAllThreads = remainingSolverThreads.map(progressNormalizedPerThread.get(_).get).sum /
                          remainingSolverThreads.size.toDouble

                        //println("normalizedProgress for thread " + threadNo + " = " + avgNormProgress + ", avg: " + avgNormProgressAllThreads)

                        if (remainingSolverThreads.size >= 2 && avgNormProgressAllThreads - avgNormProgress > avgNormProgressAllThreads / 5d) {

                          if (verbose && showProgressStats) {

                            println("\n>> >> >> Abandoning solver thread $" + threadNo)

                            println("   normalizedProgress =  " + avgNormProgress + ", avgNormProgressAllThreads = " + avgNormProgressAllThreads + ", remaining #threads: " + (remainingSolverThreads - 1) + ", trials: " + trials)

                          }

                          progressNormalizedPerThread.put(threadNo, -1d)

                          return null

                        }

                      }

                    }

                  }

                  if (showProgressStats && noOfPosElis > 500 && trials % (noOfPosElis / 500) == 0) {

                    var preciseUnassi = 0

                    var i = 0

                    while (i < noOfPosElis) {

                      if (!isAbsSetInPass(i))
                        preciseUnassi += 1

                      i += 1

                    }

                    if (preciseUnassi < prevUnassi) {

                      prevUnassi = preciseUnassi

                      println("\nAssigned (peak, all threads): " + ((noOfPosElis - preciseUnassi).toDouble / noOfPosElis.toDouble * 100).toInt + "%  @ " + timerToElapsedMs(solverTimer) / 1000 + " sec")

                      println("  remaining unassigned atoms thread $" + threadNo + ": " + preciseUnassi) // note that a 0 here doesn't mean we are finished since conflictNogi might be != -1

                      println("  conflicts after restart: thread $" + threadNo + ": " + noOfConflictsAfterRestart)

                    }

                  }

                }

              }

            }

          }

          if (conflictNogi != -1) { // conflict handling

            completeModuloConflict = false

            if (dl == 0) {

              unsat

              return None

            }

            val (newLevel: Long, newNogood: ArrayEliUnsafe, sigma: Eli) = conflictAnalysis(conflictNogi)

            // we add a new nogood and jump back

            addNogood(newNogood)

            jumpBack(newLevel)

            setEliWithNogoodUpdates(negateEli(sigma))

            //activUpdateBase *= incActivUpdateValueOnNewNogoodFactor

            if (reviseActivFact != 1f && noOfConflictsAfterRestart % reviseActivFreq == 0) {

              log("Scaling all variable activity levels...")

              var eli = 0

              //var activSum = 0f

              while (eli < noOfPosElis) {

                absEliActiv.update(absEli(eli), absEliActiv.get(eli) * reviseActivFact)

                //activSum += absEliActiv.get(absEli(eli))

                eli += 1

              }

              //println("activSum = " + activSum)

            }

          }

        } // ---------------------------------------------------------------------------------------------------------------

        if (!stopSolverThreads) {

          log("\nEnd of inner loop reached! SolverTimer end: " + timerToElapsedMs(solverTimer) + " ms\n")

          //assert(setEliCounter == noOfAllElis / 2) // NB: if this assertion fails (exception), thread blocks or long delay (!?)

          val modelCandidate: (Array[Eli], IntOpenHashSet) = { // we must not return an Array here, as we might use the result as a cache key

            import scala.collection.JavaConverters._

            lazy val restoredNogoods: ArrayBuffer[ArrayEliUnsafe] = nogiToNogood.asScala.toArray /*.map(_.toArray)*/ .to[ArrayBuffer]

            removedNogoodsPerAtomOpt.foreach { removedNogoodsPerAtom: mutable.TreeMap[Eli /*atom*/ , ArrayBuffer[ArrayEliUnsafe]] => {
              // we've performed variable elimination in class Preparation and need to restore
              // now the removed variables (atoms) with their correct polarities:satmo

              val removedNogoodsPerAtomArray = removedNogoodsPerAtom.toArray

              removedNogoodsPerAtomArray.foreach { case (atom: Eli, _) => {

                clearInPass(atom)

                clearInPass(negatePosEli(atom))

              }
              }

              removedNogoodsPerAtomArray.reverse.foreach { case (atom: Eli, removedNogoods: ArrayBuffer[ArrayEliUnsafe]) => {

                restoredNogoods.appendAll(removedNogoods)

                setInPass(atom)

                val isAtomPos = restoredNogoods.forall((nogood: ArrayEliUnsafe) => {

                  nogood.toArray.exists(!isSetInPass(_)) // TODO: optimize restoredNogoods handling

                })

                if (!isAtomPos) {

                  clearInPass(atom)

                  setInPass(negatePosEli(atom))

                }

                log(" ok restored eliminated positive eli " + atom)

              }
              }

            }

            }

            val modelCand = new it.unimi.dsi.fastutil.ints.IntArrayList(noOfPosElis)

            var mci: Eli = 0

            while (mci < noOfPosAtomElis) { // the atom elis in the model candidate must be in increasing numerical order
              // (as we use a subset of a bounced model directly as a cache key)

              if (isSetInPass(mci))
                modelCand.add(mci)

              mci += 1

            }

            val modelCandArray = modelCand.toIntArray

            (modelCandArray, new IntOpenHashSet(modelCandArray))

          }

          val checkResult: (Boolean, Array[Eli]) = if ((satMode || (progIsTight && !enforceSanityChecks)))
            (true, Array[Eli]())
          else {

            log("Checking if stable model...")

            val r = checkASPWithEliRules(modelCandidate, rulesOpt.get)

            if (!r._1) {

              log("Answer set check fail. Remainder:\n" + r._2.mkString("\n"))

            } else
              log("Answer set check OK")

            r

          }

          if (checkResult._1) {

            assert(checkResult._2.isEmpty)

            def sanityChecks = { // we perform a few simple tests with the discovered model. For debugging purposes

              stopSolverThreads = true

              println("Performing sanity checks on model candidate... (free eli search approach was: " + freeEliSearchApproach + ")")

              assert(orderNo - 1l == noOfAllElis / 2)

              val assignment /*in contrast to modelCandidate, this also includes blits and negative elits*/ =
                (0 until noOfAllElis).filter(eli => isSetInPass(eli)).to[mutable.HashSet]

              println("#assignment = " + assignment.size)
              println("   should be: " + noOfAllElis / 2)

              val assignmentSizeCorrect = assignment.size == noOfAllElis / 2

              println("Assignment size correct?: " + assignmentSizeCorrect)

              if (!assignmentSizeCorrect)
                sys.exit(-1)

              val (allElitsCovered, noInconsistencies) = {

                var eli = 0

                var allCovered = true

                var noInconsistencies = true

                while (eli < noOfAllElis) {

                  val posIncl = assignment.contains(eli)

                  val negIncl = assignment.contains(negateEli(eli))

                  if (!posIncl && !negIncl)
                    allCovered = false

                  if (posIncl && negIncl) {

                    noInconsistencies = false

                    println("Inconsistency: both " + eli + " and " + negateEli(eli) + " (negateEli(_)) are set")

                  }
                  eli += 1

                }

                (allCovered, noInconsistencies)

              }

              println("All elis covered?: " + allElitsCovered)

              println("No inconsistencies?: " + noInconsistencies)

              var violatedNogoods = 0

              var checkedNg = 0

              var nogi = 0

              while (nogi < nogiToNogood.size()) {

                val nogood = nogiToNogood.get(nogi).toArray

                checkedNg += 1

                assert(!nogood.isEmpty)

                if (nogood.forall(assignment.contains(_))) {

                  violatedNogoods += 1

                  println("Violated nogood (internal error, please report): nogi: " + nogi + " = " + nogood.mkString(","))

                }

                nogi += 1

              }

              assert(checkedNg == nogiToNogood.size())

              println("#Violated nogoods: " + violatedNogoods)

              if (!satMode) {

                var ruleViols = 0

                rulesOpt.foreach(rules => rules.foreach(rule => {

                  assert(rule.headAtomsElis.length == 1)

                  if (!satMode)
                    assert(isPosAtomEli(rule.headAtomsElis.head))

                  val bodyFlAll = rule.bodyPosAtomsElis.forall(modelCandidate._2.contains(_)) && !rule.bodyNegAtomsElis.exists(atom => modelCandidate._2.contains(negateEli(atom)))

                  val headFl = rule.headAtomsElis.forall(assignment.contains(_))

                  val viol1 = bodyFlAll && !headFl

                  val viol2 = headFl && !rules.exists(ruleB => ruleB.bodyPosAtomsElis.forall(assignment.contains(_)) && ruleB.bodyNegAtomsElis.forall(assignment.contains(_)))

                  if (viol1) {

                    ruleViols += 1

                    println("ASP rule violated: " + rule)


                  }

                  if (viol2) {

                    ruleViols += 1

                    println("ASP rule ignored: " + rule)


                  }

                }))

                println("#Violated ASP rules: " + ruleViols)

              }

              var violatedDNogoods = 0

              val dimacsDirectClauseNogoodsOpt = aspifOrDIMACSParserResult.directClauseNogoodsOpt

              dimacsDirectClauseNogoodsOpt.foreach((directDIMACSClauseNogoods: Array[ArrayEliUnsafe]) => {

                var dnogi = 0

                while (dnogi < directDIMACSClauseNogoods.length) {

                  val dnogood: Array[Int /*"symbol" integers pos/neg, not elis*/ ] = directDIMACSClauseNogoods(dnogi).toArray

                  assert(!dnogood.isEmpty)

                  if (dnogood.forall(assignment.contains(_))) {

                    violatedDNogoods += 1

                    println("  Violated direct clauses nogood (must not happen): dnogi: " + dnogi + " = " + dnogood.mkString(","))

                  }

                  dnogi += 1

                }

              })

              println("#Violated direct clauses nogoods: " + violatedDNogoods)

              // Finally, in SAT mode, we check against the original DIMACS CNF clauses:

              if (satMode) println("Checking discovered model against original DIMACS clauses...")

              val modelCandWithSymbols: Array[String] = modelCandidate._1.map(symbols(_))

              //log("modelCandWithSymbols (recall that the numbers which are SAT symbols (variables) are different from corresponding atom elis!)\n" + modelCandWithSymbols.mkString(" "))

              var checkedDIMACSclauses = 0

              val violatedDIMACSClauses: Boolean = if (!aspifOrDIMACSParserResult.clauseTokensOpt.isDefined) {

                if (satMode)
                  println("WARNING: cannot determine violatedDIMACSClauses!");

                false

              } else {

                val modelCandWithSymbolsSet = modelCandWithSymbols.toSet

                aspifOrDIMACSParserResult.clauseTokensOpt.get.exists(clause => { // TODO: optimize:

                  val clauseFulfilled = clause.exists((dimacsVarPN: Int) => {

                    if (dimacsVarPN > 0)
                      modelCandWithSymbolsSet.contains(dimacsVarPN.toString)
                    else
                      !modelCandWithSymbolsSet.contains((-dimacsVarPN).toString)

                  })

                  if (!clauseFulfilled)
                    println("\\\\\\\\  Violated original CNF clauses: " + clause.mkString(" "))

                  checkedDIMACSclauses += 1

                  if (checkedDIMACSclauses % 500000 == 0)
                    println("  original clauses checked so far: " + checkedDIMACSclauses + " / " + aspifOrDIMACSParserResult.clauseTokensOpt.get.length)

                  !clauseFulfilled

                })

              }

              if (satMode) assert(checkedDIMACSclauses == aspifOrDIMACSParserResult.clauseTokensOpt.get.length &&
                checkedDIMACSclauses == dimacsDirectClauseNogoodsOpt.get.length)

              if (satMode) println("Any violated original DIMACS clauses: " + violatedDIMACSClauses + " (checked: " + checkedDIMACSclauses + ")")

              if (!allElitsCovered || !noInconsistencies || violatedNogoods > 0 || violatedDNogoods > 0 || violatedDIMACSClauses) {

                println("\n\\/\\/\\/\\/ Internal error: Sanity checks failed on model candidate!\n")

                sys.exit(-5)

              }

            }

            //log("pass:\n " + pass.mkString(","))

            if (enforceSanityChecks || debug)
              sanityChecks

            if (satMode) log("+++ ++ + Found a satisfying assignment") else log("*** ** * Found an answer set ")

            //println("  with symbols: " + modelCandidate.map(symbols(_)).mkString(" "))

            log("  at solverTimer " + timerToElapsedMs(solverTimer) + " ms")

            modelOpt = Some(modelCandidate)

          } else { // Model candidate bounced back, so we need to retry...

            log("\\\\\\\\\\\\\\\\ \nNot an answer set: " + modelCandidate + "\n Remainder: " + checkResult._2)

            log("Model cand with symbols: " + modelCandidate._1.map(predI => symbols(predI)).mkString(" "))

            if (progIsTight)
              stomp(-10000, "Answer set check of tight program failed in first attempt")

            // We add loop nogoods and try again (required only for non-tight programs).

            // We use a modified variant of the ASSAT approach; see the revised paper http://www.cs.ust.hk/~flin/papers/assat-aij-revised.pdf
            // for the latter (not the earlier paper). But in contrast to ASSAT, we use regular CDNL conflict handling on loop nogood violations.

            val mMinusR = checkResult._2

            val loopsOverMminus: mutable.Seq[ArrayBuffer[Eli]] = {

              sccCache.getOrElseUpdate(mMinusR, {

                val t = {

                  val tR = new Int2ObjectOpenHashMap[List[Eli]]() // this is ugly, but Java's HashMaps are in this case faster than Scala's (as of 2.12)

                  /*
                  val dgEntries = dependencyGraph.entrySet.iterator

                  while (dgEntries.hasNext) {

                    val entry: util.Map.Entry[Eli, List[Eli]] = dgEntries.next()

                    if (mMinusR.contains(entry.getKey))
                      tR.put(entry.getKey, entry.getValue)
                    else
                      tR.put(-1, Nil)

                  }*/

                  val dgEntriesIterator = dependencyGraph.keySet().iterator()

                  while (dgEntriesIterator.hasNext()) {

                    val key = dgEntriesIterator.nextInt()

                    if (mMinusR.contains(key /*.value*/))
                      tR.put(key /*.value*/ , dependencyGraph.get(key /*.value*/))
                    else
                      tR.put(-1, Nil)

                  }

                  tR

                }

                /*val tKeys: java.util.Set[Eli] = t.keySet

                val dependencyGraphInducedByMminus: IntObjectHashMap[Eli, List[Eli]] = {

                  val dgmR = new IntObjectHashMap()

                  val tEntries = t.entrySet.iterator

                  while (tEntries.hasNext) {

                    val entry: util.Map.Entry[Eli, List[Eli]] = tEntries.next()

                    dgmR.put(entry.getKey, entry.getValue.filter(tKeys.contains(_)))

                  }

                  dgmR

                }*/

                val tKeys: IntSet = t.keySet() //.keys()

                val tKeysIterator = t.keySet().iterator()

                val dependencyGraphInducedByMminus = new Int2ObjectOpenHashMap[List[Eli]]()

                while (tKeysIterator.hasNext()) {

                  val key = tKeysIterator.nextInt()

                  dependencyGraphInducedByMminus.put(key /*.value*/ , t.get(key /*.value*/).filter((eli: Eli) => {

                    tKeys.contains(new Integer(eli)) // ??? TODO

                  }))

                }

                val sccs: ArrayBuffer[ArrayBuffer[Eli]] = Tarjan.trajanRec(dependencyGraphInducedByMminus)

                sccs

              })

            }

            val maximalLoopsOverMinus =
              loopsOverMminus /*.filter(candidateLoop => {  // not worth the hassle (?)

            !loopsOverMminus.exists(loop => loop.length > candidateLoop.length && candidateLoop.forall(loop.contains(_)))

          }
          )*/

            var noOfGenLoopNogoods = 0

            var i = 0

            val mll = maximalLoopsOverMinus.length

            val jumpBackAfterFirstViolatedLoopNogood = false

            while (i < mll && (conflictNogi == -1 || !jumpBackAfterFirstViolatedLoopNogood)) {

              val loop: mutable.Seq[Eli] = maximalLoopsOverMinus(i)

              val relevantNogis: mutable.Seq[Nogi] = loop.flatMap(loopPosAtomEli => eliToNogis(loopPosAtomEli).getContent)

              val externalBodiesOfLoopAtoms: Set[Eli] = relevantNogis.flatMap(nogi => {

                val negBlits = ruliformNogiToNegBlits.get(nogi)

                Option(negBlits)

              }).flatten.filter(negBlit => {

                val posBodyElis: Array[Eli] = negBlitToPosBodyElis.get(negBlit)

                !loop.exists(posBodyElis.contains(_))

              }).toSet

              var j = 0

              val ll = loop.length

              while (j < ll && (conflictNogi == -1 || !jumpBackAfterFirstViolatedLoopNogood)) {

                val eli = loop(j)

                val newLoopNogood: Set[Eli] = externalBodiesOfLoopAtoms.+(eli)

                assert(!newLoopNogood.contains(-1))

                val newLoopNogoodUnsafe = new ArrayEliUnsafe(newLoopNogood.size)

                newLoopNogoodUnsafe.setFromIntArray(newLoopNogood.toArray)

                addNogood(newLoopNogoodUnsafe)

                noOfGenLoopNogoods += 1

                j += 1

              }

              i += 1

            }

            log("#loop nogoods created: " + noOfGenLoopNogoods)

            //log("No loop nogood triggers conflict, restarting...")

            jumpBack(-1)

          }

        }

      }

      // --------- end single supported model

      if (verbose)
        println("\nSingle model solving time (thread " + threadNo + "): " + timerToElapsedMs(solverTimer) + " ms " + (if (stopSolverThreads) " (discarded) " else ""))

      modelOpt

    }

    assert(dimacsClauseNogoodsOpt.isDefined || rulesOpt.isDefined)

    if (verbose) {

      println("#symbols (variables): " + symbols.length)

      println("#literals (including body literals): " + noOfAllElis)

      println("#initial nogoods = " + clarkNogoods.length)

      println

    }

    nogoodExchangePool.clear()

    prevUnassi = Int.MaxValue // not precise even for single solver thread. For statistics/debugging purposes only.

    stopSolverThreads = false

    val r: Option[(Array[Eli], IntOpenHashSet)] = if (maxCompetingSolverThreads == 1) {

      val freeEliSearchApproach = freeEliSearchConfigsP(0)

      val singleSolverConf = SingleSolverConf(threadNo = 1,
        costsOpt = costsOpt,
        dependencyGraph = dependencyGraph,
        progIsTight = progIsTight,
        freeEliSearchApproach = if (freeEliSearchApproach == 5) 1 else freeEliSearchApproach,
        restartTriggerConfR = restartTriggerConf,
        prearrangeEliPoolR = prearrangeEliPoolP.head,
        noHeapR = noHeapP.head,
        prep = prep /*<-for debugging/crosschecks only*/ ,
        candEliCheckCapFac = (if (freeEliSearchApproach == 5) 0 else 1),
        rndmBranchR = rndmBranchP.head)

      val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(singleSolverConf)

      log("\nSolver task complete\n")

      modelOpt

    } else {

      //assert(ignoreParamVariables)

      //competingSolversExecutorService.purge()

      @volatile var firstModelOpt = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

      val paramCombs = for (freeEliSearchApproachR <- freeEliSearchConfigsP; prearrangeEliPoolR <- prearrangeEliPoolP; rndmBranchR <- rndmBranchP; noHeapR <- noHeapP)
        yield (freeEliSearchApproachR, prearrangeEliPoolR, rndmBranchR, noHeapR)

      // Remark: we are not using a global thread pool here anymore, since by default we switch to the fastest configuration and a single solver thread
      // after the first round and the overhead was not justified anymore.

      val callables = (1 to maxCompetingSolverThreads).map(ci => new Runnable {
        override def run() = {

          val (freeEliSearchApproachR: Int, prearrangeEliPoolR: Int, rndmBranchR: Float, noHeapR: Int) = if (maxCompetingSolverThreads == 1) paramCombs.head else
            paramCombs((ci - 1) % maxCompetingSolverThreads.min(paramCombs.length))

          if (verbose)
            println("Starting solver thread $" + ci + ",\n freeEliSearchApproachR: " + freeEliSearchApproachR +
              "\n prearrangeEliPoolR: " + prearrangeEliPoolR + "\nrndmBranchR: " + rndmBranchR + "\n noHeapR: " + noHeapR)

          val singleSolverConf = SingleSolverConf(threadNo = ci,
            costsOpt = costsOpt,
            dependencyGraph = dependencyGraph,
            progIsTight = progIsTight,
            freeEliSearchApproach = if (freeEliSearchApproachR == 5) 1 else freeEliSearchApproachR,
            prearrangeEliPoolR = prearrangeEliPoolR,
            restartTriggerConfR = restartTriggerConf,
            noHeapR = noHeapR,
            prep = prep /*<-for debugging/crosschecks only*/ ,
            candEliCheckCapFac = (if (freeEliSearchApproachR == 5) 0 else 1),
            rndmBranchR = rndmBranchR)

          val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(singleSolverConf)

          if (modelOpt != null) {

            stopSolverThreads.synchronized {

              if (!stopSolverThreads) {

                if (verbose)
                  println("Successful portfolio thread: " + ci)

                if (switchToBestConfig > 0) {

                  freeEliSearchConfigsP = freeEliSearchConfigsP.map(_ => freeEliSearchApproachR)

                  prearrangeEliPoolP = prearrangeEliPoolP.map(_ => prearrangeEliPoolR)

                  noHeapP = noHeapP.map(_ => noHeapR)

                  if (verbose)
                    println("\nSwitching to portfolio\n freeEliSearchConfigsP: " + freeEliSearchConfigsP +
                      "\n  prearrangeEliPoolP: " + prearrangeEliPoolP +
                      "\n  rndmBranchR: " + rndmBranchR +
                      "\n  noHeapP: " + noHeapP)

                  if (switchToBestConfig == 2)
                    maxCompetingSolverThreads = 1

                }

                stopSolverThreads = true

              }

            }

            firstModelOpt = modelOpt

          }

        }
      }) //.asJava

      //competingSolversExecutorService.invokeAny(callables)

      val solverThreads = callables.map(c => {

        val t = new Thread(c)

        //t.setPriority(Thread.MAX_PRIORITY)

        t.setDaemon(false)

        t.start()

        t

      })

      solverThreads.foreach(_.join())

      firstModelOpt

    }

    log("sampleSingleRacing complete: r = " + r)

    assert(r != null)

    r

  }

}


