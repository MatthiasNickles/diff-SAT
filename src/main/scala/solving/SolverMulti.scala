/**
  * DelSAT
  *
  * A tool for differentiable satisfiability and differentiable answer set programming
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  */

package solving

import java.util
import java.util.Comparator
import java.util.concurrent._

import aspIOutils._

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.DifferentialFunction

import com.carrotsearch.hppc.{IntObjectHashMap, IntScatterSet}

import sharedDefs._
import commandline.delSAT._

import diff.UncertainAtomsSeprt

import it.unimi.dsi.fastutil.ints.{IntArrayList, IntOpenHashSet}
import it.unimi.dsi.fastutil.objects.ObjectArrayList

import utils.{IntArrayUnsafe, LongArrayUnsafe, Tarjan, XORShift32}

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
  @inline def currentCosts(costFctsInner: ArrayBuffer[DifferentialFunction[DoubleReal]]): (Double /*total cost*/ ,
    ArrayBuffer[Double /*inner costs*/ ]) = {

    if (costFctsInner.length == 0)
      (0d, ArrayBuffer[Double]())
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

  @inline def updateAtomsFreqs(m: IntOpenHashSet,
                               measuredAtomElis: Array[Eli],
                               uncertainAtomEliToStatisticalProb: Array[Double],
                               sampledModels /*after adding new model m*/ : mutable.ArrayBuffer[Array[Eli]],
                               fromScratch: Boolean = false) = {

    assert(!fromScratch)

    val newModelsCount: Double = sampledModels.length.toDouble

    val par = measuredAtomElis.length > parallelThresh * 5

    if (par) {

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

  }

  @inline def updateMeasuredAtomsFreqsAndComputeCost(m: IntOpenHashSet,
                                                     measuredAtomElis: Array[Eli],
                                                     measuredAtomEliToStatisticalFreq: Array[Double],
                                                     sampledModels /*after adding new model m*/ : mutable.ArrayBuffer[Array[Eli]],
                                                     costFctsInner: ArrayBuffer[DifferentialFunction[DoubleReal]],
                                                     fromScratch: Boolean = false,
                                                     computeCosts: Boolean = true,
                                                     partDerivativeComplete: Boolean,
                                                     update_parameterAtomVarForParamEli_forPartDerivCompl: => Unit
                                                    ):
  Option[(Double /*total cost*/ , ArrayBuffer[Double /*inner costs*/ ])] = {

    // We firstly update the measured uncertainty atoms (which, for now, need to be identical with the parameter atoms):

    updateAtomsFreqs(m,
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

  val nogiToNogoodClark: ObjectArrayList[ArrayEliUnsafe] = new it.unimi.dsi.fastutil.objects.ObjectArrayList[ArrayEliUnsafe](clarkNogoods.length * 2)

  val ruliformNogiToNegBlits = new IntObjectHashMap[Array[Eli /*negative blit*/ ]]() // only needed for non-tight ASP programs

  val eliToNogisBuilder = Array.fill(noOfAllElis)(new mutable.ArrayBuilder.ofInt)

  val eliToNogisClark: Array[ArrayValExtensibleIntUnsafe] = Array.ofDim[ArrayValExtensibleIntUnsafe](noOfAllElis) // per each eli, all nogis which contain that eli

  //log("timer 1: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

  var nogj = 0

  val cnl = clarkNogoods.length

  while (nogj < cnl) {

    val clarkNogood: Array[Eli] = clarkNogoods(nogj)

    val newUnsafeNogood = new ArrayEliUnsafe(clarkNogood.length)

    newUnsafeNogood.setFromIntArray(clarkNogood)

    //if (threadNo != 1)
    //shuffleArray(newUnsafeNogood, rngLocal)

    nogiToNogoodClark.add(newUnsafeNogood)

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

  //log("timer 2: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

  var eliActiv = new IntArrayUnsafe(noOfAllElis) // must be global

  val elisArrangedR: Array[Eli] = (0 until noOfAllElis).toArray

  var elisArranged = if (!prearrangeEliPoolR) elisArrangedR else {

    //shuffleArray(elisArrangedR, rngLocal)

    elisArrangedR.sortBy({ case ((eli: Eli)) =>

      -eliToNogisClark(eli).length

    })

  }

  var posElisArranged = (0 until noOfPosElis).toArray

  if (prearrangeEliPoolR) {

    //shuffleArray(posElisArranged, rngLocal)

    posElisArranged = posElisArranged.sortBy({ case ((eli: Eli)) =>

      -(eliToNogisClark(eli).length + eliToNogisClark(negatePosEli(eli)).length)

    })

  }

  /**
    * @author Matthias Nickles
    *
    */
  def sampleMulti(costsOpt: Option[UncertainAtomsSeprt],
                  requestedNoOfModelsBelowThresholdOrAuto: Int, satMode: Boolean, prep: Preparation,
                  requestedNumberOfModels: Int /*-1: stop at minimum number of models required to reach threshold*/ ,
                  threshold: Double,
                  maxIt: Int): (mutable.Seq[Array[Pred]]) = {

    val sampledModels = ArrayBuffer[Array[Eli]]()

    var totalCost: Double = Double.MaxValue

    var it = 1

    val samplingTimer = System.nanoTime()

    do {

      val newModelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing(costsOpt, satMode, prep)

      if(newModelOpt.isEmpty)
        return mutable.Seq[Array[Pred]]()

      sampledModels.append(newModelOpt.get._1)

      totalCost = if (ignoreParamVariables) Double.NegativeInfinity else updateMeasuredAtomsFreqsAndComputeCost(newModelOpt.get._2,
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

        if (arrangeParamElisInEliPool) {

          elisArranged = elisArranged.sortBy({ case ((eli: Eli)) =>

            if (parameterAtomsElisSet.contains(eli)) {

              deficitByDeriv(eli) * 10000

            } else Int.MaxValue

          })

        }

      }

      log("\nSampling iteration " + it + " (of max " + maxIt + ") complete. " +
        "Current cost: " + totalCost + " (threshold: " + threshold + ")")

      it += 1

    } while (it < maxIt && (requestedNumberOfModels == -1 && totalCost > threshold ||
      requestedNumberOfModels >= 0 && sampledModels.length < requestedNumberOfModels))

    if (totalCost < threshold)
      println("\nSampling complete; specified threshold reached. " + sampledModels.length + " models sampled (with replacement)\n")
    else
      println("\nWARNING: Sampling ended but specified threshold not reached!\n")

    println("Overall time solving and sampling: " + (System.nanoTime() - samplingTimer) / 1000000 + " ms\n")

    val sampledModelsSymbolic = sampledModels.map(model => model.map(eli => symbols(eli)))

    log("sampledModelsSymbolic:\n" + sampledModelsSymbolic.map(_.mkString(" ")).mkString("\n"))

    sampledModelsSymbolic

  }

  var nogoodExchangePool = new java.util.concurrent.ConcurrentHashMap[ArrayEliUnsafe, Int /*producing thread*/ ]()

  var prevUnassi = Int.MaxValue // not precise; for statistics/debugging only

  var stop = false

  def sampleSingleRacing(costsOpt: Option[UncertainAtomsSeprt], satMode: Boolean, prep: Preparation): Option[(Array[Eli], IntOpenHashSet)] = {

    assert(dimacsClauseNogoodsOpt.isDefined || rulesOpt.isDefined)

    if (showProgressStats) {

      /* if (!satMode)
         println("#given ASP ground rules = " + rulesOpt.get.length)
       else
         println("#given nogoods from DIMACS clauses (incl. nogoods with blits) = " + dimacsClauseNogoodsOpt.get.length) */

      println("#given symbols = " + symbols.length)

      println("#noOfPosBlits = " + noOfPosBlits)

      System.out.println("Size of a completeModuloConflict assignment: " + assgnmFullSize)

      System.out.println("#elis: " + noOfAllElis)

      println("#Nogoods = " + clarkNogoods.length)

    }

    //println("timer: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

    def beliThC(freeEliSearchApproach: Int) = /*if (freeEliSearchApproach == 2 || freeEliSearchApproach == 3) 0f else*/
      if (beliThR != -1f) beliThR else if (diversify) 0.5f else if (freeEliSearchApproach == 2) (rngGlobal.nextFloat() - 0.7f).max(0.00001f) else 0.99999f

    def prearrangeEliPoolC(ci: Int) = if (prearrangeEliPoolR == 0) false else if (prearrangeEliPoolR == 1) true else {

      if (ci == 1) false else if (ci == 2) true else rngGlobal.nextBoolean()

    }

    nogoodExchangePool.clear()

    prevUnassi = Int.MaxValue // not precise even for single solver thread. For statistics/debugging purposes only.

    stop = false

    if (maxNumberOfCompetingModelSearchThreads == 1) {

      val freeEliSearchApproach = freeEliSearchApproachesR(0)

      val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(threadNo = 1, costsOpt, satMode, dependencyGraph, progIsTight,
        freeEliSearchApproach = if (freeEliSearchApproach == 5) 4 else freeEliSearchApproach,
        restartTriggerConfR = restartTriggerConf,
        //noOfConflictsBeforeRestartFactor = noOfConflictsBeforeRestartFactor,
        beliTh = beliThC(freeEliSearchApproach),
        prep /*<-for debugging/crosschecks only*/ ,
        candEliCheckCapFac = (if (freeEliSearchApproach == 5) 0d else candEliCheckCapFacR),
        prearrangeEliPool = prearrangeEliPoolC(1))

      log("\n^^^^^^^ Solver task complete\n")

      modelOpt

    } else {

      assert(ignoreParamVariables)

      val competingSolversExecutorService = new ThreadPoolExecutor(maxNumberOfCompetingModelSearchThreads, maxNumberOfCompetingModelSearchThreads,
        6, TimeUnit.SECONDS, new LinkedBlockingQueue[Runnable])

      //competingSolversExecutorService.prestartAllCoreThreads()

      import scala.collection.JavaConverters._

      val callables = (1 to maxNumberOfCompetingModelSearchThreads).map(ci => new Callable[Option[(Array[Eli], IntOpenHashSet)]] {
        override def call(): Option[(Array[Eli], IntOpenHashSet)] = {

          val freeEliSearchApproach = if (maxNumberOfCompetingModelSearchThreads == 1) freeEliSearchApproachesR.head else
            freeEliSearchApproachesR((ci - 1) % (maxNumberOfCompetingModelSearchThreads + 1) - 1)

          log("freeEliSearchApproach in thread: " + freeEliSearchApproach)

          val beliTh = beliThC(freeEliSearchApproach)

          log("beliTh in thread " + ci + ": " + beliTh)

          val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(threadNo = ci, costsOpt, satMode, dependencyGraph, progIsTight,
            freeEliSearchApproach = if (freeEliSearchApproach == 5) 4 else freeEliSearchApproach,
            restartTriggerConfR = restartTriggerConf,
            beliTh = beliTh,
            prep /*<-for debugging/crosschecks only*/ ,
            candEliCheckCapFac = (if (freeEliSearchApproach == 5) 0d else candEliCheckCapFacR),
            prearrangeEliPool = prearrangeEliPoolC(ci))

          stop = true

          println("\n^^^^^^^ callable $" + ci + " complete\n")

          modelOpt

        }
      }).asJava

      competingSolversExecutorService.invokeAny(callables)

    }

  }

  /**
    * @author Matthias Nickles
    */
  def sampleSingle(threadNo: Int /*>=1*/ ,
                   costsOpt: Option[UncertainAtomsSeprt], satMode: Boolean,
                   dependencyGraph: IntObjectHashMap[List[Eli]], progIsTight: Boolean,
                   freeEliSearchApproach: Int,
                   restartTriggerConfR: (Boolean, Int, Double),
                   beliTh: Float,
                   prep: Preparation /*<-for debugging/crosschecks only*/ ,
                   candEliCheckCapFac: Double,
                   prearrangeEliPool: Boolean): Option[(Array[Eli], IntOpenHashSet)] = {

    val timerBatchSamplingStartPreciseNs = System.nanoTime()

    val rngLocal: java.util.Random = new XORShift32()

    val sccCache = mutable.HashMap[mutable.Seq[Eli], ArrayBuffer[ArrayBuffer[Eli]]]()

    val nogiToNogood: ObjectArrayList[ArrayEliUnsafe] = new ObjectArrayList(nogiToNogoodClark)

    val eliToNogis: Array[ArrayValExtensibleIntUnsafe] = eliToNogisClark.clone().map(ausf => new ArrayValExtensibleIntUnsafe(ausf.getContent.clone())) //.asInstanceOf[Array[ArrayValExtensibleIntUnsafe]]

    var activUpdateVal = initialActivUpdateValue

    val restartTriggerConf: (Boolean, Int, Double) = if (restartTriggerConfR._3 < 0d || restartTriggerConfR._2 == -1)
      (restartTriggerConfR._1, if (restartTriggerConfR._2 == -1) (if (recAssg && symbols.length < 25000) 5000 else 5) else
        restartTriggerConfR._2,
        if (restartTriggerConfR._3 < 0d) rngGlobal.nextGaussian() * .15d - restartTriggerConfR._3 else restartTriggerConfR._3)
    else restartTriggerConfR

    val localSingleSamplerThreadPool = new ThreadPoolExecutor(2, 2, 600, TimeUnit.SECONDS,
      new LinkedBlockingQueue[Runnable]) // used for all local multithreading (i.e., not portfolio-based racing)

    //implicit val ord:Ordering[Eli] = Ordering.by(-eliActiv(_))

    val unassignedAbsElisPool = new util.PriorityQueue[Eli](new Comparator[Eli] {
      override def compare(o1: Eli, o2: Eli): Int = ((eliActiv.get(o2) - eliActiv.get(o1)))
    })

    var someFreeEli1: Eli = -1
    var someFreeEli2: Eli = -1
    var someFreeEli3: Eli = -1
    var someFreeEli4: Eli = -1

    //clarkNogoods.copyToBuffer(nogiToNogood)  slower!?

    val pass = new LongArrayUnsafe(noOfAllElis, 0l) // the partial assignment. Item = 0: eli is unassignedPosElis or doesn't hold,
    // != 0: eli holds, with orderOfEli in the ORDERBITS least significant bits, followed by decision level.

    //log("timer 3: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

    var dl = 0l // decision level (increased at each nondeterministic branching literal decision)

    var orderNo = 1l // sequence number of next eli assignment (not necessarily consecutive)

    var setEliCounter = 0

    class NogoodRemainder(var pool: /*Array[Eli]*/ ArrayEliUnsafe) {
      // NB: constructor doesn't set head/tail lits, so we need to call reset (unless we know both head/tail lits must be -1)

      type V = Int

      var headNotsetItem1: V = -1

      var tailNotsetItem2: V = -1

      @inline def sortPoolBySet: Unit = {

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

      }

      @inline def reset = { // initially, the two head/tail lits are filled with UNset items (e.g., unassignedPosElis elis)

        if (sortRemainderPoolProb > 0f && pool.size > 2)
          sortPoolBySet

        if (pool.size == 2l) {

          if (isSetInPass(pool.get(0))) {

            tailNotsetItem2 = -1

            if (isSetInPass(pool.get(1))) {

              headNotsetItem1 = -1

            } else {

              headNotsetItem1 = pool.get(1)

            }

          } else {

            headNotsetItem1 = pool.get(0)

            if (isSetInPass(pool.get(1))) {

              tailNotsetItem2 = -1

            } else {

              tailNotsetItem2 = pool.get(1)

            }

          }

        } else {

          val ps = pool.size

          headNotsetItem1 = -1

          tailNotsetItem2 = -1

          var i = ps - 1

          do {

            val gi = pool.get(i)

            if (isNotSetInPass(gi)) {

              if (headNotsetItem1 == -1)
                headNotsetItem1 = gi
              else if (pool.get(i) != headNotsetItem1)
                tailNotsetItem2 = gi

            }

            i -= 1

          } while (tailNotsetItem2 == -1 && i >= 0)

        }

        (headNotsetItem1, tailNotsetItem2)

      }

      @inline def get2NotsetItems = {

        (headNotsetItem1, tailNotsetItem2)

      }

      @inline def unSetItem(item: V) = {

        if (headNotsetItem1 == -1 && item != tailNotsetItem2)
          headNotsetItem1 = item
        else if (tailNotsetItem2 == -1 && item != headNotsetItem1)
          tailNotsetItem2 = item

      }

      @inline def setItem(item: V) = {

        @inline def fillUp = {

          if (pool.size <= 2l)
            tailNotsetItem2 = -1
          else if (pool.size == 3l) {

            if (pool.get(0) != headNotsetItem1 && isNotSetInPass(pool.get(0)))
              tailNotsetItem2 = pool.get(0)
            else {

              if (pool.get(1) != headNotsetItem1 && isNotSetInPass(pool.get(1)))
                tailNotsetItem2 = pool.get(1)
              else {

                if (pool.get(2) != headNotsetItem1 && isNotSetInPass(pool.get(2)))
                  tailNotsetItem2 = pool.get(2)
                else
                  tailNotsetItem2 = -1

              }
            }

          } else {

            val ps = pool.size

            tailNotsetItem2 = -1

            if (sortRemainderPoolProb > 0f && pool.size > 2 && rngGlobal.nextFloat() < sortRemainderPoolProb) {

              sortPoolBySet

            }

            var i = ps - 1

            do {

              val pi = pool.get(i)

              if (isNotSetInPass(pi) && pi != headNotsetItem1)
                tailNotsetItem2 = pi
              else
                i -= 1

            } while (tailNotsetItem2 == -1 && i >= 0)

          }

        }

        if (item == headNotsetItem1) {

          if (tailNotsetItem2 != -1) {

            headNotsetItem1 = tailNotsetItem2

            fillUp

          } else
            headNotsetItem1 = -1

        } else if (item == tailNotsetItem2) {

          fillUp

        }

        (headNotsetItem1, tailNotsetItem2)

      }

    }

    @inline def isSetInPass(eli: Eli): Boolean = pass.get(eli) != 0l

    @inline def isNotSetInPass(eli: Eli): Boolean = pass.get(eli) == 0l

    @inline def isAbsSetInPass(eli: Eli): Boolean = {

      if (eli < posNegEliBoundary)
        pass.get(eli + posNegEliBoundary) != 0l || pass.get(eli) != 0l
      else
        pass.get(eli - posNegEliBoundary) != 0l || pass.get(eli) != 0l

    }

    @inline def isAbsNotSetInPassInt(eli: Eli): Int = {

      val sip = if (eli < posNegEliBoundary)
        pass.get(eli + posNegEliBoundary) != 0l || pass.get(eli) != 0l
      else
        pass.get(eli - posNegEliBoundary) != 0l || pass.get(eli) != 0l

      if (sip) 0 else 1

    }

    @inline def setInPass(eli: Eli) = { // must be the only way (after preprocessing/initialization) of assigning True

      //assert(!isSetInPass(eli))  // must hold

      //assert(orderNo > 0)

      pass.update(eli, orderNo + (dl << ORDERBITS))

      setEliCounter += 1

      orderNo += 1l

      if (freeEliSearchApproach == 4 || freeEliSearchApproach == 6) {

        if (eli == someFreeEli1)
          someFreeEli1 = -1
        else if (eli == someFreeEli2)
          someFreeEli2 = -1
        else if (eli == someFreeEli3)
          someFreeEli3 = -1
        else if (eli == someFreeEli4)
          someFreeEli4 = -1

      }

    }

    @inline def clearInPass(eli: Eli) = { // must be the only way (after preprocessing/initialization) of assigning False

      //assert(isSetInPass(eli))

      // Note that this method doesn't update nogoods

      pass.update(eli, 0l)

      setEliCounter -= 1

      orderNo -= 1l

      //assert(orderNo != 0)

      if (freeEliSearchApproach == 4 || freeEliSearchApproach == 6) {

        if (someFreeEli1 == -1 || eliActiv.get(eli) > eliActiv.get(someFreeEli1))
          someFreeEli1 = eli
        else if (someFreeEli2 == -1 || eliActiv.get(eli) > eliActiv.get(someFreeEli2))
          someFreeEli2 = eli
        else if (someFreeEli3 == -1 || eliActiv.get(eli) > eliActiv.get(someFreeEli3))
          someFreeEli3 = eli
        else if (someFreeEli4 == -1 || eliActiv.get(eli) > eliActiv.get(someFreeEli4))
          someFreeEli4 = eli

      } else if (freeEliSearchApproach == 3)
        unassignedAbsElisPool.offer(eli)

    }

    @inline def orderOfEli(eli: Eli) = pass.get(eli) & ((1l << ORDERBITS) - 1l)

    @inline def decisionLevelOfEli(eli: Eli) = pass.get(eli) >>> ORDERBITS // for large bulk compare operations, use, e.g., pass(eli) > dl << ORDERBITS

    var forceElis = new it.unimi.dsi.fastutil.ints.IntRBTreeSet() // new ArrayEliUnsafe(noOfAllElis * 2) // on the heap, the next batch of deductively inferable literals

    var forceElisSize = 0

    var conflictNogi = -1

    val nogiToRemainder = new it.unimi.dsi.fastutil.objects.ObjectArrayList[NogoodRemainder]() /* two unassigned elis (head/tail literals) per each nogood */

    @inline def checkFireNogood(remaining2InNogood: (Eli, Eli), nogi: Nogi) = {

      if (remaining2InNogood._1 == -1)
        conflictNogi = nogi
      else if (remaining2InNogood._2 == -1) { // the only remaining unassignedPosElis eli ._1 is unit resulting

        if (recAssg)
          setEliWithNogoodUpdates(negateEli(remaining2InNogood._1))
        else
          forceElis.add(negateEli(remaining2InNogood._1))

      }

    }

    @inline def setEliWithNogoodUpdates(eli: Eli): Unit = {

      if (isNotSetInPass(eli) /*&& conflictNogi == -1*/ ) {

        //log(" assigning eli " + eli + " on decision level " + dl + ", orderNo: " + orderNo)

        setInPass(eli)

        if (!recAssg) {

          var i = eliToNogis(eli).length - 1

          while (i >= 0) {

            checkFireNogood(nogiToRemainder.get(eliToNogis(eli).buffer.get(i)).setItem(eli), eliToNogis(eli).buffer.get(i))

            i -= 1

          }

        } else {

          val il = eliToNogis(eli).length

          var i = 0

          if (il < parallelThresh) {

            while (i < il) {

              nogiToRemainder.get(eliToNogis(eli).buffer.get(i)).setItem(eli)

              i += 1

            }

          } else {

            val nweh = il / 2

            val cdl = new CountDownLatch(2)

            localSingleSamplerThreadPool.execute(new Runnable() {
              override def run(): Unit = {

                var i = nweh - 1

                while (i >= 0) {

                  //itemOp(buffer(i))
                  nogiToRemainder.get(eliToNogis(eli).buffer.get(i)).setItem(eli)

                  i -= 1

                }

                cdl.countDown()

              }
            })

            localSingleSamplerThreadPool.execute(new Runnable() {
              override def run(): Unit = {

                var il = eliToNogis(eli).length

                while (i < il) {

                  nogiToRemainder.get(eliToNogis(eli).buffer.get(i)).setItem(eli)

                  i += 1

                }

                cdl.countDown()

              }
            })

            cdl.await()

          }

          i = 0

          while (i < il && conflictNogi == -1) { // with recAssg = false, we need a separate loop here as otherwise checkFireNogood would operate with incompletely updated remainders,
            // which would lead to wrong results (also see same pattern in method jumpBack)

            checkFireNogood(nogiToRemainder.get(eliToNogis(eli).buffer.get(i)).get2NotsetItems, eliToNogis(eli).buffer.get(i))

            i += 1

          }


        }
      }

    }

    log("timer 4: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

    var nogi: Nogi = 0

    val ntngl = nogiToNogood.size

    while (nogi < ntngl) {

      val nogood = nogiToNogood.get(nogi)

      nogiToRemainder.add {

        val nogoodRemainder = new NogoodRemainder(pool = nogood)

        nogoodRemainder.reset

        //checkFireNogood(rem, nogi = nogi)  // we can't do this here since the remainders aren't completely known yet, which would
        // lead to errors if checkFireNogood actually fires. Thus, the very first bunch of assigned literals is on decision level 1 (!).

        nogoodRemainder

      }

      nogi += 1

    }

    var firstRecordedNogi = -1

    log("timer 5: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

    @inline def activUpEli(eli: sharedDefs.Eli) = eliActiv.incBy(eli, activUpdateVal)

    @inline def incActivNogoodElisUnsafe(nogood: ArrayEliUnsafe, nogi: Nogi, until: Long) = {

      var i = until - 1

      while (i >= 0) {

        val eli = nogood.get(i)

        if (eli != -1)
          activUpEli(eli)

        i -= 1

      }

    }

    def conflictAnalysis(pivotNogi: Nogi):
    (Long /*new decision level to jump to*/ , ArrayEliUnsafe /*learned nogood*/ , Int /*sigmaEli*/ ) = {

      log("\n\\\\\\ Conflict analysis...")

      var pivotNogood = nogiToNogood.get(pivotNogi)

      val accumulatedNogoodBuilder = new ArrayValExtensibleIntUnsafe(pivotNogood.clone(0)) //new ArrayValExtensible[Eli](pivotNogood.toArray /* clone()*/)

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

          val candNogisLength = eliToNogis(sigmaNot).length //candNogis.length

          var candNogisI = 0 //rngLocal.nextInt(candNogisLength)

          val candNogisIStart = candNogisI

          var eps: Nogi = -1

          while (candNogisI < candNogisLength && eps == -1) {

            val candNogi: Nogi = candNogis.get(candNogisI)

            val candNogood = nogiToNogood.get(candNogi)

            val fa: Boolean = {

              var i = 0

              val cl = candNogood.size()

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
            // this typically (but not necessarily) indicates that elis are set out of order, e.g., an neg(eli) is set to True before
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

    var noOfConflictsAfterRestart = 0

    var geomNoOfConflictsBeforeRestart = restartTriggerConf._2

    var noOfRestarts = 0

    val nogisToReset = new IntScatterSet() // scatter/hashset to avoid resetting duplicates, but often not worth the effort

    nogisToReset.ensureCapacity(noOfAllElis /*rough estimator*/)

    val clearInJumpBackTasks = new util.ArrayList[Runnable]()

    var nogisWithEliToClear: ArrayValExtensibleIntUnsafe = null

    var nweh = -1

    var eliToClear = -1

    var cdlcl = null.asInstanceOf[CountDownLatch]

    clearInJumpBackTasks.add(new Runnable {
      override def run(): Unit = {

        var i = nweh - 1

        while (i >= 0) {

          nogiToRemainder.get(nogisWithEliToClear.get(i)).unSetItem(eliToClear)

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

          nogiToRemainder.get(nogisWithEliToClear.get(i)).unSetItem(eliToClear)

          i += 1

        }

        cdlcl.countDown()

      }
    })

    @inline def jumpBack(newLevel: Long) = {

      log("Jumping back to decision level " + newLevel)

      // We removeItem everything with a decision level > newLevel

      conflictNogi = -1

      forceElisSize = 0
      forceElis.clear()

      if (newLevel == -1) { // we restart from scratch

        dl = 0

        noOfConflictsAfterRestart = 0

        activUpdateVal = initialActivUpdateValue

        someFreeEli1 = -1
        someFreeEli2 = -1
        someFreeEli3 = -1
        someFreeEli4 = -1
        /* someFreeEli5 = -1*/

        unassignedAbsElisPool.clear()

      } else {

        dl = newLevel

        noOfConflictsAfterRestart += 1

      }

      //nogisToReset.clear()

      var eli = 0

      while (eli < noOfPosElis) {

        @inline def clear(eli: Eli) = {

          assert(isSetInPass(eli))

          clearInPass(eli)

          val nogisWithEli: ArrayValExtensibleIntUnsafe = eliToNogis(eli)

          if (nogisWithEli.length < parallelThresh) {

            var i = nogisWithEli.length - 1

            while (i >= 0) {

              val nogi = nogisWithEli.get(i)

              nogiToRemainder.get(nogi).unSetItem(eli)

              i -= 1

            }

          } else {

            nogisWithEliToClear = nogisWithEli

            nweh = nogisWithEli.length / 2

            eliToClear = eli

            cdlcl = new CountDownLatch(2)

            //localSingleSamplerThreadPool.invokeAll(clearInJumpBackTasks)

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

    }

    @inline def addNogood(newNogoodR: ArrayEliUnsafe): Nogi = {

      //assert(!newNogood.contains(-1))

      val newNogoodArray = newNogoodR.toArray.distinct

      val newNogood = new ArrayEliUnsafe(newNogoodArray.length)

      newNogood.setFromIntArray(newNogoodArray)

      val newNogi = nogiToNogood.size

      if (firstRecordedNogi == -1)
        firstRecordedNogi = newNogi

      nogiToNogood.add(newNogood)

      var i = newNogood.size() - 1

      while (i >= 0) {

        val eliInNewNogood = newNogood.get(i)

        eliToNogis(eliInNewNogood).append(newNogi)

        i -= 1

      }
      val newNogoodRemainder = new NogoodRemainder(pool = newNogood)

      nogiToRemainder.add(newNogoodRemainder)

      checkFireNogood(newNogoodRemainder.reset, newNogi)

      if (maxNumberOfCompetingModelSearchThreads > 1)
        nogoodExchangePool.put(newNogood, threadNo)

      incActivNogoodElisUnsafe(newNogood, newNogi, newNogood.size())

      newNogi

    }

    @inline def removeRecordedNogoods(firstNogi: Nogi, lastNogi: Nogi) = {

      assert(firstRecordedNogi >= 0 && firstNogi >= firstRecordedNogi && lastNogi >= firstNogi && lastNogi < nogiToNogood.size)

      val noToRemove = lastNogi - firstNogi + 1

      var nogiToRemove = lastNogi

      while (nogiToRemove >= firstNogi) {

        nogiToNogood.remove(nogiToRemove)

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

        eli += 1

      }

    }

    var modelOpt: Option[(Array[Eli], IntOpenHashSet)] = None

    @inline def noOfConflictsBeforeRestart = {

      ((nogiToNogood.size - firstRecordedNogi) * restartTriggerConf._3).max(2)

    }

    var restartTimer = System.nanoTime()

    while (modelOpt.isEmpty) {

      var completeModuloConflict = false

      var trials = 0

      val eal = (if (freeEliSearchApproach == 2) posElisArranged.length else elisArranged.length)

      val maxItInit = (eal.toDouble * candEliCheckCapFac).toInt.max(1)

      var entryFreeEliSearch = rngLocal.nextInt(noOfPosElis)

      @inline def findFreeEli: (Int, Float) = {

        var freeEli = -1

        var freeEliActiv = Int.MinValue

        val removedElisFreeOpt = if (variableElimConfig._5 || !variableElimConfig._1) None else removedNogoodsPerAtomOpt.flatMap(_.keys.find(!isAbsSetInPass(_)))

        if (removedElisFreeOpt.isDefined)
          freeEli = removedElisFreeOpt.get
        else {

          if (!ignoreParamVariables) {

            // We check the parameter atoms (random variables) in the order provided by the partial derivatives (over multiple atoms, this
            // implicitly gives the gradient):

            var i = 0

            val il = deficitOrderedUncertainLiterals.length / 2 // each variable appears twice, we only need their lowest ranked literals

            while (i < il) {

              val uncertainEli = deficitOrderedUncertainLiterals(i)

              if (!isAbsSetInPass(uncertainEli)) {

                return (uncertainEli, 1f)

              }

              i += 1

            }

          }

          if (freeEliSearchApproach == 4 || freeEliSearchApproach == 6) {

            val r1 = isAbsNotSetInPassInt(someFreeEli1) * eliActiv.get(someFreeEli1)

            val r2 = isAbsNotSetInPassInt(someFreeEli2) * eliActiv.get(someFreeEli2)

            val r3 = isAbsNotSetInPassInt(someFreeEli3) * eliActiv.get(someFreeEli3)

            val r4 = isAbsNotSetInPassInt(someFreeEli4) * eliActiv.get(someFreeEli4)

            freeEli = if (r1 > r2 && r1 > r3 && r1 > r4) someFreeEli1
            else if (r2 > r1 && r2 > r3 && r2 > r4) someFreeEli2
            else if (r3 > r1 && r3 > r2 && r3 > r4) someFreeEli3
            else if (r4 > r1 && r4 > r2 && r4 > r3) someFreeEli4
            else -1

            if (freeEli == -1) {

              if (freeEliSearchApproach == 6) {

                freeEli = rngLocal.nextInt(noOfAllElis)

                if (isAbsSetInPass(freeEli))
                  freeEli = -1

              } else {
                var i = 0

                val eal = elisArranged.length

                var maxIt = if (noOfConflictsAfterRestart == 0) 1 else maxItInit

                while (i < eal && (maxIt > 0 || freeEli == -1)) {

                  val candEli: Eli = elisArranged(i)

                  if (!isAbsSetInPass(candEli) && (eliActiv.get(candEli) > freeEliActiv || freeEliActiv == Int.MinValue)) {

                    freeEli = candEli

                    freeEliActiv = eliActiv.get(candEli)

                    maxIt -= 1

                  }

                  i += 1

                }

              }

            }

          } else if (freeEliSearchApproach == 2) {

            var posEliI = noOfPosElis - 1

            var maxIt = if (noOfConflictsAfterRestart == 0) 1 else maxItInit

            while (posEliI >= 0 && ((maxIt > 0 || freeEli == -1))) {

              val posEli = posElisArranged(posEliI)

              if (!isAbsSetInPass(posEli) && (eliActiv.get(absEli(posEli)) > freeEliActiv || freeEliActiv == Int.MinValue)) {

                freeEli = posEli

                freeEliActiv = eliActiv.get(posEli)

                maxIt -= 1

              }

              posEliI -= 1

            }

          } else if (freeEliSearchApproach == 0) {

            val xa = elisArranged

            var i = entryFreeEliSearch

            var maxIt = if (noOfConflictsAfterRestart == 0) 1 else maxItInit

            var stop = false

            while (!stop && ((maxIt > 0 || freeEli == -1))) {

              val candEli: Eli = xa(i)

              if (!isAbsSetInPass(candEli) && ((eliActiv.get(candEli) > freeEliActiv /*|| freeEliActiv == Int.MinValue*/))) {

                freeEli = candEli

                freeEliActiv = eliActiv.get(candEli)

                maxIt -= 1

              }

              i += 1

              if (i >= eal)
                i = 0

              if (i == entryFreeEliSearch)
                stop = true


            }

            entryFreeEliSearch = i

          } else if (freeEliSearchApproach == 3) {

            while (freeEli == -1 && !unassignedAbsElisPool.isEmpty) {

              val pe = unassignedAbsElisPool.poll()

              if (!isAbsSetInPass(pe)) {

                freeEli = pe

              }

            }

            if (freeEli == -1) {

              var i = 0

              val eal = elisArranged.length

              var maxIt = if (noOfConflictsAfterRestart == 0) 1 else maxItInit

              while (i < eal && (maxIt > 0 || freeEli == -1)) {

                val candEli: Eli = elisArranged(i)

                if (!isAbsSetInPass(candEli) && (eliActiv.get(candEli) > freeEliActiv || freeEliActiv == Int.MinValue)) {

                  freeEli = candEli

                  freeEliActiv = eliActiv.get(candEli)

                  maxIt -= 1

                }

                i += 1

              }

            }

          } else {
            assert(false, "Error: Unsupported free eli search approach: " + freeEliSearchApproach)
          }

        }

        (freeEli, -1f)

      }

      @inline def unitProp = {

        while (!forceElis.isEmpty && conflictNogi == -1) {

          val eli = forceElis.firstInt()

          forceElis.remove(eli) //removeLastInt()

          setEliWithNogoodUpdates(eli)


        }

      }

      while (!completeModuloConflict && !stop) { // inner loop (candidate model generation) ----------------------------

        trials += 1

        //assert(orderNo + forceElisSize <= maxOrderNo, "Error: Maximum order exceeded")

        if (!recAssg)
          unitProp

        if (conflictNogi == -1) {

          if (nogoodExchangeProbability > 0 && maxNumberOfCompetingModelSearchThreads > 1) nogoodExchangePool.forEach { case (i: (ArrayEliUnsafe, Int)) => {

            if (i._2 != threadNo && rngLocal.nextFloat() <= nogoodExchangeProbability && i._1.size() < nogoodExchangeSizeThresh) {

              log("this thread: " + threadNo + ", nogood from other thread " + i._2)

              addNogood(i._1)

              nogoodExchangePool.remove(i._1)

            }
          }
          }

          //nogoodExchangePool.clear()

          if (conflictNogi == -1) {

            completeModuloConflict = setEliCounter == noOfAllElis / 2

            if (!completeModuloConflict) {

              // Branching...

              val (freeEli, enforceProb) = findFreeEli

              if (freeEli != -1) {

                val branchingEli = if (rngLocal.nextFloat() < beliTh.max(enforceProb)) freeEli else negateEli(freeEli)

                log("branchingEli: " + branchingEli)

                dl += 1

                //assert(dl < maxDecisions, "ERROR: Maximum number of decision levels exceeded: " + dl)

                setEliWithNogoodUpdates(branchingEli)

                val restartCutOffUnits = Math.sqrt(dl + noOfConflictsAfterRestart) //(dl * (noOfConflictsAfterRestart + 1)) / 50000  //+ ((System.nanoTime() - restartTimer) / 1000000000l )

                if (restartTriggerConf._2 != -2 && ((restartTriggerConf._1 && restartCutOffUnits > geomNoOfConflictsBeforeRestart ||
                  !restartTriggerConf._1 && noOfConflictsAfterRestart > noOfConflictsBeforeRestart))) { // restart

                  if (showProgressStats)
                    println("Restarting...")

                  restartTimer = System.nanoTime()

                  noOfRestarts += 1

                  if (restartTriggerConf._1)
                    geomNoOfConflictsBeforeRestart = Math.pow(restartTriggerConf._3, noOfRestarts.toDouble).toInt

                  if (removeLearnedNogoods > 0 && firstRecordedNogi >= 0 && firstRecordedNogi < nogiToNogood.size) {

                    val noOfNogoodsToRemove = ((nogiToNogood.size - firstRecordedNogi).toDouble * removeLearnedNogoods).toInt.max(1)

                    removeRecordedNogoods(firstNogi = firstRecordedNogi, lastNogi = firstRecordedNogi + noOfNogoodsToRemove - 1)

                    log(" Removed " + noOfNogoodsToRemove + " learned nogoods.")

                  }

                  if (shuffleNogoodsOnRestart) {

                    var k = 0

                    while (k < nogiToRemainder.size) {

                      shuffleArray(nogiToRemainder.get(k).pool, rngLocal)

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

                    println("Assigned = " + ((noOfPosElis - preciseUnassi).toDouble / noOfPosElis.toDouble * 100).toInt + " %")

                    println(" remaining unassigned atoms: " + preciseUnassi) // note that a 0 here doesn't mean we are finished since conflictNogi might be != -1

                  }

                }

              }

            }

          }

        }

        if (conflictNogi != -1) { // conflict handling

          completeModuloConflict = false

          if (dl == 0) {

            println("UNSAT") // Conflicting nogood: " + nogiToNogood.get(conflictNogi).toArray().mkString(","))

            return None

          }

          log("noOfConflictsAfterRestart: " + noOfConflictsAfterRestart + "  (noOfConflictsBeforeRestart: " + noOfConflictsBeforeRestart + ")")

          //log("\nconflictNogi = " + nogiToNogood.get(conflictNogi).toArray.mkString(","))

          val (newLevel: Long, newNogood: ArrayEliUnsafe, sigma: Eli) = conflictAnalysis(conflictNogi)

          // we add a new nogood and jump back to decision level newLevel

          addNogood(newNogood)

          jumpBack(newLevel)

          setEliWithNogoodUpdates(negateEli(sigma))

          activUpdateVal *= incActivUpdateValueOnNewNogoodFactor

          if (reviseActivDiv != 1 && noOfConflictsAfterRestart % reviseActivFreq == 0) {

            var eli = 0

            //var activSum = 0

            while (eli < noOfAllElis) {

              val na = eliActiv.get(eli) / reviseActivDiv

              eliActiv.update(eli, na)

              //activSum += na.toInt

              eli += 1

            }

            //println("activSum = " + activSum)

          }

        }

      } // ---------------------------------------------------------------------------------------------------------------

      if (!stop) {

        log("\n! End of inner loop reached !")

        log("orderNo = " + orderNo)

        log("^^^^^^ Timer inner loop: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms\n")

        //assert(setEliCounter == noOfAllElis / 2) // NB: if this assertion fails (exception), thread blocks or long delay (!?)

        val modelCandidate: (Array[Eli], IntOpenHashSet) = { // we must not return an Array here, as we might use the result as a cache key

          import scala.collection.JavaConverters._

          lazy val restoredNogoods = nogiToNogood.asScala.toArray.map(_.toArray).to[ArrayBuffer]

          removedNogoodsPerAtomOpt.foreach { removedNogoodsPerAtom: mutable.TreeMap[Eli /*atom*/ , ArrayBuffer[Array[Eli]]] => {
            // we've performed variable elimination in class Preparation and need to restore
            // now the removed variables (atoms) with their correct polarities:satmo

            val removedNogoodsPerAtomArray = removedNogoodsPerAtom.toArray

            removedNogoodsPerAtomArray.foreach { case (atom: Eli, _) => {

              clearInPass(atom)

              clearInPass(negatePosEli(atom))

            }
            }

            removedNogoodsPerAtomArray.reverse.foreach { case (atom: Eli, removedNogoods: ArrayBuffer[Array[Eli]]) => {

              restoredNogoods.appendAll(removedNogoods)

              setInPass(atom)

              val isAtomPos = restoredNogoods.forall(nogood => !nogood.forall(isSetInPass(_)))

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

          //modelCand.sizeHint(noOfPosAtomElis)

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

        val checkResult: (Boolean, Array[Eli]) = if ((satMode || (progIsTight && !enforceChecks)))
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

          log("Stopping competing single-model solver instance threads")

          stop = true // stops competing threads (but not necessarily immediately)

          def sanityChecks = { // for debugging only

            println("Performing sanity checks on model candidate... (search approach was: " + freeEliSearchApproach + ")")

            assert(setEliCounter == noOfAllElis / 2)

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

                  log("Inconsistency: both " + eli + " and " + negateEli(eli) + " are set")

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

              if ( /*!nogood.isEmpty && */ nogood.forall(assignment.contains(_))) {

                violatedNogoods += 1

                println("Violated nogood (must not happen): nogi: " + nogi + " = " + nogood.mkString(","))

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

            val dimacsDirectClauseNogoodsOpt = prep.aspifOrDIMACSParserResult.directClauseNogoodsOpt

            dimacsDirectClauseNogoodsOpt.foreach((directDIMACSClauseNogoods: ArrayBuffer[Array[Eli]]) => {

              var dnogi = 0

              while (dnogi < directDIMACSClauseNogoods.length) {

                val dnogood: Array[Int /*"symbol" integers pos/neg, not elis*/ ] = directDIMACSClauseNogoods(dnogi)

                assert(!dnogood.isEmpty)

                if (dnogood.forall(assignment.contains(_))) {

                  violatedDNogoods += 1

                  println("  Violated direct clause nogood (must not happen): dnogi: " + dnogi + " = " + dnogood.mkString(","))

                }

                dnogi += 1

              }

            })

            println("#Violated direct clause nogoods: " + violatedDNogoods)

            // Finally, in SAT mode, we check against the original DIMACS CNF clauses:

            if (satMode) println("Checking original DIMACS clauses...")

            val modelCandWithSymbols = modelCandidate._1.map(symbols(_))

            //log("modelCandWithSymbols (recall that the numbers which are SAT symbols (variables) are different from corresponding atom elis!)\n" + modelCandWithSymbols.mkString(" "))

            var checkedDIMACSclauses = 0

            val violatedDIMACSClauses: Boolean = aspifOrDIMACSParserResult.clauseTokensOpt.isDefined &&
              aspifOrDIMACSParserResult.clauseTokensOpt.get.exists(clause => {

                val clauseFulfilled = clause.exists((dimacsVarPN: Int) => {

                  if (dimacsVarPN > 0)
                    modelCandWithSymbols.contains(dimacsVarPN.toString)
                  else
                    !modelCandWithSymbols.contains((-dimacsVarPN).toString)

                })

                if (!clauseFulfilled)
                  println("  Violated original CNF clause: " + clause.mkString(" "))

                checkedDIMACSclauses += 1

                !clauseFulfilled

              })

            if (satMode) assert(checkedDIMACSclauses == aspifOrDIMACSParserResult.clauseTokensOpt.get.length &&
              checkedDIMACSclauses == dimacsDirectClauseNogoodsOpt.get.length)


            if (satMode) println("Any violated original DIMACS clauses: " + violatedDIMACSClauses + " (checked: " + checkedDIMACSclauses + ")")

            if (!allElitsCovered || !noInconsistencies || violatedNogoods > 0 || violatedDNogoods > 0 || violatedDIMACSClauses) {

              System.out.println("\n\\/\\/\\/\\/ Internal error: Sanity checks failed on model candidate!\n")

              sys.exit(-5)

            }


          }

          //log("pass:\n " + pass.mkString(","))

          if (enforceChecks || debug)
            sanityChecks

          if (satMode) log("+++ ++ + Found a satisfying assignment") else log("*** ** * Found an answer set ")

          //println("  with symbols: " + modelCandidate.map(symbols(_)).mkString(" "))

          log("  at " + ((System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000) + " ms")

          modelOpt = Some(modelCandidate)

        } else { // Model candidate bounced back, so we need to retry...

          log("\\\\\\\\\\\\\\\\ \nNot an answer set: " + modelCandidate + "\n Remainder: " + checkResult._2)

          log("Model cand with symbols: " + modelCandidate._1.map(predI => symbols(predI)).mkString(" "))

          assert(!progIsTight)

          // We add loop nogoods and try again (required only for non-tight programs).

          // We use a modified variant of the ASSAT approach; see the revised paper http://www.cs.ust.hk/~flin/papers/assat-aij-revised.pdf
          // for the latter (NB: the original ASSAT paper contains a mistake).
          // In contrast to ASSAT, we use regular CDNL conflict handling on loop nogood violations.

          val mMinusR = checkResult._2

          val loopsOverMminus: mutable.Seq[ArrayBuffer[Eli]] = {

            sccCache.getOrElseUpdate(mMinusR, {

              val t = {

                val tR = new IntObjectHashMap[List[Eli]]() // this is ugly, but Java's HashMaps are in this case faster than Scala's (as of 2.12)

                /*
                val dgEntries = dependencyGraph.entrySet.iterator

                while (dgEntries.hasNext) {

                  val entry: util.Map.Entry[Eli, List[Eli]] = dgEntries.next()

                  if (mMinusR.contains(entry.getKey))
                    tR.put(entry.getKey, entry.getValue)
                  else
                    tR.put(-1, Nil)

                }*/

                val dgEntries = dependencyGraph.keys()

                dgEntries.forEach(key => {

                  if (mMinusR.contains(key.value))
                    tR.put(key.value, dependencyGraph.get(key.value))
                  else
                    tR.put(-1, Nil)

                })

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

              val tKeys: IntObjectHashMap[List[Eli]]#KeysContainer = t.keys()

              val dependencyGraphInducedByMminus = new IntObjectHashMap[List[Eli]]()

              tKeys.forEach(key => {

                dependencyGraphInducedByMminus.put(key.value, t.get(key.value).filter(tKeys.contains(_)))

              })


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

          if (true || conflictNogi == -1) {

            //log("No loop nogood triggers conflict, restarting...")

            jumpBack(-1)

          } else { // doesn't work (why?)

            assert(false)

            val (newLevel, learnedNogood, sigma) = conflictAnalysis(conflictNogi)

            addNogood(learnedNogood)

            jumpBack(newLevel)

            setEliWithNogoodUpdates(negateEli(sigma))

          }

        }

      }

    }

    // --------- end single supported model

    println("\nSingle model solving time: " + (System.nanoTime() - timerBatchSamplingStartPreciseNs) / 1000000 + " ms")

    modelOpt

  }

}