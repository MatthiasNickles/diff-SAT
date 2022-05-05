/**
  * diff-SAT
  *
  * Copyright (c) 2018-2022 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package solving

import java.util
import java.util.concurrent._

//import jdk.internal.vm.annotation.Contended
//import sun.misc.Contended

import aspIOutils._

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, Variable}

import input.diffSAT._
import it.unimi.dsi.fastutil.ints.{IntOpenHashSet, _}

import sharedDefs._

import input.UNSAFEhelper._
import input.{UNSAFEhelper, diffSAT}

import utils._
import utils.Various._

import scala.collection.{Seq, mutable}
import scala.collection.mutable.ArrayBuffer

/**
  * Main multimodel solver and propositional model sampling class.
  *
  * @todo further refactoring
  * @author Matthias Nickles
  *
  */
class SolverMulti(prep: Preparation) {

  import prep._

  case class SampleMultiModelsConf(
                                    requestedNoOfModelsBelowThresholdOrAuto: Int,
                                    noOfSecondaryModels: Int,
                                    prep: Preparation,
                                    requestedNumberOfModels: Int /*-1: stopSolverThreads at minimum number of models required to reach threshold*/ ,
                                    costThreshold: Double, // the target cost
                                    maxIt: Int,
                                    maxSamplingTimeMs: Long,
                                    offHeapGarbageCollectionMode: Int /*0: never do any off-heap ("unsafe memory") garbage collection,
    1: always perform off-heap garbage collection when either (an estimate of) free off-heap memory falls
    below x% or UNSAFEhelper.debugMode=true,
    2: enforces garbage collection after each model, regardless of available memory,
    -1: auto (omits off-heap garbage collections for
    sampling tasks (since these typically generate small models and need to be fast) or if only
    a single model has been requested by the user, in which case occupied off-heap memory is simply released by the OS on program exit)*/);

  val localSingleSamplerThreadPool = /*Executors.newFixedThreadPool(3)*/
    if (false /*localSolverParallelThresh == localSolverParallelThreshMax*/ )
      null.asInstanceOf[ThreadPoolExecutor] else
      new ThreadPoolExecutor(3 /*TODO: set depending on whether parallel unit propagation specified*/ ,
        8 /*<- TODO: set depending on unit prop config and #CPUs*/ , 10, TimeUnit.SECONDS,
        new LinkedBlockingQueue[Runnable](256) /*new SynchronousQueue[Runnable]*/) // used for various local (within a solver thread) multithreading


  val parallelBCPThreadPool: ExecutorService = localSingleSamplerThreadPool

  /*@Contended*/ val sampledModels = ArrayBuffer[(Array[Eli], IntOpenHashSet)]()

  //@volatile var refreshedBestPhasesGlobal: Int = 0

  var maxCompetingSolverThreads: Int = (if (maxSolverThreadsR < 0) (if (noOfAbsElis < -maxSolverThreadsR)
    1
  else
    Math.ceil(Runtime.getRuntime().availableProcessors() / (if (abandonOrSwitchSlowThreads != 0 && abandonOrSwitchSlowThreads != 4)
      1.4d else 2.2d/*1.6d*/))).toInt.min(upperLimitAutoSolverThreads)
  else
    maxSolverThreadsR).max(1)

  val threadConfs: Array[SolverThreadSpecificSettings] = Array.ofDim[SolverThreadSpecificSettings](maxCompetingSolverThreads)

  @volatile var optimalSingleSolverConfOpt: Option[SolverThreadSpecificSettings] = None

  val uncertainAtomsUpdateExecutorService = new ThreadPoolExecutor(2, 2, 3, TimeUnit.SECONDS, new LinkedBlockingQueue[Runnable])

  //private[this] val unsafe: Unsafe = unsafeRefl.get(null).asInstanceOf[Unsafe] // we can prevent val access via
  // automatically generated getter method like this (using private [this]), but doesn't seem to make a difference, because of inlining, except in profiler like VisualVM

  /**
    * Computes both the total cost and all inner costs (the sub-costs which add up to the total cost).
    * Call only after updating the measured atom frequencies.
    *
    * Notice that this function does _not_ update the costs with the current counts of measured atoms in the sample, so
    * before calling this function it needs to be ensured that the values of the measured variables are up-to-date.
    *
    * @param costFctsInner
    * @return (total cost (=sum of inner costs), array of inner costs)
    */
  @inline def currentCosts(costFctsInner: Array[DifferentialFunction[DoubleReal]]): (Double /*total cost*/ ,
    Array[Double /*inner costs*/ ]) = {

    if (costFctsInner.length == 0)
      (0d, Array[Double]())
    else {

      var costUnnorm = 0d

      val innerCosts = Array.ofDim[Double](costFctsInner.length)

      var i = 0

      while (i < costFctsInner.length) {

        val costInner = costFctsInner(i).getReal

        costUnnorm += costInner

        innerCosts(i) = costInner

        i += 1

      }

      (costUnnorm / costFctsInner.length.toDouble, innerCosts)

    }

  }

  @inline def updateAtomsFreqs(mOpt: Option[IntOpenHashSet],
                               measuredAtomElis: Array[Eli],
                               sampledModels /*after(!) adding new model mOpt*/ : ArrayBuffer[(Array[Eli], IntOpenHashSet)],
                               fromScratch: Boolean = false): Unit = {

    val newModelsCount: Double = sampledModels.length.toDouble

    if (fromScratch) {

      var i = 0

      val il = measuredAtomElis.length

      while (i < il) {

        val measuredAtomEli: Eli = measuredAtomElis(i)

        val measureAtomVar: Variable[DoubleReal] = eliToVariableInCostFunctions(measuredAtomEli)

        var count = 0

        var j = 0

        while (j < sampledModels.length) {

          val model = sampledModels(j)

          if (model._2.contains(measuredAtomEli))
            count += 1

          j += 1

        }

        measureAtomVar.set(new DoubleReal(count.toDouble / newModelsCount))

        i += 1

      }

    } else {

      assert(mOpt.isDefined)

      mOpt.foreach(m => {

        if (measuredAtomElis.length > localSolverParallelThresh * 5) {

          val tasks = new util.ArrayList[Runnable]()

          val cdl = new CountDownLatch(2)

          tasks.add(new Runnable() {

            override def run(): Unit = {

              var i = 0

              val il = measuredAtomElis.length / 2

              while (i < il) {

                val measuredAtomEli = measuredAtomElis(i)

                val measureAtomVar = eliToVariableInCostFunctions(measuredAtomEli)

                measureAtomVar.set(new DoubleReal((measureAtomVar.getReal * (newModelsCount - 1d) +
                  (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount))

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

                val measureAtomVar = eliToVariableInCostFunctions(measuredAtomEli)

                measureAtomVar.set(new DoubleReal((measureAtomVar.getReal * (newModelsCount - 1d) +
                  (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount))

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

            val measureAtomVar = eliToVariableInCostFunctions(measuredAtomEli)

            measureAtomVar.set(new DoubleReal((measureAtomVar.getReal * (newModelsCount - 1d) +
              (if (m.contains(measuredAtomEli)) 1d else 0d)) / newModelsCount))

            i += 1

          }

        }

      })

    }

  }

  @inline def tempUpdMeasuredAtomsFreqs(appending: Boolean,
                                        newModel: IntOpenHashSet,
                                        measuredAtomElis: Array[Eli],
                                        modelsCount: Int /* <--- excluding newModel */): Unit = {

    assert(appending)

    if (appending) {

      var i = 0

      val il = measuredAtomElis.length

      while (i < il) {

        val measuredAtomEli = measuredAtomElis(i)

        val measureAtomVar = eliToVariableInCostFunctions(measuredAtomEli)

        val newValue = if (newModel.contains(measuredAtomEli))
          (measureAtomVar.getReal * modelsCount + 1d) / (modelsCount + 1d)
        else
          (measureAtomVar.getReal * modelsCount) / (modelsCount + 1d)

        measureAtomVar.set(new DoubleReal(newValue))

        i += 1

      }

    } /* nope, gives NaN for #models = 0
    else {  // undoes one previous appending call

      var i = 0

      val il = measuredAtomElis.length

      while (i < il) {

        val measuredAtomEli = measuredAtomElis(i)

        val measureAtomVar = eliToVariableInCostFunctions(measuredAtomEli)

        val newValue = if (newModel.contains(measuredAtomEli))
          (-1d + measureAtomVar.getReal + modelsCount * measureAtomVar.getReal) / (1d + modelsCount)
        else
          (1d + modelsCount) * measureAtomVar.getReal / modelsCount

        measureAtomVar.set(new DoubleReal(newValue))

        i += 1

      }

    }*/

  }

  @inline def predictTotalCostWithHypotheticalModel(newModel: IntOpenHashSet,
                                                    measuredAtomElis: Array[Eli]): Double = {

    //  println("\nBefore:\n" + measuredAtomElis.map(eli => eliToVariableInCostFunctions(eli).getReal).mkString(","))

    val originalMeasuredAtomValues: Array[Double] = measuredAtomElis.map(eli => eliToVariableInCostFunctions(eli).getReal)

    tempUpdMeasuredAtomsFreqs(appending = true,
      newModel = newModel,
      measuredAtomElis = measuredAtomElis,
      sampledModels.length)

    // println("  With hypothetical update:\n" + measuredAtomElis.map(eli => eliToVariableInCostFunctions(eli).getReal).mkString(","))

    val predictedNewTotalCost = currentCosts(costFctsInner)

    measuredAtomElis.zipWithIndex.map { case (eli, index) => eliToVariableInCostFunctions(eli).set(new DoubleReal(originalMeasuredAtomValues(index))) }

    // println("\nAfter reverting to original:\n" + measuredAtomElis.map(eli => eliToVariableInCostFunctions(eli).getReal).mkString(","))

    predictedNewTotalCost._1

  }

  @inline def updateMeasuredAtomsFreqsAndComputeCost(mOpt: Option[IntOpenHashSet],
                                                     measuredAtomElis: Array[Eli],
                                                     sampledModels /*after adding new model m*/ : ArrayBuffer[(Array[Eli], IntOpenHashSet)],
                                                     costFctsInner: Array[DifferentialFunction[DoubleReal]],
                                                     fromScratch: Boolean = false,
                                                     computeCosts: Boolean = true
                                                    ):
  Option[(Double /*total cost*/ , Array[Double /*inner costs*/ ])] = {

    // We update the current frequencies of the measured atoms (the values of the freqx variables in costs/cost derivatives):

    updateAtomsFreqs(mOpt,
      measuredAtomElis,
      sampledModels,
      fromScratch)

    if (!computeCosts)
      None
    else
      Some(currentCosts(costFctsInner))

  }

  /**
    * Samples multiple models (answer sets or SAT models) until the total cost function falls below the specified threshold
    * (or the maximum number of trials has been reached or some specified minimum number of models have been generated).
    * Don't invoke directly - when using the User API, use [[input.ProbabilisticAnswerSetProgram#solve(input.SolverParametersOverlay, scala.Option)]] instead.
    *
    * @param sampleMultiConf
    * @return (sequence of sampled symbolic models, sequence of pairs (model as array of elis, model as eli hash set))
    */
  def sampleMulti(sampleMultiConf: SampleMultiModelsConf): SamplingResult /*(mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)], Long)*/ = {

    import sampleMultiConf._

    if (UNSAFEhelper.debugMode) println("Available off-heap mem at start of sampleMulti: " + approxSizeOfCurrentFreeUnsafeMemory() + " (" + approxSizeOfCurrentFreeUnsafeMemory().toDouble / 1073741824d + " GB)")

    @inline def printMeasuredEliFreqs: Unit = {

      var i = 0

      val il = measuredAtomsElis.length

      while (i < il) {

        val measuredAtomEli: Eli = measuredAtomsElis(i)

        println("   f(" + symbols(measuredAtomEli - 1) + ") = " + new DoubleReal(sampledModels.count(_._2.contains(measuredAtomEli)).toDouble / sampledModels.length.toDouble))

        i += 1

      }

    }

    var totalCost: Double = Double.MaxValue

    var it = 1

    val samplingTimerNs = System.nanoTime()

    val stagnationTol = costThreshold / stagnationTolDiv

    var oldTotalCost = Double.MaxValue

    var costDifForStagn = Double.MaxValue

    val showNumDiffProgressForDebugging = debug

    var minCostSf = Double.MaxValue

    if (enforceStopWhenSampleSizeReached)
      stomp(-5012)

    if (requestedNumberOfModels != 1 && (!freeOrReassignDeletedNogoodMemory || freeDeletedNogoodMemoryApproach != 2))
      stomp(-5009, "If -n 1 is not specified, freeOrReassignDeletedNogoodMemory must be true and freeDeletedNogoodMemoryApproach must be 2")

    if (requestedNumberOfModels != 1 && nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0)
      stomp(-5009, "If -n 1 is not specified, nogoodRemovalUsingRecyclingFromTotalHistoryEvery must be 0 (deactivated)")

    if (writeRuntimeStatsToFile) {

      assert(diffSAT.stats != null)

      input.diffSAT.stats.writeEntry(key = "timeoutMs", value = timeoutMs, solverThreadNo = 0 /*0: outside solver solver thread or thread irrelevant */)

      input.diffSAT.stats.writeEntry(key = "targetCost", value = costThreshold, solverThreadNo = 0)

      input.diffSAT.stats.writeEntry(key = "requestedNumberOfModels", value = requestedNumberOfModels, solverThreadNo = 0)

    }

    @inline def samplingContinueCriterion(it: Nogi, totalCost: Double, costDifForStagn: Double): Boolean = (it < maxIt &&
      System.currentTimeMillis <= maxSamplingTimeMs &&
      (requestedNumberOfModels <= -1 && (totalCost.isNaN || totalCost > costThreshold) ||
        requestedNumberOfModels >= 0 && (sampledModels.length < requestedNumberOfModels || (totalCost.isNaN || totalCost > costThreshold) && !enforceStopWhenSampleSizeReached)) &&
      !(stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost < Double.MaxValue &&
        (requestedNumberOfModels <= -1 || sampledModels.length >= requestedNumberOfModels)))

    @inline def offHeapGarbageCollectionCriterion(lockedSolverData: Boolean): Boolean = { // also see offHeapGarbageReleaseCriterion().
      // Both collecting off-heap garbage and releasing it is costly.

      val r = !lockedSolverData && (offHeapGarbageCollectionMode == 1 || offHeapGarbageCollectionMode == 2 || offHeapGarbageCollectionMode == -1 && (

        !(sampleMultiConf.requestedNumberOfModels == 1 && sampleMultiConf.noOfSecondaryModels == 1 ||
          sampleMultiConf.requestedNumberOfModels == -1 && sampleMultiConf.noOfSecondaryModels == -1)
        // i.e., with possible multimodel sampling (... == -1), by default we do NOT perform any off-heap garbage collections, for performance reasons

        ))
      // If lockedSolverData (from reuseSolverData), we need to postpone garbage collection and release until after the outer sampling loop

      r

    }

    @inline def offHeapGarbageReleaseCriterion(noFurtherModels: Boolean, lockedSolverData: Boolean): Boolean = { // also see offHeapGarbageCollectionCriterion.
      // Both collecting off-heap garbage and releasing it is costly.

      offHeapGarbageCollectionCriterion(lockedSolverData) && !(offHeapGarbageCollectionMode == -1 && noFurtherModels) &&
        (UNSAFEhelper.debugMode || offHeapGarbageCollectionMode == 2 ||
          approxSizeOfCurrentFreeUnsafeMemory.toFloat < approxSizeOfInitialFreeUnsafeMemory.toFloat * offHeapGarbageReleaseThreshold)

    }

    var outerLoopIncomplete = true

    var reentrySolverDataOpt: Option[SingleSolverThreadData] = None

    if (allowNumFiniteDiff) { // we use auto/sym diff (where available for a parameter atom) and/or finite differences (sort of discrete numerical differentiation) to approximate the partial
      // derivatives. The latter is mainly useful if automatic differentiation (i.e., nablaInner) cannot be used, i.e., for parameter atoms which
      // aren't measured atoms (i.e., don't appear in the cost function term), as it is the case for weight learning and Inductive Logic Programming.

      do {

        //val noOfModelsBeforeProbes = sampledModels.length

        val useRandomDiffQuot = rngGlobal.nextDouble() < numFinDiffShuffleProb

        val diffQuotsPerParameter: Predef.Map[Eli, Double] = parameterLiteralElisArray.take(parameterLiteralElisArray.length / 2 /*<- i.e., positive literals only*/).map {
          case probingParamAtomEli: Eli => {

            if (useRandomDiffQuot) {

              if (showNumDiffProgressForDebugging) println(" Random diffquot step in allowNumFiniteDiff")

              (probingParamAtomEli, rngGlobal.nextDouble())

            } else {

              val diffQuotPerAutoDiff = deficitByDeriv(probingParamAtomEli) // we try to get an analytical (automatic differentiation) diff result first

              if ((!diffQuotPerAutoDiff.isNaN || ignoreParamIfNotMeasured))
                (probingParamAtomEli, diffQuotPerAutoDiff)
              else { // this branch is only entered if we couldn't get a value analytically:

                if (showNumDiffProgressForDebugging) println(" Probing for parameter (hypothesis) atom " + symbols(probingParamAtomEli - 1) + "...")

                if (showNumDiffProgressForDebugging) println("  Probing for +" + symbols(probingParamAtomEli - 1) + "...")

                val rnOrderParamEli: Predef.Map[Integer, Double] = deficitOrderedUncertainLiteralsForJava.map(p => (p, {

                  1d / deficitOrderedUncertainLiteralsForJava.indexOf(p).toDouble / deficitOrderedUncertainLiteralsForJava.length.toDouble // heuristic

                })).toMap

                val rnOrderParamEliMin = -1d

                val rnOrderParamEliMax = 1d

                java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
                  // we push the probing atom to the top or bottom of the branching literals priority ranking

                  if (parameterLiteralEli == probingParamAtomEli)
                    rnOrderParamEliMin
                  else if (parameterLiteralEli == negateEli(probingParamAtomEli))
                    rnOrderParamEliMax
                  else
                    rnOrderParamEli(parameterLiteralEli)

                }))

                val (newModelOpt: Option[(Array[Eli], IntOpenHashSet)], _) = sampleSingleRacing(maxSamplingTimeMs = maxSamplingTimeMs, collectOffHeapGarbage = offHeapGarbageCollectionCriterion(reuseSolverData))

                if (newModelOpt.isEmpty) { // UNSAT or aborted

                  finalActionsAfterSampling()

                  return solving.SamplingResult(mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)](), System.nanoTime() - samplingTimerNs)

                }

                val costWithProbePlusH = predictTotalCostWithHypotheticalModel(newModelOpt.get._2, measuredAtomsElis)

                if (showNumDiffProgressForDebugging) println("  Probing for -" + symbols(probingParamAtomEli - 1) + "...")

                java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
                  // we push the probing atom to the top or bottom of the branching literals priority ranking

                  if (parameterLiteralEli == probingParamAtomEli)
                    rnOrderParamEliMax
                  else if (parameterLiteralEli == negateEli(probingParamAtomEli))
                    rnOrderParamEliMin
                  else
                    rnOrderParamEli(parameterLiteralEli)

                }))

                val (newModelOptMinusH: Option[(Array[Eli], IntOpenHashSet)], _) = sampleSingleRacing(maxSamplingTimeMs = maxSamplingTimeMs,
                  collectOffHeapGarbage = offHeapGarbageCollectionCriterion(reuseSolverData))

                if (newModelOptMinusH.isEmpty) { // UNSAT or aborted

                  finalActionsAfterSampling()

                  return solving.SamplingResult(mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)](), System.nanoTime() - samplingTimerNs)

                }

                val costWithProbeMinusH = predictTotalCostWithHypotheticalModel(newModelOptMinusH.get._2, measuredAtomsElis)

                val diffQuot = (costWithProbePlusH - costWithProbeMinusH) // * noOfModelsBeforeProbes.toDouble
                // NB: negative diffQuote increases(!) the likeliness that the respective parameter atom will be included in the next model.
                // NB: since in the solver we only need to compare these "quotients", division by 2h is redundant.

                if (showNumDiffProgressForDebugging) println(" ==> diffQuot for param atom " + symbols(probingParamAtomEli - 1) + " = " + diffQuot)

                (probingParamAtomEli, diffQuot)

              }

            }

          }

        }.toMap

        val ordering = if (diversifyLight || diversify) {

          //shuffleArray(deficitOrderedUncertainLiteralsForJava, rg = rngGlobal)  // not useful here, doesn't reliably achieve shuffling of elements with equal diffQuots due to IEEE arithmetics (e.g., -0 vs. 0)

          val nnn = mutable.HashMap[Integer, Double]() ++ deficitOrderedUncertainLiteralsForJava.map(_ -> (rngGlobal.nextDouble() - 0.5d) / 1e12d /*1e12d*/)

          Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
            // NB: sorting algo is stable

            val x = diffQuotsPerParameter.get(parameterLiteralEli)

            val r: Double = x.getOrElse(-diffQuotsPerParameter.get(negateNegEli(parameterLiteralEli)).getOrElse(0d))

            r + nnn(parameterLiteralEli)

          })

        } else {

          Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
            // NB: sorting algo is stable, but 0 vs. -0 issue (see above)

            val x = diffQuotsPerParameter.get(parameterLiteralEli)

            val r = x.getOrElse(-diffQuotsPerParameter.get(negateNegEli(parameterLiteralEli)).getOrElse(0d))

            r

          })

        }

        java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, ordering)

        // We compute the actual new model (the one we keep in sampledModels):
        val (newModelOpt: Option[(Array[Eli], IntOpenHashSet)], newReentrySolverDataOpt: Option[SingleSolverThreadData]) =
          sampleSingleRacing(collectOffHeapGarbage = offHeapGarbageCollectionCriterion(reuseSolverData),
            maxSamplingTimeMs = maxSamplingTimeMs, reentrySingleSolverThreadDataOpt = reentrySolverDataOpt)

        if (newModelOpt.isEmpty) { // UNSAT or aborted

          finalActionsAfterSampling()

          return solving.SamplingResult(mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)](), System.nanoTime() - samplingTimerNs)

        }

        sampledModels.append(newModelOpt.get)

        if (reuseSolverData)
          reentrySolverDataOpt = newReentrySolverDataOpt

        totalCost = if (ignoreParamVariablesR) Double.NegativeInfinity
        else
          updateMeasuredAtomsFreqsAndComputeCost(Some(newModelOpt.get._2),
            measuredAtomElis = measuredAtomsElis,
            sampledModels,
            costFctsInner = costFctsInner,
            fromScratch = false /*true*/ ,
            computeCosts = true // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
          ).get._1

        costDifForStagn = Math.abs(oldTotalCost - totalCost)

        oldTotalCost = totalCost

        minCostSf = minCostSf.min(totalCost)

        //println("minCostSf = " + minCostSf)

        if (resetsNumericalOuterLoopOnStagnation > 0 && costDifForStagn < stagnationTol && totalCost > costThreshold) {

          if (showNumDiffProgressForDebugging) println("\nResetting samples (stagnation detected; costDifForStagn = " + costDifForStagn + ")\n\n")

          sampledModels.clear()

          oldTotalCost = Double.MaxValue

          totalCost = oldTotalCost

          resetsNumericalOuterLoopOnStagnation -= 1

        }

        if (showProgressStats) {

          if (showNumDiffProgressForDebugging) println("\nSampling in progress... Sampled " + sampledModels.length + " models.\nOuter-outer sampling iteration (with allowNumFiniteDiff = true, mixedScenario = " + (if (mixedScenario) "true" else "false") + ") " + it + " (of max " + maxIt + ") complete. " +
            "Current total cost: " + totalCost + " (threshold: " + costThreshold + "). #models: " + sampledModels.length + "\n")
          else if (it % 2000 == 0)
            println("\nSampling in progress... Sampled " + sampledModels.length + " models. Current total cost: " + totalCost + " (threshold: " + costThreshold + ")")

          if (writeRuntimeStatsToFile)
            input.diffSAT.stats.writeEntry(key = "totalCostIntermediate", value = totalCost, solverThreadNo = 0)

        }

        it += 1

        outerLoopIncomplete = samplingContinueCriterion(it = it, totalCost = totalCost, costDifForStagn = costDifForStagn)

        if (offHeapGarbageReleaseCriterion(noFurtherModels = !outerLoopIncomplete, lockedSolverData = reuseSolverData))
          offHeapGarbageCollectionFreeGarbage

      } while (outerLoopIncomplete)

      if (stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost > costThreshold)
        stomp(-5011)

      if (debug) println("minCostSf (over all samples models) = " + minCostSf)

    } else do { // the (mostly deprecated) simpler outer-outer sampling loop for purely _deductive_ probabilistic inference (measured atoms = parameter atoms) and plain SAT/ASP solving

      if (!ignoreParamVariablesR) {

        if (diversify) {

          //shuffleArray(deficitOrderedUncertainLiteralsForJava, rg = rngGlobal)  // not useful here, doesn't reliably achieve shuffling of elements with equal diffQuots due to IEEE arithmetics (e.g., -0 vs. 0)

          val nnn = deficitOrderedUncertainLiteralsForJava.map(_ -> (rngGlobal.nextDouble() - 0.5d) / 1e12d).toMap

          java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, /*deficitOrdering*/ Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
            // NB: sorting algo is stable, but 0 vs. -0 issue (see above)

            deficitByDeriv(parameterLiteralEli) + nnn(parameterLiteralEli)

          }))

        } else {

          java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, /*deficitOrdering*/ Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {

            deficitByDeriv(parameterLiteralEli)

          })) // unfortunately boxing (Integer) needed, to achieve custom sort order
          //java.util.Arrays.sort(deficitOrderedUncertainLiteralsForJava, deficitOrdering)

        }

      }

      val (newModelOpt: Option[(Array[Eli], IntOpenHashSet)], newReentrySolverDataOpt: Option[SingleSolverThreadData]) = sampleSingleRacing(collectOffHeapGarbage = offHeapGarbageCollectionCriterion(reuseSolverData),
        maxSamplingTimeMs = maxSamplingTimeMs, reentrySingleSolverThreadDataOpt = reentrySolverDataOpt)

      if (newModelOpt.isEmpty) { // UNSAT or aborted

        finalActionsAfterSampling()

        return solving.SamplingResult(mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)](), System.nanoTime() - samplingTimerNs)

      }

      sampledModels.append(newModelOpt.get)

      if (reuseSolverData)
        reentrySolverDataOpt = newReentrySolverDataOpt

      totalCost = if (ignoreParamVariablesR) Double.NegativeInfinity else updateMeasuredAtomsFreqsAndComputeCost(Some(newModelOpt.get._2),
        measuredAtomElis = measuredAtomsElis,
        sampledModels,
        costFctsInner = costFctsInner,
        fromScratch = false /*!hypothesisParamTargetWeightVariables.isEmpty*/ ,
        computeCosts = true // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
      ).get._1

      costDifForStagn = Math.abs(oldTotalCost - totalCost)

      oldTotalCost = totalCost

      if (showProgressStats)
        println("Sampling in progress... Sampled " + sampledModels.length + " models.\nOuter-outer sampling iteration " + it + " (of max " + maxIt + ") complete. " +
          "Current total cost: " + totalCost + " (threshold: " + costThreshold + ")")
      else if (it % 10 == 0)
        println("Sampling in progress... Sampled " + sampledModels.length + " models. Current total cost: " + totalCost + " (threshold: " + costThreshold + ")")

      if (writeRuntimeStatsToFile)
        input.diffSAT.stats.writeEntry(key = "totalCostIntermediate", value = totalCost, solverThreadNo = 0)

      it += 1

      outerLoopIncomplete = samplingContinueCriterion(it = it, totalCost = totalCost, costDifForStagn = costDifForStagn)

      if (offHeapGarbageReleaseCriterion(noFurtherModels = !outerLoopIncomplete, lockedSolverData = reuseSolverData))
        offHeapGarbageCollectionFreeGarbage

    } while (outerLoopIncomplete)

    if (stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost > costThreshold)
      stomp(-5011)

    if (requestedNumberOfModels <= -2 && -requestedNumberOfModels > sampledModels.length) { // we "fill up" the sample by uniformly sampling from the current sample

      if (showProgressStats)
        println("Sampling " + (-requestedNumberOfModels - sampledModels.length) + " further models (with replacement) by uniformly sampling from current sample...")

      val originalSampleSize = sampledModels.length

      do {

        val i = rngGlobal.nextInt(originalSampleSize)

        sampledModels.append(sampledModels(i))

      } while (-requestedNumberOfModels > sampledModels.length)

    }

    if (noOfSecondaryModels > 0) { // we uniformly sample from the overall sampledModels

      println("Sampling " + noOfSecondaryModels + " models (with replacement) uniformly from the multisolution...")

      var i = 1

      val secondarySampledModels = ArrayBuffer[(Array[Eli], IntOpenHashSet)]()

      while (i <= noOfSecondaryModels) {

        secondarySampledModels.append(sampledModels(rngGlobal.nextInt(sampledModels.length)))

        i += 1

      }

      sampledModels.clear()

      sampledModels.appendAll(secondarySampledModels)

    }

    if (showProbsOfSymbols) {

      println("Approximations:\n")

      val showFreqsOf = symbols.sorted.filterNot(_.contains("aux")).map(symbolToAbsEli(_))

      showFreqsOf.foreach(atomEli => {

        val freqInModels = sampledModels.count(_._1.contains(atomEli)).toDouble / sampledModels.length.toDouble

        println("Pr(" + symbols(atomEli - 1) + ") =(approx.) " + freqInModels)

      })

    }

    def finalActionsAfterSampling(): Unit = {

      if (reuseSolverData && noOfMinibenchmarkTrials > 1) // TODO: this is needed due to unknown bug which
      // causes an off-heap memory leak if reuseSolverData=true.
        stomp(-10000, "If noOfMinibenchmarkTrials > 1, sharedDefs.reuseSolverData needs to be false")

      //System.gc()

      if (offHeapGarbageCollectionCriterion(lockedSolverData = false)) { // with reuseSolverData=true within the sampling loop, we
        // couldn't collect model data garbage in the inner solver thread, we had to wait until this point.

        reentrySolverDataOpt.foreach(_.queueOffHeapGarbageInSingleSolver)

        // nope, as these are allocated outside the "mini-benchmarking" loop: aspifOrDIMACSParserResult.rulesOrClauseNogoods.foreach(_.foreach{ _.addToGarbage() })

      }

      if (offHeapGarbageReleaseCriterion(noFurtherModels = true, lockedSolverData = false))
        offHeapGarbageCollectionFreeGarbage

      val timedOut = System.currentTimeMillis > maxSamplingTimeMs && (totalCost > costThreshold || sampledModels.length < requestedNumberOfModels)
      // TODO (?): doesn't consider secondary models (switch -s)

      if (writeRuntimeStatsToFile) {

        input.diffSAT.stats.writeEntry(key = "totalCost", value = totalCost, solverThreadNo = 0)

        input.diffSAT.stats.writeEntry(key = "sampledModels", value = sampledModels.length, solverThreadNo = 0)

        input.diffSAT.stats.writeEntry(key = "targetCostReached", value = totalCost <= costThreshold, solverThreadNo = 0)

        input.diffSAT.stats.writeEntry(key = "targetNoOfModelsReached", value = sampledModels.length >= requestedNumberOfModels, solverThreadNo = 0)

        input.diffSAT.stats.writeEntry(key = "timedout", value = timedOut, solverThreadNo = 0)

      }

      if (timedOut) {

        stomp(-5018, "" + timeoutMs + "ms")

      } else if (totalCost <= costThreshold) {

        println("\nSampling complete; cost (over all models): " + totalCost + " (<= threshold " + costThreshold + ")\n" + sampledModels.length + " model(s) sampled (with replacement)\n")

      } else if (sampledModels.length > 0 /*otherwise UNSAT*/ ) {

        stomp(-5008, "\nCost reached: " + totalCost + " (> threshold " + costThreshold + ")")

      }

    }

    //println("Time for multi-model sampling: " + timerToElapsedMs(samplingTimer) + " ms\n")

    val sampledModelsUsingElisWithEvalResolved: ArrayBuffer[(Array[Eli], IntOpenHashSet)] = sampledModels.map { case (modelElis, _) => {

      val modelElisEvalResolved: Array[Eli] = modelElis.map((posEli: Eli) => {

        val sym = symbolsWithoutTranslation(posEli - 1) // e.g., _eval_("f(pn1(a))*2","?",1)  Note that after "?" there can be any number of user-specified extra arguments

        if (sym.startsWith(evalFactPrefix + "(") && sym.contains("\"?\"") /*<- important as there might be resolved _eval_ atoms also (i.e., without "?")*/ ) {

          val (term, extraArgs) = aspIOutils.splitEvalSymbol(sym)

          val evalFunOpt: Option[DifferentialFunction[DoubleReal]] = sampleMultiConf.prep.costsOpt.flatMap(_.evalExpressionToFct.get(term))

          if (evalFunOpt.isEmpty)
            stomp(-209, term)

          val resolvedEvalAtomSym = "_eval_(\"" + term + "\"," + (evalFunOpt.get.getReal * probabilisticFactProbDivider).toInt + extraArgs

          symbolsWithoutTranslation = symbolsWithoutTranslation.:+(resolvedEvalAtomSym) // hmmpff

          symbolsWithoutTranslation.length - 1

        } else
          posEli

      })

      (modelElisEvalResolved, new IntOpenHashSet(modelElisEvalResolved))

    }

    }

    val sampledModelsSymbolicWithNegLits = if (!satMode) {

      val symbolicModels = sampledModelsUsingElisWithEvalResolved.map(model => model._1.map(eli => symbolsWithoutTranslation(eli - 1)))

      symbolicModels // In ASP mode, any classically-negative literals are already symbols (e.g., "-a") whereas
      // default negation is represented by absence of the respective atom.

    } else { // In SAT-mode, we need to fill up the model for printing with negative literals if the positive literal isn't present. :

      val fullSATModelsWithNegLiterals = sampledModelsUsingElisWithEvalResolved.map((model: (Array[Eli], IntOpenHashSet)) => {

        // In SAT mode only, we need to fill up the model with negative literals if the respective positive literal isn't present:

        val fullModelWithSymbols: Array[Pred] = symbolsWithoutTranslation.map(symbol =>
          if (model._2.contains(symbol.toInt)) symbol else "-" + symbol)

        fullModelWithSymbols

      })

      fullSATModelsWithNegLiterals

    }

    //if (debug && satMode) println("sampledModelsSymbolic (positive literals only):\n" +
    //sampledModelsSymbolic.map((m: Array[String]) => m.map(_.toInt).sorted.mkString(" ")).mkString("\n"))

    finalActionsAfterSampling()

    solving.SamplingResult(sampledModelsSymbolicWithNegLits,
      sampledModelsUsingElisWithEvalResolved,
      System.nanoTime() - samplingTimerNs)

  }

  @inline def offHeapGarbageCollectionFreeGarbage: Unit = {

    freeGarbageOffHeapMem(Long.MaxValue)

    if (UNSAFEhelper.debugMode) println("Available off-heap memory after garbage collection   " + approxSizeOfCurrentFreeUnsafeMemory() + " (" + approxSizeOfCurrentFreeUnsafeMemory().toDouble / 1073741824d + " GB)")
    // Remark: there is sometimes a discrepancy (a few MB) between this and the amount which was available at the start of
    // sampleSingle() of unknown cause - perhaps some unaccounted slack generated by unsafe's memory management?

    if (UNSAFEhelper.debugMode) showRemainingAllocsDebug()

  }

  /** Samples a single model (answer set in case of ASP mode) using (possibly) multiple parallel solver threads which
    * compete against each other in discovering a model.
    * The model generated by this function consists of elis (literals represented as positive integers).
    *
    * @author Matthias Nickles
    * @return Option[model as array of elis, model as hash set of elis] or None (UNSAT)
    */
  def sampleSingleRacing(collectOffHeapGarbage: Boolean, maxSamplingTimeMs: Long,
                         reentrySingleSolverThreadDataOpt: Option[SingleSolverThreadData] = None): (Option[(Array[Eli], IntOpenHashSet)], Option[SingleSolverThreadData] /*<-- data from successful solver run, for optional reentry*/ ) = {
    // If the returned models list is empty, this can mean either UNSAT or UNKNOWN (inner solver aborted, e.g., timeout),
    // that is, at this level these two results cannot be distinguished from each other anymore.

    val sharedAmongSingleSolverThreads = new SharedAmongSingleSolverThreads(noOfAbsElis = noOfAbsElis)

    @volatile var preReportedMinUnassignedGlobal = noOfAllElis

    @volatile var minUnassignedGlobal = noOfAllElis // not precise - use for statistical or debugging purposes only

    @volatile var unsatMessagePrinted = false

    case class SolverThreadInfo(thread: Thread, progressNormalized: Double = 0d)

    val progressNormalizedPerThread = scala.collection.concurrent.TrieMap[Int, SolverThreadInfo]()

    val enforceProgressChecksEveryTrials = enforceProgressChecksEveryTrialsR

    val minimumTrialsBeforeFirstProgressCheck = 500.min(enforceProgressChecksEveryTrials)

    val threadChangeCheckFreq = Math.abs(abandonOrSwitchSlowThreads).toInt.max(1)

    var threadChangeCheckFreqState = threadChangeCheckFreq

    var threadChangeActions = 0

    /**
      * Computes a single model using one existing thread (but might launch further threads for sub-tasks).
      *
      * @author Matthias Nickles
      * @param singleSolverConf
      * @return Option[model as array of elis, model as hash set of elis] or None (UNSAT) or null (UNKNOWN satisfisability, e.g., timeout)
      */
    def sampleSingle(singleSolverConf: SolverThreadSpecificSettings,
                     collectOffHeapGarbage: Boolean,
                     maxSamplingTimeMs: Long,
                     singleSolverThreadData: SingleSolverThreadData,
                     reentry: Boolean): Option[(Array[Eli], IntOpenHashSet)] = {

      import singleSolverConf._

      import singleSolverThreadData._

      Thread.currentThread().setPriority(Thread.MAX_PRIORITY)

      progressNormalizedPerThread.put(threadNo, new SolverThreadInfo(thread = Thread.currentThread()))

      if (UNSAFEhelper.debugMode) resetMemTracerDebug() // use to find off-heap memory leaks

      if (UNSAFEhelper.debugMode) println("Available off-heap memory at start of sampleSingle:  " + approxSizeOfCurrentFreeUnsafeMemory() + " (" + approxSizeOfCurrentFreeUnsafeMemory().toDouble / 1073741824d + " GB)")

      if (nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0 && collectOffHeapGarbage)
        stomp(-5017, "With nogoodRemovalUsingRecyclingFromTotalHistoryEvery > 0 no complete off-heap garbage collection is possible")

      def unsat(): Unit = {

        if (!stopSolverThreads && !unsatMessagePrinted) {

          unsatMessagePrinted = true

          println("\n\nUNSAT " + (if (verbose) "\n  (reporting: solver thread $" + threadNo + ")" else ""))

        }

        //stopSolverThreads = true
        stopSingleSolverThreads()

        if (writeRuntimeStatsToFile)
          stats.writeEntry(key = "unsat", value = "true", solverThreadNo = 0)

      }

      def unknown(): Unit = {

        //stopSolverThreads = true
        stopSingleSolverThreads()

        println("\n\nUNKNOWN (inner solver timed out after " + timeoutMs + "ms)")  // note that the actual stomp warning occurs later (in callers)

        if (collectOffHeapGarbage)
          queueOffHeapGarbageInSingleSolver

      }

      @inline def printSingleLineProgress(trials: Int, noOfRemovedNogoods: Int): Unit = {

        val peakPercent = ((noOfAbsElis - minUnassignedGlobal).toDouble / noOfAbsElis.toDouble * 100).toInt.min(99)

        //val progressEstimGlobalPercent = ((1d - (Math.log10(minUnassignedGlobal + 5) / Math.log10(noOfAbsElis))) * 100).toInt.min(99)

        //val progressEstimThreadPercent = ((1d - (Math.log10(noOfAbsElis - orderNo + 1/*NB: not the overall minimum of thread*/) / Math.log10(noOfAbsElis))) * 100).toInt.min(99)

        //val trialsPerConflicts = noOfConflictsTotal.toDouble / trials


        /* nonsense?
                var violNogoodSum = 0

                var i = 0

                while (i < clarkNogoodsFinal.length) {

                  val ng: IntArrayUnsafeS = clarkNogoodsFinal(i)

                  val notViol = ng.exists(eli => {

                    isNotSetInPass(eli) && !isNotAbsSetInPass(eli)

                  })

                  if(!notViol)
                    violNogoodSum += 1

                  i += 1

                }

                if(violNogoodSum < sharedAmongSingleSolverThreads.minViolNogoodCountSum)
                  sharedAmongSingleSolverThreads.minViolNogoodCountSum = violNogoodSum
        */


        if (timeAtLastProgressPrintedNs > 0l) {

          val noOfNanosSinceLastProgressPrinted = System.nanoTime() - timeAtLastProgressPrintedNs

          val noOfPropagationsPerNanosecond = noOfPropagationsSinceLastProgressPrinted.toDouble / noOfNanosSinceLastProgressPrinted

          val noOfPropagationsPerSecond = (noOfPropagationsPerNanosecond * /*ms:1000000*//*sec:*/ 1000000000d).toLong

          avgNoPropagationsPerSecond = (noOfPropagationsPerSecond + noOfProgressUpdatesPrinted * avgNoPropagationsPerSecond) / (noOfProgressUpdatesPrinted + 1)

        }

        noOfProgressUpdatesPrinted += 1

        timeAtLastProgressPrintedNs = System.nanoTime()

        noOfPropagationsSinceLastProgressPrinted = 0

        //lazy val avgAbsEliScore = totalAbsEliScoreForDebugging / noOfAbsElis.toDouble // updated only at score rescaling, otherwise 0!

        lazy val removedNogoodsByPrefilter = omittedByPreFilterForNogoods.toDouble / (keptByPreFilterForNogoods + omittedByPreFilterForNogoods)

        if (!stopSolverThreads && peakPercent >= 0) {

          if (writeRuntimeStatsToFile) {

            input.diffSAT.stats.writeEntry(key = "minUnassignedGlobal", value = minUnassignedGlobal, solverThreadNo = 0)

            input.diffSAT.stats.writeEntry(key = "noOfConflictsTotal", value = noOfConflictsTotal, solverThreadNo = threadNo)

          }

          // The length of the following string should be below maxAssumedConsoleWidth to avoid scrolling of status line

          val pStr = ("@" + timerToElapsedMs(solverTimer) / 1000 + "s:" +
            "Rm:" + (if (minUnassignedGlobal <= 1) "1" /*2 is the finest resolution possible with minUnassignedGlobal*/
          else
            toKorM(minUnassignedGlobal)) + //"(<" + /*(if (peakPercent == 99) "<=" else "")*/ +(100 - peakPercent + 1) + "%)," + // not exact, since we sample this value not every trial
            //"Prgr~" + progressEstimGlobalPercent + "%|" +
            ",t$" + threadNo + ":" +
            //"Progress estim thread: " + progressEstimThreadPercent + "%, " +
            "C:" + toKorM(noOfConflictsTotal) + "," +
            //(if (debug) "violNgs:" + sharedAmongSingleSolverThreads.minViolNogoodCountSum + "," else "") +
            //(if (debug && computeAvgLR) "avgLR: " + (avgLR /*- (avgLR % 0.01)*/) + ", " else "") +
            /*includes nogoods shared with this thread -> */ "LN:" /*after removal*/ + (toKorM(getApproxNoOfLearnedNogoods) /*if (firstRecordedNogi >= 1) nogiClarkToNogoodReducible.size - firstRecordedNogi else 0*/) + "" +
            // (if (noOfRemovedNogoods >= 0) " after removing " + noOfRemovedNogoods + ", " else ", ") +
            "(DN:" + toKorM(noOfDeletedLearnedNogoods) + ",SN:" + toKorM(noOfSharedNogoods) + (if (learnedNogoodReduciblesListTotal != null) ",rcycld:" + toKorM(noOfRecycledLearnedNogoodsFromTotal) + " from:" + toKorM(learnedNogoodReduciblesListTotal.size) else "") + ")," +
            (if (debug /*&& threshForPreFilterLearnedNogoods != 0d */ && keptByPreFilterForNogoods > 0) "preFiltered:" + Math.floor(removedNogoodsByPrefilter * 1000) / 10 + "%," else "") +
            "Rs:" + toKorM(noOfRestarts) + "," +
            (if (debug) "PrgChks:" + noOfProgressChecks + "," else "") +
            (if(noOfRephasings > 0) "Rp:" + toKorM(noOfRephasings) + "(SLS:" + toKorM(noOfRephasingsUsingSLS) + ")," else "") +
            (if(noOfWeakRephasings > 0) "WRp:" + toKorM(noOfWeakRephasings) + "," else "") +
            (if (debug && bestPhasesQueue != null) "refrshBstPh:" + sharedAmongSingleSolverThreads.refreshedBestPhasesGlobal + "/" + bestPhasesQueue.size + "," else "") +
            //(if (debug && rescalingsAbsEliScores > 0) "#conflicts/#rescalingsAbsEliScores: " + noOfConflictsTotal / rescalingsAbsEliScores + ", " else "") +
            (if (debug && abandonOrSwitchSlowThreads != 0d) "thrdChgActs:" + threadChangeActions + "," else "") +
            (if (debug) "ngdRmvThrsh:" + nogoodRemovalThreshAdapted.toInt + "," else "") +
            //(if (debug) "getApproxNoOfLearnedNogoods: " + getApproxNoOfLearnedNogoods + ", " else "") +
            //  (if (debug) "noOfNogoodRemovalPhases: " + noOfNogoodRemovalPhases + ", " else "") +
            (if (debug) "rsclLitScrs:" + rescalingsAbsEliScores + "," else "") +
            (if (debug) "noisePhsMm:" + round(noisePhaseMemo, 6) + "," else "") +
            //(if (debug) "totalAbsEliScore: " + (totalAbsEliScoreForDebugging.toInt /*set only at rescaling!*/) + ", " else "") +
            // (if (debug) "Avg var score: " + (avgAbsEliScore - (avgAbsEliScore % 0.000000000000001)) + ", " else "") +
            (if (debug && noOfReducibleSpaceRequests > 0) "MemMisses:" + round(noOfReducibleSpaceRequestsMisses.toDouble / noOfReducibleSpaceRequests.toDouble, 3) + "," else "") +
            //(if (debug) "rsseEMA:" + round(reducibleSlotSizeEnlargementsEMA.toDouble, 3) + "," else "") +
            //(if (debug) "confls/trials:" + round(noOfConflictsTotal.toFloat / trials.toFloat,2) + "," else "") +
            //"linePrint: " + linePrint + "," +
            //  (if (debug && enforceLBDemaComputation) "lbdEmaFast: " + round(lbdEmaFast, 2) + ", " else "") +
            (if (debug && useLBDs) "lbdEmaSlow:" + round(lbdEmaSlow, 2) + "," else "") +
            //(if (debug) "Conflicts/trials:" + round(trialsPerConflicts, 2) + ", " else "") +
            //(if (debug && rndmBranchProbR < 0f) "rndmBranchProb:" + rndmBranchProb else "") +
            (if (true) "P/s:" + toKorM(avgNoPropagationsPerSecond) + "," else "") +
            "Tr:" + toKorM(trials)
            )

          printStatusLine(pStr)

          // ^ NB: remaining #unassigned literals < 1 at this point doesn't imply we are finished, since there may still be some unresolved conflict(s)

        }

      }

      var enforceImmediateFullRestart = reentry

      if(reentry) {

        if(debug)
          println("\nReusing solver data from previous model")

        modelOpt = null/*not: None*/

        violatedNogoodReducible = 0l

        noOfConflictsTotal = 0

        noOfConflictsAfterRestart = 0

        noOfConflictsAfterLastRephasing = 0

        noOfRestarts = 0

        uncertainEliSearchStart = 0

      }

      if(triviallyUNSAT) {

        unsat

        if (collectOffHeapGarbage)
          queueOffHeapGarbageInSingleSolver

        return None

      }

      while (modelOpt == null/*[sic]; None = UNSAT*/ && !stopSolverThreads) { // bounce-back loop; if program is tight or in sat-mode, there is only a single iteration

        var incompleteModuloConflict = true

        var trials = 0 // inner loop trials (for truth assignment search in an individual solver thread, not sampling trials)

        var maxApproachSwitches = maxApproachSwitchesPerSolverThread

        var assignmentBasedProgress: Boolean = false

        var assignmentBasedProgressGlobal: Boolean = false

        while (incompleteModuloConflict && !stopSolverThreads) { // inner loop of single model solver ----------------------------

          // After this loop, we have a single supported model (as a truth assignments to elis), or
          // model candidate (in the ASP case) which needs to be checked for stable-ness, or UNSAT

          trials += 1

          if(enforceImmediateFullRestart) {  // in case of reentry reusing the solver data structures from a previous sampled model

            enforceImmediateFullRestart = false

            restart(trials, jumpBackLevelFromConflict = -1, temporaryDisableReusedTrailRestarts = true)

          }

          if (absEliScoringApproach == 1 && playStackStartOrderNumber >= 0) { // see Liang et al: Exponential RecencyWeighted Average Branching Heuristic for SAT Solvers
            // Based on Exponential Recency Weighted Average (ERWA) (an approach to multi-armed bandits)

            val multiplier: Float = if (violatedNogoodReducible == 0l) 0.9f else 1f // we give extra rewards for triggering conflicts

            var i = orderNumber - 1

            while (i >= playStackStartOrderNumber) { // the absElis we are examining in this loop are exactly those which
              // have been assigned by the most recent setEliWithNogoodUpdatesNoHeap() call:

              val absEli = toAbsEli(rmiStoreG.get(i))

              //   println("rmiStoreG i = " + i + ", absEli = " + absEli)

              //assert(!isNotAbsSetInPass(absEli))

              val d = (getNoOfConflictsForERWA - getLastConflictOfAbsEli(absEli)) + 1

              if (d != 0) {

                val reward = multiplier / d.toFloat

                val newQValue = (1f - alpha) * getAbsEliScore(absEli) + alpha * reward

                setAndEnactScoreOfAbsEli(absEli, newQValue)

              }

              i -= 1

            }

            // println("----------------------------------------------")

          }

          if (violatedNogoodReducible != 0l) { // conflict...

            if(getNogoodSizeFromReducible(violatedNogoodReducible) <= 0) {  // if this happens, likely the space reserved for some reducible flew over

              stomp(-10000, "Invalid internal state (thread " + threadNo + "):\n  getNogoodSizeFromReducible(" + violatedNogoodReducible + ") = " + getNogoodSizeFromReducible(violatedNogoodReducible))

            }

            if (dl == 0) { // nowhere to go back

              // if (debug2)
              // println("\nUnsat; conflicting nogood: " + generateRefToNogoodInReducible(violatedNogoodReducible).toArray.mkString(","))

              unsat

              if (collectOffHeapGarbage)
                queueOffHeapGarbageInSingleSolver

              return None

            }

            noOfConflictsTotal += 1

            noOfConflictsAfterRestart += 1

            noOfConflictsAfterLastRephasing += 1

            if (scoringForRemovalOfLearnedNogoods == 1 || scoringForRemovalOfLearnedNogoods == 10 || scoringForRemovalOfLearnedNogoods == 11)
              nogoodActivityBump += nogoodActivityDecay // Minisat 2: nogoodActivityBump *= (1f / nogoodActivityDecay)

            uncertainEliSearchStart = 0

            incompleteModuloConflict = true

            //weaklyRephase

            val performRegularRestart = !localRestarts && decideDoRegularRestart

            /*if(!performRegularRestart && noViolNogoodsRecentBCP > 0) {

              //println("xxx")
              jumpBack((dl - 1).max(0), trials)

            } else*/ {

              if (noOfConflictsTotal % checkLearnedNogoodRemovalEveryNconflicts == 0 && (!removeLearnedNogoodAtRegularRestarts || performRegularRestart))
                possiblyRemoveLearnedNogoods(trials)

              //val restarted = possibleRestart(trials)

              if (true) { // conflict analysis and backtracking...
                // Observe that we decide whether or not to restart _after_ conflict analysis, because we can utilize
                // the backtracking level for reused trail restarts.

                {

                  // println("\ncurrent dec level (before conflict analysis): " + dl)

                  // The following estimation is very important - if the initial size of the new nogood is underestimated, we'll
                  // require a costly resizing later in conflictAnalysis. If it's overestimated, we waste space and harm
                  // cache locality. If in doubt, overestimate.
                  //val initialWorkingNogoodSizeInConflictAnalysis = 3 * avgSizeLearnedNogoods.max(getNogoodSizeFromReducible(violatedNogoodReducible))
                  val workingReducibleSizeInConflictAnalysisInNoOfInts = if (defaultNogoodAllocationSize == -1) {

                    val r = /*next2Pow*/ (workingReducibleSizeInConflictAnalysisAutoValueInNoOfInts.max(getNogoodSizeFromReducible(violatedNogoodReducible) + 20) /* -
                    offsetIntsOfNogoodInReducible - closingIntsAfterNogoodInReducible*/)

                    if (noOfConflictsTotal % 500 == 0) {

                      workingReducibleSizeInConflictAnalysisAutoValueInNoOfInts =
                        (workingReducibleSizeInConflictAnalysisAutoValueInNoOfInts - 5 +
                          (100 * reducibleSlotSizeEnlargementsEMA.toDouble).toInt).max(64).min(1024)
                      // ^while the reducibleSlotSizeEnlargementsEMA (exponential moving average over reducible slot enlargement event frequency) remains
                      // close to 0, workingReducibleSizeInConflictAnalysisAutoValue goes slowly down over time, creating larger slots in the beginning and refilling
                      // these slots later after nogoods have been deleted. But if the ema is signifiantly above 0, the slot size
                      // for new nogoods increases proportionally. NB: this heuristics has a significant influence on performance,
                      // as off-heap memory allocation is rather slow using many JDK's UNSAFE compared to C/C++-malloc.

                      //println("\nworkingReducibleSizeInConflictAnalysisAutoValue= " + workingReducibleSizeInConflictAnalysisAutoValue + ", initialWorkingNogoodSizeInConflictAnalysis = " + initialWorkingNogoodSizeInConflictAnalysis + ", getNogoodSizeFromReducible(violatedNogoodReducible): " + getNogoodSizeFromReducible(violatedNogoodReducible))

                    }

                    r

                  } else
                    defaultNogoodAllocationSize.max(getNogoodSizeFromReducible(violatedNogoodReducible) * 2)

                  val newNogoodReducibleInitial: NogoodReducible = reserveReducibleSpace(minimumRequiredReducibleSpaceSizeInNoOfInts = workingReducibleSizeInConflictAnalysisInNoOfInts)

                  conflictAnalysis(violatedNogoodReducible, newNogoodReducibleInitial)
                  /*
                                println("\n  want to jump back to: " + newLevel)

                                println("\n  sigmaEli = " + sigmaEli + ", neg(sigmaEli) = " + negateEli(sigmaEli))

                                println("\n  dec level of sigmaEli = " + decisionLevelOfEli(sigmaEli))

                                println("\n  is sigma not abs-assigned (before jumping back)? " + isNotAbsSetInPass(sigmaEli))
                  */

                  if (debug2) {

                    println("\n\n *********** From conflictAnalysis, conflictAnalysisResult_sigmaEli = " + conflictAnalysisResult_sigmaEli)

                    //println("From conflictAnalysis, new nogood = " + newNogood.toArray.mkString(","))

                  }

                  assert(decisionLevelOfEli(conflictAnalysisResult_sigmaEli) == dl)

                  if (absEliScoringApproach == 1 || absEliScoringApproach == 2) {

                    if (alpha > alphaTh)
                      alpha -= alphaStep

                  }

                  if (extReducibles == 1) { // TODO: why is this here but for the other extReducibles further below??

                    setupNewReducibleForExt1(conflictAnalysisResult_conflictNogoodReducible, beforeSolvingstarted = false)

                    possiblyAddLearnedNogoodToReducibleLists(trials, conflictAnalysisResult_conflictNogoodReducible)

                  }

                  //conflEmaSlow += (noOfConflictsTotal - conflEmaSlow) / (1 << 14).toDouble

                  //conflEmaFast += (noOfConflictsTotal - conflEmaFast) / (1 << 5).toDouble

                  //if(noOfConflictsTotal % 1000 == 0)
                  //println("\n" + conflEmaSlow, conflEmaFast)

                  if (!isClarkReducible(violatedNogoodReducible)) {

                    val lbd: Int = if (useLBDs/*useLBD*/) getLBDFromReducible /*computeLBD*/ (/*violatedNogoodReducible*/ conflictAnalysisResult_conflictNogoodReducible) else -1
                    // ^differently from glucose, we use lbd of violatedNogoodReducible, as we don't have the lbd of the conflictAnalysisResult_conflictNogoodReducible

                    //println("lbd for lbdEma = " + lbd)

                    if (useLBDs) { // exponential moving averages of the learnt clause LBD

                      // Biere, Fröhlich: Evaluating CDCL Restart Schemes @POS'15 (http://fmv.jku.at/biere/talks/Biere-POS15-talk.pdf):

                      lbdEmaSlow += (lbd - lbdEmaSlow) / (1 << 14).toDouble

                      lbdEmaFast += (lbd - lbdEmaFast) / (1 << 5).toDouble

                    }

                    if (absEliScoringApproach == 0 && !evsids /*&& adaptiveVSIDSFact != 1f*/ ) { // variant of adaptVSIDS (Liang et al)

                      if (lbdEmaFast / 1.2d > lbdEmaSlow) {

                        absEliScoreScaleBaseAdaptive = absEliScoreScaleBaseLow

                      } else {

                        absEliScoreScaleBaseAdaptive = absEliScoreScaleBaseHigh

                      }

                    }

                  }

                  val performLocalRestart = localRestarts && { // based on Ryvchin & Strichman 2008: Local Restarts in SAT

                    if(removeLearnedNogoodAtRegularRestarts)
                      stomp(-5009, "localRestarts cannot be combined with removeLearnedNogoodAtRegularRestarts")

                    val df = noOfConflictsTotal - getConflictsAtDecisionLevel(conflictAnalysisResult_newDecisionLevel)

                    df > noOfConflictsBeforeRestart * localRestartsTriggerThreshFactor

                  }

                  val restarted = if(performLocalRestart || performRegularRestart || forceRestart) {

                    if(forceRestart)
                      possiblyRemoveLearnedNogoods(trials, all = true) // TODO: necessary?

                    forceRestart = false

                    restart(trials, jumpBackLevelFromConflict = conflictAnalysisResult_newDecisionLevel)

                    true

                  } else
                    false

                  if (!restarted) {

                    if (debug2) {

                      println("BEFORE jumping back:")

                      var countUnset = 0

                      var kkkk = 0

                      while (kkkk < getNogoodSizeFromReducible(conflictAnalysisResult_conflictNogoodReducible)) {

                        println("   index " + kkkk + ", eli = " + getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkkk) + ", isSetInPass?: " + isSetInPass(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkkk)) /*+ ", absEliScore: " + getAbsEliScore(toAbsEli(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkk)))*/)

                        if (isNotSetInPass(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkkk)))
                          countUnset += 1

                        kkkk += 1

                      }

                    }

                    jumpBack(conflictAnalysisResult_newDecisionLevel, trials)

                    assert(isNotAbsSetInPass(conflictAnalysisResult_sigmaEli)) // sigmaEli had been assigned on the previous decision level, so must have
                    // been unassigned when jumping back given that newLevel < prevLevel

                  }

                  if (debug2) println("conflictAnalysisResult_sigmaEli = " + conflictAnalysisResult_sigmaEli + "")

                  if (debug2 && false) {

                    println("\nLearned nogood:")

                    var kkk = 0

                    while (kkk < getNogoodSizeFromReducible(conflictAnalysisResult_conflictNogoodReducible)) {

                      println("   index " + kkk + ", eli = " + getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkk) + ", isSetInPass?: " + isSetInPass(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkk)) /*+ ", absEliScore: " + getAbsEliScore(toAbsEli(getEliFromNogoodInReducible(conflictAnalysisResult_conflictNogoodReducible, kkk)))*/)

                      kkk += 1

                    }

                    println("-----------------")

                  }

                  val skipLearnedNogood/*skipping doesn't appear to be useful*/ = if (extReducibles == 2 || extReducibles == 4 || extReducibles == 3 || extReducibles == 5 || extReducibles == 0) {

                    //val ngScore = getLBDFromReducible(conflictAnalysisResult_conflictNogoodReducible) //getNogoodReducibleScore(conflictAnalysisResult_conflictNogoodReducible, scoringForRemovalOfLearnedNogoods = scoringForRemovalOfLearnedNogoods)

                    // println(ngScore)

                    if(true /*ngScore <= 10 /*1e-15d*/ */) {

                      if (extReducibles == 2)
                        setupNewReducibleForExt2(conflictAnalysisResult_conflictNogoodReducible)

                      possiblyAddLearnedNogoodToReducibleLists(trials, conflictAnalysisResult_conflictNogoodReducible) // TODO: why is this not at same location as possyiblyAdd for extReducibles=1?

                      false

                    } else {

                      if (freeOrReassignDeletedNogoodMemory)
                        makeNogoodSpaceAvailable(conflictAnalysisResult_conflictNogoodReducible)

                      true

                    }

                  } else
                    false

                  val (satFoundDuringRephasing, newDecisionLevel) = if (rephasePhaseMemo) {

                    val (satFoundDuringRephasing/*true can come from an SLS rephasing (e.g., WalkSAT)*/, newDecisionLevel/*currently not used*/) = possibleRephasing(trials)
                    assert(newDecisionLevel == -1)

                    if (satFoundDuringRephasing)
                      incompleteModuloConflict = false

                    (satFoundDuringRephasing, newDecisionLevel)

                  } else
                    (false, -1)

                  if(newDecisionLevel >= 0 && newDecisionLevel < dl) {  // currently inactive (see possibleRephasing())

                    println("\nJumping back from " + dl + " to " + newDecisionLevel + " after rephasing to best phase")

                    jumpBack(newDecisionLevel, trials)

                  } else if (!skipLearnedNogood && !restarted && !satFoundDuringRephasing &&
                    getNogoodSizeFromReducible(conflictAnalysisResult_conflictNogoodReducible) > 0) {

                    setEliWithNogoodUpdatesNoHeap(negateEli(conflictAnalysisResult_sigmaEli), conflictAnalysisResult_conflictNogoodReducible)

                  }

                  nogoodRemovalThreshAdjustConflictCount -= 1

                  if (nogoodRemovalThreshAdjustConflictCount <= 0) {
                    nogoodRemovalAdjustNoOfConflicts *= nogoodRemovalAdjustInc;
                    nogoodRemovalThreshAdjustConflictCount = nogoodRemovalAdjustNoOfConflicts.toInt;
                    nogoodRemovalThreshAdapted *= nogoodRemovalThreshRatio

                  }

                }

              }

            }

            //noViolNogoodsRecentBCP = 0 //:::

          } else { // no nogood is in conflict...

            incompleteModuloConflict = orderNumber != noOfPosElisPlus1

            if (incompleteModuloConflict) { // satisfiability still unknown

              if (noOfConflictsBeforeNextRephasing == 0) { // we need this here (in addition to the conflict-branch) to ensure Walksat etc are called if there are no conflicts but noOfConflictsBeforeNextRephasing=0

                val (satFoundDuringRephasing /*true can come from an SLS rephasing (e.g., WalkSAT)*/ , newDecisionLevel /*currently not used*/ ) = possibleRephasing(trials)
                assert(newDecisionLevel == -1)

                if (satFoundDuringRephasing)
                  incompleteModuloConflict = false

              }

              if(incompleteModuloConflict) {

                val freeEliW = /*if (rngLocal.nextFloat() < 0.1f) {  //:::  greedy lookahead step
/*
                val maxMin = false //rngLocal.nextBoolean()

                //countViolNgs = true

                var maxViol = if(maxMin) 0f else 999999999f

                var maxViolEli = 0

                var i = 0

                val maxChecks = 100

                while(i < maxChecks) {

                  var freeEliCand = 0

                  do {

                    freeEliCand = rngLocal.nextInt(noOfAllElis + 1) - noOfAbsElis

                  } while (isPosOrNegSetInPass(freeEliCand) || freeEliCand == 0)

                  setDecisionLevelTo(dl + 1) // the next eli needs to be set on the new decision level

                  val vngccc = setEliWithNogoodUpdatesNoHeap(freeEliCand, reason = 0l, countViolNgs = true)

                  //if(vngccc == 0)
                   // maxChecks = 0

                  val vngc =  /*getAbsEliScore(toAbsEli(freeEliCand)) / */ vngccc

                  if((!maxMin && vngc < maxViol || maxMin && vngc > maxViol) || i == 0 || maxChecks == 0) {

                    maxViol = vngc

                    maxViolEli = freeEliCand

                  }

                  jumpBack((dl - 1), trials)

                  violatedNogoodReducible = 0L

                  i += 1

                } */

                val decEli1 = findDecisionEli

                setDecisionLevelTo(dl + 1) // the next eli needs to be set on the new decision level

                val vngc1 = setEliWithNogoodUpdatesNoHeap(decEli1, reason = 0l, countViolNgs = true)

                jumpBack((dl - 1), trials)

                violatedNogoodReducible = 0L

                val decEli2 = negateEli(decEli1)

                val vngc2 = setEliWithNogoodUpdatesNoHeap(decEli2, reason = 0l, countViolNgs = true)

                jumpBack((dl - 1), trials)

                violatedNogoodReducible = 0L

                if(vngc1 > vngc2)
                  decEli1
                else
                  decEli2

              } else */ {

                  findDecisionEli // invokes branching heuristics (nondeterministic decision literal choice)
                  // or finds free parameter literal using differentiation

                }

                if (freeEliW != 0) {

                  if (debug2)
                    println("\nbranching eli = " + freeEliW + " (decision level " + dl + ", trial " + trials + ")")

                  //if (extraChecks) assert(isNotAbsSetInPass(freeEliW))

                  val assignedBeforeBranching = orderNumber

                  if (localRestarts)
                    updateConflictsAtDecisionLevel(dl + 1, noOfConflictsTotal)

                  setDecisionLevelTo(dl + 1) // the next eli needs to be set on the new decision level

                  if (reusedTrailRestarts) {

                    updateDecisionAbsEliSeqForRTR(dl, (freeEliW))

                  }

                  val countViolNgs = bestPhaseCriterion == 2

                  val violNogoodCount = setEliWithNogoodUpdatesNoHeap(freeEliW, reason = 0l, countViolNgs = countViolNgs)

                  if (countViolNgs) {

                    if (violNogoodCount >= 1)
                      violNogoodCountsPerLevel.update(dl, violNogoodCount)

                  }

                  val noOfPropagationsInBCP = orderNumber - assignedBeforeBranching

                  noOfPropagationsSinceLastProgressPrinted += noOfPropagationsInBCP

                  val performProgressCheck = trials > minimumTrialsBeforeFirstProgressCheck &&
                    (noOfAbsElis - orderNumber <= (minUnassignedThisThread >> 1) &&
                      trials - lastProgressCheckAtTrial > minNoTrialsBetweenTwoProgressChecks) || fastModByPow2(trials, enforceProgressChecksEveryTrials) == 0

                  //  println("progressThresh = " + progressThresh + ", noOfAbsElis - orderNo = " + (noOfAbsElis - orderNo) + ", minUnassignedThisThread = " + minUnassignedThisThread + ", minUnassignedThisThread - progressThresh = " + (minUnassignedThisThread - progressThresh) + ", noOfAbsElis - orderNo <= minUnassignedThisThread - progressThresh = " + (noOfAbsElis - orderNo <= minUnassignedThisThread - progressThresh))

                  if (performProgressCheck) {

                    noOfProgressChecks += 1 // (in this thread)

                    lastProgressCheckAtTrial = trials

                    /* println("Progress check; current time: " + System.currentTimeMillis() + ", maxSamplingTimeMs: " + maxSamplingTimeMs +

                        "\nSystem.currentTimeMillis() - maxSamplingTimeMs in sec: " + (System.currentTimeMillis() - maxSamplingTimeMs)/1000

                        )*/

                    if (System.currentTimeMillis() > maxSamplingTimeMs) {

                      unknown()

                      return null

                    }

                    if (noOfAbsElis - orderNumber <= minUnassignedThisThread) {

                      assignmentBasedProgress = true

                      minUnassignedThisThread = noOfAbsElis - orderNumber

                      if (minUnassignedThisThread < minUnassignedGlobal) {

                        assignmentBasedProgressGlobal = true

                        minUnassignedGlobal = minUnassignedThisThread

                        sharedAmongSingleSolverThreads.greedilyBestThread = threadNo

                      } else
                        assignmentBasedProgressGlobal = false

                    } else {

                      assignmentBasedProgress = false

                      assignmentBasedProgressGlobal = false

                    }

                    val progress = {

                      //(See in debug mode status line "refrshBstPh" to check how many "best phases" are getting enqueue)

                      enforceBestPhaseQueueEntry || (if (bestPhaseCriterion == 0) {

                        lbdEmaFast / 1.3d > lbdEmaSlow //lbdEmaFast / 1.2d > lbdEmaSlow

                        //conflEmaFast / 1.5 > conflEmaSlow

                        //println(conflEmaFast / conflEmaSlow)

                      } else if (bestPhaseCriterion == 1) {

                        globalBestPhaseMemo && assignmentBasedProgressGlobal || !globalBestPhaseMemo && assignmentBasedProgress

                      } else if (bestPhaseCriterion == 2) {

                        var violNogoodSum = 0

                        var i = 1

                        while (i <= dl) {

                          violNogoodSum += violNogoodCountsPerLevel.get(i)

                          i += 1

                        }

                        {

                          if (violMaxNogoodCountsPerLevel.get(dl) == -1 ||
                            Math.abs(violNogoodSum - violMaxNogoodCountsPerLevel.get(dl)) > violMaxNogoodCountsPerLevel.get(dl) * 2) {

                            violMaxNogoodCountsPerLevel.update(dl, violNogoodSum)

                            true

                          } else
                            false

                        }

                        /*

                            if(violNogoodCountsPerLevel.get(dl) > violMaxNogoodCountsPerLevel.get(dl)) {

                              violMaxNogoodCountsPerLevel.update(dl, violNogoodCountsPerLevel.get(dl))

                              true

                            } else
                              false
                            */

                      } else {

                        stomp(-5009, "Unknown bestPhaseCriterion value")

                        false

                      })

                    }

                    if (progress && bestPhasesQueue != null && noOfConflictsTotal > minNoConflictsBeforeFirstRephasing /*since this is very costly*/ ) {

                      sharedAmongSingleSolverThreads.refreshedBestPhasesGlobal += 1

                      val newBestPhases = new ByteArrayUnsafeS(noOfAbsElis + 1, initialValue = if (rngLocal.nextBoolean()) 0x01.toByte else 0x00.toByte /*0x02.toByte*/)

                      var absEli = 1

                      /*bestPhasesForAbsElis.synchronized*/
                      {

                        while (absEli <= noOfAbsElis) {

                          if (isPosOrNegSetInPass(absEli) /*&& decisionLevelOfEli(absEli) <= dl*/ ) {

                            newBestPhases.update(absEli, if (isSetInPass(absEli)) 0x01.toByte else 0x00.toByte)

                            //updateInPhasePreviousForAbsElis(absEli, if (isSetInPass(absEli)) 0x01.toByte else 0x00.toByte)

                          }

                          absEli += 1

                        }

                      }

                      bestPhasesQueue.synchronized {

                        bestPhasesQueue.enqueueFinite(newBestPhases, maxSize = bestPhasesQueueSize) // keeping >1 "best" states doesn't seem to improve things, but more tests required

                      }

                    }

                    preReportedMinUnassignedGlobal = minUnassignedGlobal

                    threadChangeCheckFreqState -= 1

                    if (abandonOrSwitchSlowThreads != 0 && threadChangeCheckFreqState == 0) { // TODO: ??remove all thread switch stuff:

                      threadChangeCheckFreqState = threadChangeCheckFreq

                      if (true) { // we sample and average progress

                        val norm = (if (threadmxBean.isCurrentThreadCpuTimeSupported) threadmxBean.getCurrentThreadCpuTime() / 10000000 else trials).toDouble

                        val normalizedProgress = ((/*lbdEmaSlow.toDouble*/ noOfConflictsTotal.toDouble * 10d * orderNumber.toDouble)) /
                          norm.toDouble

                        val n = trials.toDouble / (noOfAbsElis / Math.abs(abandonOrSwitchSlowThreads * 100)).toDouble

                        avgNormProgress = (normalizedProgress + n * avgNormProgress) / (n + 1) // cumulative moving average

                        //println("\n avgNormProgress = " + avgNormProgress)

                      }

                      lazy val remainingSolverThreads: collection.Set[Eli] = progressNormalizedPerThread.keySet

                      val threadShouldChange = maxCompetingSolverThreads > 1 && avgNormProgress > 0 && {

                        progressNormalizedPerThread.synchronized {

                          remainingSolverThreads.size >= 2 && {

                            val tt: Option[SolverThreadInfo] = progressNormalizedPerThread.get(threadNo)

                            val t: SolverThreadInfo = new SolverThreadInfo(tt.get.thread, avgNormProgress)

                            progressNormalizedPerThread.put(threadNo, t)

                            lazy val avgNormProgressAllThreads = remainingSolverThreads.map(progressNormalizedPerThread.get(_).get.progressNormalized).sum /
                              remainingSolverThreads.size.toDouble

                            //println("\nnormalized progress for thread " + threadNo + " = " + avgNormProgress + ", avg: " + avgNormProgressAllThreads)

                            avgNormProgressAllThreads > avgNormProgress * 1.1d

                          }

                        }

                      }

                      if (threadShouldChange) { // a (seemingly) "slow" thread (progress beyond average), so we take action:

                        threadChangeActions += 1

                        val identicalApproaches = false && (maxCompetingSolverThreads == 1 || threadConfs.map(conf => conf.freeEliSearchApproach).distinct.length == 1
                          /*^ deactivated; even if all approaches are the same, switching the "slowest" to a different approach can make sense. */)

                        if (slowThreadAction == 4) {

                          forceRestart = true

                        } else if (slowThreadAction != 3 || identicalApproaches) {

                          progressNormalizedPerThread.synchronized {

                            if (slowThreadAction == 0 && remainingSolverThreads.size >= 2) {

                              progressNormalizedPerThread.remove(threadNo)

                              if (verbose && showProgressStats) {

                                println("\n\n>> >> >> Abandoning solver thread $" + threadNo + " after " + trials + " trials")

                                if (debug) println("   Current #threads in JVM in total (including non-solver threads): " + (java.lang.Thread.activeCount))

                                return null

                              }

                            } else {

                              val newPriority: Eli = if (slowThreadAction == 2) (Thread.currentThread().getPriority + 1).min(Thread.MAX_PRIORITY) else (Thread.currentThread().getPriority() - 1).max(Thread.MIN_PRIORITY)

                              if (newPriority != Thread.currentThread().getPriority()) {

                                //if (verbose) println("\nChanging priority of thread $" + threadNo + " after " + trials + " trials\n from " + Thread.currentThread().getPriority() + " to " + newPriority)

                                Thread.currentThread().setPriority(newPriority)

                              } else {

                                //if (verbose) println("\n" + (if (slowThreadAction == 2) "Decreasing" else "Increasing") + " priorities of threads other than thread $" + threadNo + " after " + trials + " trials")

                                progressNormalizedPerThread.foreach(ti => {

                                  val thread = ti._2.thread

                                  if (slowThreadAction == 1)
                                    thread.setPriority((thread.getPriority + 1).min(Thread.MAX_PRIORITY))
                                  else
                                    thread.setPriority((thread.getPriority - 1).max(Thread.MIN_PRIORITY))

                                })

                              }

                            }

                          }

                        } else if (!identicalApproaches) { // TODO: remove?

                          stomp(-10000, "slowThreadAction 3 currently not available")

                          freeEliSearchApproachP.synchronized {

                            maxApproachSwitches -= 1

                            val newApproach = freeEliSearchApproachP.getAllAlternativeValues((freeEliSearchApproachP.getAllAlternativeValues.indexOf(freeEliSearchApproach) + 1) % freeEliSearchApproachP.getAllAlternativeValues.length)

                            if (verbose && showProgressStats)
                              println("\n>> >> >> Switching solver thread $" + threadNo + " to decision heuristics " + newApproach + "... (after " + trials + " trials)")

                            freeEliSearchApproach = newApproach

                            threadConfs(threadNo - 1).freeEliSearchApproach = newApproach

                            //setThreadParams()

                          }

                        }

                      }

                    }

                    printSingleLineProgress(trials, noOfRemovedNogoods = -1)

                  }

                  //}

                }

              }

            }

          }

        } // -------------------------------------------------------------------------------------------------------------

        stopSolverThreads.synchronized {

          if (!stopSolverThreads) {

            //stopSingleSolverThreads()  // we don't call this here as we couldn't bounce back an invalid answer set then

            if (debug) println("\n\nModel candidate found. SolverTimer: " + timerToElapsedMs(solverTimer) + " ms\nReporting thread: $" + threadNo + "\n")

            assert(orderNumber - 1 == noOfAllElis / 2)

            val modelCandidate: (Array[Eli], IntOpenHashSet) = { // we don't just return an array here but also a hash set, since we might use the result as a cache key

              @inline def retranslateMappedEli(oldEli: Eli): Eli = {

                if (!preProcesssVariableElimConfig._1 || !preProcesssVariableElimConfig._5)
                  oldEli
                else {

                  {

                    val translatedEli = if (isPosEli(oldEli)) {

                      absEliUndoChangeMap(oldEli)

                    } else {

                      negateEli(absEliUndoChangeMap(negateNegEli(oldEli)))

                    }

                    translatedEli

                  }

                }

              }

              if (preProcesssVariableElimConfig._1 && !satMode)
                stomp(-5009, "Preproc currently not available in ASP mode") // TODO: more tests required, then activate

              val assignmentAsHashSet = new IntOpenHashSet(noOfPosAtomElis) // can (initially) contain positive as well as negative literals (elis)

              var absElii: Eli = 1

              while (absElii <= noOfPosAtomElis /*i.e., this doesn't comprise blits*/ ) {

                if (isSetInPass(absElii)) {

                  assignmentAsHashSet.add(retranslateMappedEli(absElii))

                } else {

                  assignmentAsHashSet.add(negateEli(retranslateMappedEli(absElii)))

                }

                absElii += 1

              }

              val test = false

              var noOfRestoredOriginalPosAtoms = 0

              assert(!test || !preProcesssVariableElimConfig._5)

              removedNogoodsPerAtomOpt.foreach { removedNogoodsPerAtom: mutable.TreeMap[Eli /*atom*/ , mutable.HashSet[IntArrayUnsafeS]] => {
                // We've performed variable elimination (materially or non-materially - i.e. just ignoring "eliminated" variables) in class Preparation and need to restore
                // now the removed variables (atoms) with their correct polarities.
                // This must be done even if the "eliminated" variables (the removedNogoodsPerAtom keys) have not materially been
                // removed from symbols (preProcesss_variableOrNogoodElimConfig._5 = false).

                // TODO: optimize:

                val removedNogoodsPerAtomArray: Array[(Eli, mutable.HashSet[IntArrayUnsafeS])] = removedNogoodsPerAtom.toArray

                removedNogoodsPerAtomArray.foreach { case (removedPosAtom: Eli, _) => {

                  assert(isPosEli(removedPosAtom)) // (must also be an atom eli (no blit), however, the isPosAtomEli() check wouldn't
                  // always work here because of the translation if preProcesss_variableOrNogoodElimConfig._5=true)

                  if (test) {

                    clearInPass(removedPosAtom, calledWhen = 2)

                    clearInPass(negatePosEli(removedPosAtom), calledWhen = 2)

                  }

                  assignmentAsHashSet.remove(removedPosAtom)

                  assignmentAsHashSet.remove(negatePosEli(removedPosAtom))

                }
                }

                removedPosAtomsOrderedOpt.get.reverse.foreach { case removedPosAtom: Eli => {
                  // it's important that we restore the variables in reverse order (because the nogoods of variables removed earlier
                  // might contain variables removed later)

                  val removedNogoods: mutable.HashSet[IntArrayUnsafeS] = removedNogoodsPerAtom.get(removedPosAtom).get

                  if (test)
                    setInPassAfterSolvePhase(removedPosAtom)

                  assignmentAsHashSet.add(removedPosAtom)

                  // We check if the extended formula (i.e., restoredNogoods) is satisfied:

                  var noFulfilledNogoods = true

                  val rnit = removedNogoods.iterator

                  while (noFulfilledNogoods && rnit.hasNext) {

                    val nogood: IntArrayUnsafeS = rnit.next()

                    var nj = 0

                    do {

                      val eli = nogood.get(nj)

                      noFulfilledNogoods = !assignmentAsHashSet.contains(eli) // if yes, the nogood cannot be fulfilled, so,
                      // if this is also the case for all the other nogoods in restoredNogoods, we keep
                      // the assignment (assignmentHashSetForVarRestoration.add(removedPosAtom)) of the restored variable.

                      nj += 1

                    } while (!noFulfilledNogoods && nj < nogood.sizev)

                  }

                  if (!noFulfilledNogoods) { // we must revert the assignment of the restored variable to negative

                    if (test) {

                      clearInPass(removedPosAtom, calledWhen = 2)

                      setInPassAfterSolvePhase(negatePosEli(removedPosAtom))

                    }

                    assignmentAsHashSet.remove(removedPosAtom)

                    assignmentAsHashSet.add(negatePosEli(removedPosAtom))

                  }

                  noOfRestoredOriginalPosAtoms += 1

                  if (debug2) println(" Restored eliminated positive eli " + removedPosAtom)

                }
                }

              }

              }

              if (test) {

                val modelCand = new IntArrayList(noOfAbsElis)

                var mci: Eli = 1

                while (mci <= noOfPosAtomElis) { // the atom elis in the model candidate must be in increasing numerical order
                  // (as we use toAbsEli subset of toAbsEli bounced model directly as toAbsEli cache key)

                  if (isSetInPass(mci))
                    modelCand.add(mci)

                  mci += 1

                }

                val modelCandArray: Array[Eli] = modelCand.toIntArray

                println("modelCandArray (test):\n " + modelCandArray.sorted.mkString(" "))

                (modelCandArray, new IntOpenHashSet(modelCandArray))


              }

              val r = {

                assignmentAsHashSet.removeIf(isNegEli(_))

                val modelCandArray: Array[Eli] = assignmentAsHashSet.toIntArray // modelCand.toIntArray

                if (debug) println("modelCandArray:\n " + modelCandArray.sorted.mkString(" ") + "\nassignmentAsHashSet:\n" + assignmentAsHashSet.toIntArray.mkString(" "))

                (modelCandArray, assignmentAsHashSet)

              }

              if (debug) println("\nRestored eliminated variables: " + noOfRestoredOriginalPosAtoms)

              r

            }

            val checkResult: (Boolean, Array[Eli]) = if ((satMode || (assureProgIsTight && !performSanityChecks)))
              (true, Array[Eli]())
            else {

              assert(!preProcesssVariableElimConfig._1 || !preProcesssVariableElimConfig._5)

              if (debug) println("Checking if stable model...")

              val r = checkASPWithEliRules(modelCandidate, rulesOpt.get)

              if (!r._1) {

                if (debug) println("Answer set check fail. Remainder:\n" + r._2.mkString("\n"))

              } else if (debug) println("Answer set check OK")

              r

            }

            if (checkResult._1) {

              assert(checkResult._2.isEmpty)

              //stopSolverThreads = true
              stopSingleSolverThreads()

              def threadSanityChecks: Unit = { // we perform a few simple tests with the discovered model (which must already be established as a valid answer set in ASP mode at this point).
                // These tests are not correctness proofs, they are just for debugging purposes.

                // TODO: due to incomplete locking on stopSolverThreads, we occasionally end up here >= twice

                //stopSolverThreads = true  // we should not set this to true here as then later certain code contingent on false would be omitted

                println("\nPerforming informal in-thread sanity checks on resulting model candidate...")
                // (There is another sanity check called in object diffSAT (for sat mode only)

                if (!satMode) {

                  assert(!preProcesssVariableElimConfig._1 || !preProcesssVariableElimConfig._5)

                  val r = checkASPWithEliRules(modelCandidate, rulesOpt.get)

                  if (!r._1) {

                    println("Answer set check fail!") // indicates that tightness recognition gave wrong result, as otherwise the model would have
                    // been bounced back

                    sys.exit(-1)

                  } else
                    println("Answer set check OK")

                }

                val assignment /* In contrast to modelCandidate, this also includes blits (ASP-mode) and negative elis! */ =
                  ((-noOfAbsElis to -1) ++ (1 to noOfAbsElis)).filter(eli => {

                    isSetInPass(eli)

                  }).to(mutable.HashSet)

                val expectedAssignmentSize = noOfAllElis / 2

                println("#assignment = " + assignment.size)
                println("   should be: " + expectedAssignmentSize)

                val assignmentSizeCorrect = assignment.size == expectedAssignmentSize

                println("Assignment size correct?: " + assignmentSizeCorrect)

                if (!assignmentSizeCorrect)
                  sys.exit(-1)

                val (allElitsCovered, noInconsistencies) = {

                  var allCovered = true

                  var noInconsistencies = true

                  ((-noOfAbsElis to -1) ++ (1 to noOfAbsElis)).foreach { eli =>

                    val posIncl = assignment.contains(eli)

                    val negIncl = assignment.contains(negateEli(eli))

                    if (!posIncl && !negIncl)
                      allCovered = false

                    if (posIncl && negIncl) {

                      noInconsistencies = false

                      println("Inconsistency: both " + eli + " and " + negateEli(eli) + " (negateEli(_)) are set")

                    }

                  }

                  (allCovered, noInconsistencies)

                }

                println("All elis covered?: " + allElitsCovered)

                println("No inconsistencies?: " + noInconsistencies)

                var violatedNogoods = 0

                var checkedNg = 0

                //if(debug) println("Reentry: " + reentry)

                var nogi = 0

                while (nogi < nogiClarkToNogoodReducible.size) { // if preProcesss_variableOrNogoodElimConfig._5=true, we
                  // are using the translated nogoods here (i.e., as used during solving), and also the solver's assignment.

                  @inline def nogoodInReducibleToEliArrayBuffer(addr: NogoodReducible): ArrayBuffer[Eli] = {

                    val sb = new ArrayBuffer[Eli]()

                    val ngs = getNogoodSizeFromReducible(addr)

                    var i = 0

                    while (i < ngs) {

                      sb.append(getEliFromNogoodInReducible(addr, i))

                      i += 1

                    }

                    sb

                  }

                  val nogoodArrayBuffer = nogoodInReducibleToEliArrayBuffer(nogiClarkToNogoodReducible.get(nogi))

                  //println(" checked nogood: " + nogood.mkString(" "))

                  checkedNg += 1

                  assert(!nogoodArrayBuffer.isEmpty)

                  if (nogoodArrayBuffer.forall(assignment.contains(_))) {

                    violatedNogoods += 1

                    println("Violated nogood (internal error, please report): nogi: " + nogi + " = " + nogoodArrayBuffer.mkString(","))

                  }

                  nogi += 1

                }

                assert(checkedNg == nogiClarkToNogoodReducible.size)

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

                // NB: There is a further (and for satMode/DIMACS the most important) informal enforceSanityChecks check in diffSAT.scala

                if (!allElitsCovered || !noInconsistencies || violatedNogoods > 0) {

                  println("\n\\/\\/\\/\\/ Internal error: Initial sanity checks failed on model candidate!\n")

                  sys.exit(-5)

                }

              }

              //if(debug) println("pass:\n " + pass.mkString(","))

              if (performSanityChecks) {

                if (sampledModels.length <= 2 || sampledModels.length % 100 == 0)
                  threadSanityChecks

              }

              if (debug) {
                if (satMode) println("\nFound a satisfying assignment") else println("\nFound an answer set")
              }

              //println("  with symbols: " + modelCandidate.map(symbols(_)).mkString(" "))

              if (debug) println("  at solverTimer " + timerToElapsedMs(solverTimer) + " ms")

              modelOpt = Some(modelCandidate)

            } else { // Model candidate bounced back in ASP mode, so we need to retry with added loop nogoods (this
              // enhancement and re-bouncing possibly needs to be repeated several times)...

              if (debug) println("\\\\\\\\\\\\\\\\ \nNot an answer set: " + modelCandidate._1.mkString(",") + " (" + modelCandidate._2 + ")\n Remainder: " + checkResult._2.mkString(","))

              if (debug) println("Model cand with symbols: " + modelCandidate._1.map(predI => symbols(predI - 1)).mkString(" "))

              if (assureProgIsTight) // if the program is tight (i.e., we only need to look for so-called supported models), every model returned
              // by the SAT solver is an answer set
                stomp(-10000, "Answer set check of SAT model of presumably tight program failed")
              // ^if this happens the logic program is either actually not tight (there is a loop in the positive dependency graph)
              // or the model actually isn't a model (e.g., bug in Clark completion)

              // We add loop nogoods and try again (only for non-tight programs).

              // We use a modified variant of the ASSAT approach with CMODELS-style backjumping (instead of restarting the
              // SAT solver ("inner loop") from scratch);
              // ASSAT: see revised paper http://www.cs.ust.hk/~flin/papers/assat-aij-revised.pdf [ASSAT]
              // for the latter (not the earlier version of this paper).
              // Note that in contrast to ASSAT and CMODELS, we use CDNL instead of CDCL, e.g., conflict handling on loop nogood violations.

              /* Recall:

                "Loop" (in ASP): a non-empty, non-singletom set of atoms is a loop iff the subgraph of the positive dependency graph
                  induced by L is strongly connected.
                A singleton set {p} is a loop iff there is an arc from p to p in the positive dependency graph.

                 Subgraph G(S) "induced" by S is the graph whose node set is S and whose edge set consists of all edges
                 that have both endpoints in S.
              */

              val mMinusR = checkResult._2

              val loopsInMminus: mutable.Seq[ArrayBuffer[Eli]] = { // see Def 3 in [ASSAT]

                sccCache.getOrElseUpdate(mMinusR, {

                  val t = {

                    val tR = new Int2ObjectOpenHashMap[List[Eli]]()

                    val dgEntriesIterator = positiveDependencyGraph.keySet().iterator()

                    while (dgEntriesIterator.hasNext()) {

                      val key: Eli = dgEntriesIterator.nextInt()

                      if (mMinusR.contains(key))
                        tR.put(key, positiveDependencyGraph.get(key))

                    }

                    tR

                  }

                  val tKeys: IntSet = t.keySet()

                  val tKeysIterator = t.keySet().iterator()

                  val dependencyGraphInducedByMminus = new Int2ObjectOpenHashMap[List[Eli]]()

                  while (tKeysIterator.hasNext()) {

                    val key = tKeysIterator.nextInt()

                    dependencyGraphInducedByMminus.put(key, t.get(key).filter((eli: Eli) => {

                      tKeys.contains(new Integer(eli)) // TODO: ?works only with boxed int?

                    }))

                  }

                  val sccs: ArrayBuffer[ArrayBuffer[Eli]] = Tarjan.trajanRec(dependencyGraphInducedByMminus) // we identify strongly connected components

                  sccs

                })

              }

              val maximalLoopsInMminus =
                loopsInMminus.filter(candidateLoop => { // TODO: ? remove .filter(...) (which ensures that loop is maximal)? filter worth the hassle?
                  !loopsInMminus.exists(loop => loop.length > candidateLoop.length && candidateLoop.forall(loop.contains(_)))

                }
                )

              var noOfGenLoopNogoods = 0

              var i = 0

              val mll = maximalLoopsInMminus.length

              val jumpBackAfterFirstViolatedLoopNogood = false // TODO: test true
              assert(!jumpBackAfterFirstViolatedLoopNogood)

              while (i < mll && (violatedNogoodReducible == 0l || !jumpBackAfterFirstViolatedLoopNogood)) {

                val loop: mutable.Seq[Eli] = maximalLoopsInMminus(i)

                //println("Loop = " + loop.mkString(","))

                val externalBodiesOfLoopAtoms: Set[Eli] = /*blits of rule bodies where the head is in a loop but not any of the body literals*/
                  loop.flatMap((loopPosAtomEli: Eli) => {

                    val negBlits: Array[Eli] = posHeadAtomToNegBlits.get(loopPosAtomEli) //ruliformNogiToNegBlits.get(nogood)

                    // println("negBlits:  " + negBlits.mkString(","))

                    Option(negBlits)

                  }).flatten.filter(negBlit => {

                    //println("negBlit = " + negBlit)

                    val posBodyElis: Array[Eli] = negBlitToPosBodyElis.get(negBlit)

                    !loop.exists(posBodyElis.contains(_))

                  }).toSet

                //println("externalBodiesOfLoopAtoms = " + externalBodiesOfLoopAtoms.mkString(","))

                var j = 0

                val ll = loop.length

                while (j < ll && (violatedNogoodReducible == 0l /*<-TODO: check redundant by default as by default we don't verify added nogoods anymore*/ ||
                  !jumpBackAfterFirstViolatedLoopNogood)) {

                  // see Def. 2 in [ASSAT]

                  val eli: Eli = loop(j)

                  val newLoopNogood: Set[Eli] = externalBodiesOfLoopAtoms.+(eli)

                  assert(!newLoopNogood.contains(0 /* *** -1*/))

                  val newLoopNogoodUnsafe = new IntArrayUnsafeS(newLoopNogood.size) // TODO: allocate space directly, without creating an object wrapper

                  newLoopNogoodUnsafe.setFromIntArray(newLoopNogood.toArray)

                  if (debug) println("Adding loop nogood: " + newLoopNogoodUnsafe)

                  val newLoopNogoodReducible = generateNogoodReducibleFromNogoodClarkOrSpecial(
                    nogoodAddr = newLoopNogoodUnsafe.getAddr,
                    nogoodSize = newLoopNogoodUnsafe.sizev,
                    beforeSolvingStarted = false)

                  addLearnedNogoodReducibleToReducibleLists(newLoopNogoodReducible, 0l)

                  if (emitClauses)
                    loopNogoodsForEmitClauses.add(newLoopNogoodUnsafe)

                  noOfGenLoopNogoods += 1

                  j += 1

                }

                i += 1

              }

              if (debug) println("Restarting after addition of " + noOfGenLoopNogoods + " loop nogoods...\n")

              jumpBack(-1, trials)

            }

          }

        }

      }

      // ^^^^^ End of bounce back loop for generating a single answer set or SAT model

      emitClauses.synchronized {
        if (emitClauses && !stopSolverThreads && !emittedClauses) {

          emittedClauses = true

          println("\nClauses (from completion + lazily discovered loop formulas), thread $" + threadNo + ":\n")

          @inline def printClause(nogood: IntArrayUnsafeS): Unit = {

            var i = 0

            while (i < nogood.size) {

              val eli = nogood.get(i)

              val l = (if (isNegEli(eli)) negateNegEli(eli) + 1 else -(eli + 1)) + (if (i == nogood.size - 1) " 0" else " ")

              print(l)

              i += 1

            }

            println

          }

          println("p cnf " + noOfAbsElis + " " + (clarkNogoodsFinal.length + loopNogoodsForEmitClauses.size))

          clarkNogoodsFinal.foreach((nogood: IntArrayUnsafeS) => printClause(nogood))

          loopNogoodsForEmitClauses.forEach((nogood: IntArrayUnsafeS) => printClause(nogood))

          println

        }

      }

      if (showIntermediateTimers)
        println("$" + threadNo + ": solverTimer 3a: " + timerToElapsedMs(solverTimer) + " ms")

      if ( /*!reuseSolverData &&*/ collectOffHeapGarbage) // otherwise, we collect the model data garbage only after the outer sampling loop
        queueOffHeapGarbageInSingleSolver

      if (showIntermediateTimers)
        println("$" + threadNo + ": solverTimer 3e: " + timerToElapsedMs(solverTimer) + " ms")

      modelOpt

    }

    assert(dimacsClauseNogoodsOpt.isDefined || rulesOpt.isDefined)

    lazy val problemDescription = "#Symbols (variables): " + symbols.length +
      "\n#Literals (including rule body literals): " + noOfAllElis +
      "\n#Nogoods: " + clarkNogoodsFinal.length +
      "\n#Parameter atoms: " + parameterAtomsElis.length +
      "\n#Measured atoms: " + measuredAtomsElis.length

    if (verbose) {

      println("\n" + problemDescription)

      if (clarkNogoodsFinal.length <= 20) {

        println("Initial nogoods (with eli numbers):")

        clarkNogoodsFinal.foreach(ng => println(" " + ng.toArray.mkString(",")))

      }

      println

    }

    if (writeRuntimeStatsToFile) {

      stats.writeEntry(key = "problemDescription", value = problemDescription, solverThreadNo = 0)

    }

    sharedAmongSingleSolverThreads.nogoodReducibleExchangePool.clear()

    minUnassignedGlobal = noOfAllElis // not precise even for single solver thread. For statistics/debugging/informal progress report purposes only.

    if (debug) println("\nStarting new set of " + maxCompetingSolverThreads + " inner solver thread(s)...") // optimalSingleSolverConfOpt = " + optimalSingleSolverConfOpt)

    stopSolverThreads = false

    def writeSettingsToStatsFile(runThreadNos: scala.Seq[Nogi], threadInfos: => Map[Int, String]) = {
      //        prettyPrint(singleSolverConf, omit = List("dependencyGraph") )

      val generalInfoStr = "<span style=\"color:orange\">seedRngGlobal: " + seedRngGlobal + "</span><br>Java version: " + System.getProperty("java.runtime.version") +
        "<br>Max JVM memory: " + (Runtime.getRuntime.maxMemory / 1073741824l) + " GB" + ", available processors: " + Runtime.getRuntime.availableProcessors +
        "<br>Command line arguments: <pre>" + commandLineTakeNote + "</pre><p>"

      val infoHeader = runThreadNos.map(threadNo => "<a href=\"#threadSettings" + threadNo + "\">Jump to settings for thread $" + threadNo + "</a>\n").mkString("\n<br>") + "\n<br>"

      val infoThreadsStr = runThreadNos.map(threadNo => ("<pre><a name=\"threadSettings" + threadNo + "\"></a>\n" + threadInfos(threadNo) + "</pre>")).mkString("\n").replaceAllLiterally("\n", "<br>")

      // to include an anchor link use this scheme: <a href="#anchorName">here</a>  --->    <a name="anchorName"></a>

      val infoSharedSettingsStr = "<pre><a name=\"sharedDefs\"></a>\n" +
        getSharedFieldsUsingReflection().map(nv => nv._1 + " = " + nv._2).mkString("<br>") + "\n</pre>"

      val infoSharedSettingsHeader = "<a href=\"#sharedDefs\">Jump to shared settings</a>\n"

      input.diffSAT.stats.writeEntry(key = "settings", value =
        generalInfoStr + infoHeader + infoSharedSettingsHeader + infoThreadsStr + infoSharedSettingsStr,
        solverThreadNo = 0)

      stats.writeEntry(key = "noOfThreads", value = runThreadNos.length, solverThreadNo = 0)

    }

    var newReentrySolverDataOpt: Option[SingleSolverThreadData] = None

    val modelFromCompetitiveSolverRunsOpt: Option[(Array[Eli], IntOpenHashSet)] = {

      if (reentrySingleSolverThreadDataOpt.isDefined && maxCompetingSolverThreads > 1) // the reused data from the previous model
      // cannot be shared among multiple threads (TODO: albeit we might reuse it for one of the threads?)
        stomp(-5009, "reuseSolverData=true cannot be combined with switchToBestConfigAfterFirstModel=" + switchToBestConfigAfterFirstModel)

      uncertainAtomsUpdateExecutorService.purge()

      @volatile var firstModelOpt = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

      val paramCombsSeq: Seq[SolverThreadSpecificSettings] = {

        if (optimalSingleSolverConfOpt.isDefined) { // (note: by default, if optimalSingleSolverConfOpt.isDefined we use only a single solver thread)

          (1 to maxCompetingSolverThreads).map(_ => optimalSingleSolverConfOpt.get)

        } else {

          (1 to maxCompetingSolverThreads).map(threadNo => {

            SolverThreadSpecificSettings(threadNo = threadNo,
              positiveDependencyGraph = positiveDependencyGraph,
              assureProgIsTight = progIsTight,
              freeEliSearchApproachP.getThreadOrDefaultValue(threadNo),
              restartTriggerConfR = (restartTriggerConfP._1.getThreadOrDefaultValue(threadNo),
                restartTriggerConfP._2(restartTriggerConfP._1.getThreadOrDefaultValue(threadNo)),
                restartTriggerConfP._3(restartTriggerConfP._1.getThreadOrDefaultValue(threadNo))),
              traverseReduciblesUpwardsInUnitProp = traverseReduciblesUpwardsInUnitPropP.getThreadOrDefaultValue(threadNo),
              initAbsElisArrangement = initAbsElisArrangementP.getThreadOrDefaultValue(threadNo),
              prep = prep /*<-for debugging/crosschecks only*/ ,
              seed = {

                val seedR = seedP.getThreadOrDefaultValue(threadNo)

                if (seedR == -1l) (if (threadNo - 1 < threadPRNGSeedPool.length) threadPRNGSeedPool(threadNo - 1) else rngGlobal.nextLong()) else seedR

              },
              restartFrequencyModifierFactorR = restartFrequencyModifierFactorP.getThreadOrDefaultValue(threadNo),
              useSLSinPhaseMemoRephasingR = useSLSinPhaseMemoRephasingP.getThreadOrDefaultValue(threadNo),
              nogoodRemovalThreshRatio = nogoodRemovalThreshRatioP.getThreadOrDefaultValue(threadNo),
              absEliScoringApproach = absEliScoringApproachP.getThreadOrDefaultValue(threadNo),
              nogoodRemovalThreshInit = nogoodRemovalThreshInitP.getThreadOrDefaultValue(threadNo),
              noisePhaseMemoR = noisePhaseMemoP.getThreadOrDefaultValue(threadNo),
              localRestarts = localRestartsP.getThreadOrDefaultValue(threadNo),
              scoringForRemovalOfLearnedNogoodsR = scoringForRemovalOfLearnedNogoodsP.getThreadOrDefaultValue(threadNo),
              weakRephasingAtRestartEvery = weakRephasingAtRestartEveryP.getThreadOrDefaultValue(threadNo),
              rephasePhaseMemo = rephasePhaseMemoP.getThreadOrDefaultValue(threadNo),
              nogoodBCPtraversalDirection = nogoodBCPtraversalDirectionP.getThreadOrDefaultValue(threadNo),
              singleSolverThreadDataOpt = None,
              absEliScoringApproach15NoOfBins = absEliScoringApproach15NoOfBinsP.getThreadOrDefaultValue(threadNo)
            )

          })

        }

      }

      var paramCombs: Array[SolverThreadSpecificSettings] = {

        val cbsArray = (if (maxCompetingSolverThreads < paramCombsSeq.length) paramCombsSeq.distinct else paramCombsSeq).toArray

        //shuffleArray(cbsArray, rngGlobal)  // cannot be used anymore!

        cbsArray

      }

      if (paramCombs.length > maxCompetingSolverThreads)
        stomp(-5015, "from " + paramCombs.length + " different configurations. Specified number of solver threads = " + maxCompetingSolverThreads)

      if (paramCombs.length < maxCompetingSolverThreads) // we must ensure that memory-wise at least maxCompetingSolverThreads different copies are in paramCombs,
      // to avoid overwriting of values when we later patch individual configurations with different field values.
        paramCombs = Array.tabulate(maxCompetingSolverThreads)(i => paramCombs((i) % paramCombs.length).copy())

      (1 to maxCompetingSolverThreads).foreach(threadNo => {

        val singleSolverConf: SolverThreadSpecificSettings = paramCombs((threadNo - 1) % maxCompetingSolverThreads) //.min(paramCombs.length))

        singleSolverConf.threadNo = threadNo

        threadConfs(threadNo - 1) = singleSolverConf

      })

      val runThreadNos = if (threadSelect.isEmpty) (1 to maxCompetingSolverThreads).toSeq else {

        println("Selected subset of threads (all other thread$ omitted): " + threadSelect)

        if (threadSelect.exists(_ > maxCompetingSolverThreads))
          stomp(-5009, "Invalid value for threadSelect: element(s) exceed number of threads specified (" + maxCompetingSolverThreads + ")")

        (1 to maxCompetingSolverThreads).toSeq.filter(threadSelect.contains(_))

      }

      /*lazy*/ val threadInfos: Map[Int, String] = runThreadNos.map(threadNo => (threadNo, prettyPrint(threadConfs(threadNo - 1), omit = List("dependencyGraph")))).toMap

      if (writeRuntimeStatsToFile)
        writeSettingsToStatsFile(runThreadNos, threadInfos)

      sharedAmongSingleSolverThreads.threadConfsOpt = Some(threadConfs)

      val callables: Seq[Runnable] = runThreadNos.map(threadNo => new Runnable {

        override def run(): Unit = {

          val singleSolverConf = threadConfs(threadNo - 1)

          if (verbose)
            println("Starting solver thread $" + singleSolverConf.threadNo + ":\n" + threadInfos(threadNo) + "\n")

          val singleSolverThreadData: SingleSolverThreadData = reentrySingleSolverThreadDataOpt.getOrElse(new SingleSolverThreadData(prep = prep, singleSolverConf, tempFacts = Nil, maxCompetingSolverThreads = maxCompetingSolverThreads, sharedAmongSingleSolverThreads = sharedAmongSingleSolverThreads))

          val reentry = reentrySingleSolverThreadDataOpt.isDefined

          singleSolverConf.singleSolverThreadDataOpt = Some(singleSolverThreadData) // just another reference to singleSolverThreadData so that we can assign it via threadConfs too

          val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(singleSolverConf,
            maxSamplingTimeMs = maxSamplingTimeMs,
            collectOffHeapGarbage = collectOffHeapGarbage,
            singleSolverThreadData = singleSolverThreadData,
            reentry = reentry)

          if (modelOpt != null) {

            stopSolverThreads.synchronized {

              /*if (true || !stopSolverThreads)*/ {

                //if (verbose)
                println("\nSuccessful portfolio thread: $" + singleSolverConf.threadNo)

                //if(fileNameOpt.get.contains("uuf250-090"))
                // println

                if (writeRuntimeStatsToFile)
                  stats.writeEntry(key = "successfulThread", value = singleSolverConf.threadNo, solverThreadNo = 0)

                newReentrySolverDataOpt = Some(singleSolverThreadData)

                if (sampledModels.size == 0 /*<- if > 0, we would switch after the nth model this way, to minimize influence from JVM hotspot compilation */ &&
                  switchToBestConfigAfterFirstModel > 0) { // we switch to a singleton portfolio, but we could theoretically also switch to some other subset:

                  optimalSingleSolverConfOpt = Some(singleSolverConf)

                  if (verbose)
                    println("\nFor sampling any further models, switching to single configuration\n" + prettyPrint(singleSolverConf, omit = List("dependencyGraph")) + "\n")

                  if (switchToBestConfigAfterFirstModel == 2)
                    maxCompetingSolverThreads = 1

                }

                //stopSolverThreads = true   // too late; would for very small problems allow other threads to continue
                // past sanity checks.

              }

            }

            firstModelOpt = modelOpt

          }

          if (debug) println("End of thread $" + threadNo)

        }

      })

      val solverThreads = ArrayBuffer[Thread]()

      solverThreads.append(Thread.currentThread)

      for (threadNo <- 2 to callables.size) {

        val t = new Thread(callables(threadNo - 1))

        t.setDaemon(false)

        solverThreads.append(t)

        t.start()

      }

      callables(1 - 1).run()

      solverThreads.drop(1).foreach(_.join())

      firstModelOpt

    }

    if (debug) println("sampleSingleRacing complete: r = " + modelFromCompetitiveSolverRunsOpt)

    if (modelFromCompetitiveSolverRunsOpt == null)
      (None /*this means that the caller of this method cannot distinguish UNKNOWN from UNSAT*/ , newReentrySolverDataOpt)
    else
      (modelFromCompetitiveSolverRunsOpt, newReentrySolverDataOpt)

  }

}
