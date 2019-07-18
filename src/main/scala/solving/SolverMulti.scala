/**
  * delSAT
  *
  * Copyright (c) 2018,2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package solving

import java.lang.management.ManagementFactory
import java.util
import java.util.concurrent._
import java.util.{Map, Optional}

import aspIOutils._
import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, Variable}
import commandlineDelSAT.delSAT._
import it.unimi.dsi.fastutil.ints._
import it.unimi.dsi.fastutil.objects.ObjectArrayList
import sharedDefs.{allowNumFiniteDiff, _}
import sun.misc.Contended
import utils._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * Main multimodel solver and propositional model sampling class.
  *
  * TODO: more detailed API documentation
  *
  * @author Matthias Nickles
  *
  */
class SolverMulti(prep: Preparation) {

  import prep._

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

  val uncertainAtomsUpdateExecutorService = new ThreadPoolExecutor(2, 2, 3, TimeUnit.SECONDS, new LinkedBlockingQueue[Runnable])

  var maxCompetingSolverThreads = (if (maxSolverThreadsR < 0) (if (noOfPosElis < -maxSolverThreadsR)
    1
  else
    Math.ceil(Runtime.getRuntime().availableProcessors() / (if (abandonOrSwitchSlowThreads > 0) 1.4d else 1.4d))).toInt else maxSolverThreadsR).max(1)

  var maxBurstRR = Math.abs(maxBurstR)

  @Contended var dynamicallyAdaptMaxBurst = maxBurstR < 0

  @Contended var noOfConflictsTotalAllThreads = 0 // approximate number - not entirely current

  @inline def updateAtomsFreqs(mOpt: Option[IntOpenHashSet],
                               measuredAtomElis: Array[Eli],
                               sampledModels /*after adding new model mOpt*/ : ArrayBuffer[(Array[Eli], IntOpenHashSet)],
                               fromScratch: Boolean = false): Unit = {

    val newModelsCount: Double = sampledModels.length.toDouble

    if (fromScratch) {

      var i = 0

      val il = measuredAtomElis.length

      while (i < il) {

        val measuredAtomEli: Eli = measuredAtomElis(i)

        val measureAtomVar: Variable[DoubleReal] = eliToVariableInCostFunctions(measuredAtomEli)

        measureAtomVar.set(new DoubleReal(sampledModels.count(_._2.contains(measuredAtomEli)).toDouble / newModelsCount))

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

  case class SampleMultiConf(
    requestedNoOfModelsBelowThresholdOrAuto: Int,
    noOfSecondaryModels: Int,
    prep: Preparation,
    requestedNumberOfModels: Int /*-1: stopSolverThreads at minimum number of models required to reach threshold*/ ,
    threshold: Double,
    maxIt: Int);

  @Contended val localSingleSamplerThreadPool = if (localSolverParallelThresh == localSolverParallelThreshMax) null.asInstanceOf[ThreadPoolExecutor] else
    new ThreadPoolExecutor(3, 3, 5, TimeUnit.SECONDS,
      new LinkedBlockingQueue[Runnable]) // used for various local (within toAbsEli solver thread) multithreading

  @Contended val sampledModels = ArrayBuffer[(Array[Eli], IntOpenHashSet)]()

  val passPreviousGlobal: ByteArrayUnsafeS = if (globalPassCache)
    new ByteArrayUnsafeS(noOfPosElis, 0x00.toByte /*<- sensitive value*/ , true) // 0x01.toByte could be used to indicate "don't know", but doesn't seem to have a positive effect
  // NB: we deliberately access this ^ array in a thread unsafe way
  else
    null.asInstanceOf[ByteArrayUnsafeS]


  /**
    * Samples multiple models (answer sets or SAT models) until the total cost function falls below the specified threshold (or the maximum number of trials has been reached).
    *
    * @param sampleMultiConf
    * @return (sequence of sampled symbolic models, sequence of pairs (model as array of elis, model as eli hash set))
    */
  def sampleMulti(sampleMultiConf: SampleMultiConf): (mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)]) = {

    import sampleMultiConf._

    def printMeasuredEliFreqs = {

      var i = 0

      val il = measuredAtomsElis.length

      while (i < il) {

        val measuredAtomEli: Eli = measuredAtomsElis(i)

        println("   f(" + symbols(measuredAtomEli) + ") = " + new DoubleReal(sampledModels.count(_._2.contains(measuredAtomEli)).toDouble / sampledModels.length.toDouble))

        i += 1

      }

    }

    var totalCost: Double = Double.MaxValue

    var it = 1

    val samplingTimer = System.nanoTime()

    val stagnationTol = threshold / stagnationTolDiv

    var oldTotalCost = Double.MaxValue

    var costDifForStagn = Double.MaxValue

    val showNumDiffProgress = debug

    var minCostSf = Double.MaxValue

    if (enforceStopWhenSampleSizeReached)
      stomp(-5012)

    @inline def samplingStopCriterion(it: Int, totalCost: Double, costDifForStagn: Double): Boolean = (it < maxIt &&
      (requestedNumberOfModels <= -1 && (totalCost.isNaN || totalCost > threshold) ||
        requestedNumberOfModels >= 0 && (sampledModels.length < requestedNumberOfModels || (totalCost.isNaN || totalCost > threshold) && !enforceStopWhenSampleSizeReached)) &&
      !(stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost < Double.MaxValue &&
        (requestedNumberOfModels <= -1 || sampledModels.length >= requestedNumberOfModels)))

    if (allowNumFiniteDiff) { // we use auto/sym diff (where available for a parameter atom) and/or finite differences (sort of discrete numerical differentiation) to approximate the partial
      // derivatives. The latter is mainly useful if automatic differentiation (i.e., nablaInner) cannot be used, i.e., for parameter atoms which
      // aren't measured atoms (i.e., don't appear in the cost function term), as it is the case for weight learning and Inductive Logic Programming.

      do {

        val noOfModelsBeforeProbes = sampledModels.length

        val useRandomDiffQuot = rngGlobal.nextDouble() < numFinDiffShuffleProb

        val diffQuotsPerParameter: Predef.Map[Eli, Double] = parameterLiteralElisArray.take(parameterLiteralElisArray.length / 2 /*<- i.e., positive literals only*/).map {
          case probingParamAtomEli: Eli => {

            if (useRandomDiffQuot) {

              if (showNumDiffProgress) println(" Random diffquot step in allowNumFiniteDiff")

              (probingParamAtomEli, rngGlobal.nextDouble())

            } else {

              val diffQuotPerAutoDiff = deficitByDeriv(probingParamAtomEli) // we try to get an analytical (automatic differentiation) diff result first

              if (!diffQuotPerAutoDiff.isNaN || ignoreParamIfNotMeasured)
                (probingParamAtomEli, diffQuotPerAutoDiff)
              else {

                if (showNumDiffProgress) println(" Probing for parameter (hypothesis) atom " + symbols(probingParamAtomEli) + "...")

                if (showNumDiffProgress) println("  Probing for +" + symbols(probingParamAtomEli) + "...")

                val rnOrderParamEli: Predef.Map[Integer, Double] = deficitOrderedUncertainLiteralsForJava.map(p => (p, {

                  //deficitByDeriv(p)

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

                val newModelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing(tempFacts = Nil)

                if (newModelOpt.isEmpty)
                  return (mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)]())

                sampledModels.append(newModelOpt.get)

                val costWithProbePlusH = updateMeasuredAtomsFreqsAndComputeCost(None,
                  measuredAtomElis = measuredAtomsElis,
                  sampledModels,
                  costFctsInner = costFctsInner,
                  fromScratch = true,
                  computeCosts = true // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
                ).get._1

                sampledModels.remove(noOfModelsBeforeProbes, sampledModels.length - noOfModelsBeforeProbes)

                if (showNumDiffProgress) println("  Probing for -" + symbols(probingParamAtomEli) + "...")

                java.util.Arrays.parallelSort(deficitOrderedUncertainLiteralsForJava, Ordering.by[Integer, Double]((parameterLiteralEli: Integer) => {
                  // we push the probing atom to the top or bottom of the branching literals priority ranking

                  if (parameterLiteralEli == probingParamAtomEli)
                    rnOrderParamEliMax
                  else if (parameterLiteralEli == negateEli(probingParamAtomEli))
                    rnOrderParamEliMin
                  else
                    rnOrderParamEli(parameterLiteralEli)

                }))

                val newModelOptMinusH: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing(tempFacts = Nil)

                if (newModelOptMinusH.isEmpty)
                  return (mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)]())

                sampledModels.append(newModelOptMinusH.get)

                val costWithProbeMinusH = updateMeasuredAtomsFreqsAndComputeCost(None,
                  measuredAtomElis = measuredAtomsElis,
                  sampledModels,
                  costFctsInner = costFctsInner,
                  fromScratch = true,
                  computeCosts = true // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
                ).get._1

                sampledModels.remove(noOfModelsBeforeProbes, sampledModels.length - noOfModelsBeforeProbes)

                val diffQuot = (costWithProbePlusH - costWithProbeMinusH) // * noOfModelsBeforeProbes.toDouble
                // NB: negative diffQuote increases(!) the likeliness that the respective parameter atom will be included in the next model.
                // NB: since in the solver we only need to compare these "quotients", division by 2h is redundant.

                if (showNumDiffProgress) println(" ==> diffQuot for param atom " + symbols(probingParamAtomEli) + " = " + diffQuot)

                (probingParamAtomEli, diffQuot)

              }

            }

          }
        }.toMap

        val ordering = if (diversifyLight || diversify) {

          //shuffleArray(deficitOrderedUncertainLiteralsForJava, rg = rngGlobalRG)  // not useful here, doesn't reliably achieve shuffling of elements with equal diffQuots due to IEEE arithmetics (e.g., -0 vs. 0)

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

        val newModelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing()

        if (newModelOpt.isEmpty)
          return (mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)]())

        sampledModels.append(newModelOpt.get)

        totalCost = if (ignoreParamVariablesR) Double.NegativeInfinity else updateMeasuredAtomsFreqsAndComputeCost(Some(newModelOpt.get._2),
          measuredAtomElis = measuredAtomsElis,
          sampledModels,
          costFctsInner = costFctsInner,
          fromScratch = true,
          computeCosts = true // TODO: computing the costs (for convergence check and deficitOrderedUncertainAtoms) is costly, so we don't do this every time
        ).get._1

        costDifForStagn = Math.abs(oldTotalCost - totalCost)

        oldTotalCost = totalCost

        minCostSf = minCostSf.min(totalCost)

        //println("minCostSf = " + minCostSf)

        if (resetsNumericalOuterLoopOnStagnation > 0 && costDifForStagn < stagnationTol && totalCost > threshold) {

          if (showNumDiffProgress) println("\n RESETTING (costDifForStagn = " + costDifForStagn + ")\n\n")

          sampledModels.clear()

          oldTotalCost = Double.MaxValue

          totalCost = oldTotalCost

          resetsNumericalOuterLoopOnStagnation -= 1

        }

        if (showProgressStats) {

          if (showNumDiffProgress) println("\nOuter-outer sampling iteration (with allowNumFiniteDiff = true, mixedScenario = " + (if (mixedScenario) "true" else "false") + ") " + it + " (of max " + maxIt + ") complete. " +
            "Current total cost: " + totalCost + " (threshold: " + threshold + "). #models: " + sampledModels.length + "\n")

        }

        it += 1

      } while (samplingStopCriterion(it = it, totalCost = totalCost, costDifForStagn = costDifForStagn))

      if (stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost > threshold)
        stomp(-5011)

      if (debug)
        println("minCostSf = " + minCostSf)

    } else do { // the (mostly deprecated) simpler outer-outer sampling loop for purely _deductive_ probabilistic inference (measured atoms = parameter atoms) and plain SAT/ASP solving

      if (!ignoreParamVariablesR) {

        if (diversify) {

          //shuffleArray(deficitOrderedUncertainLiteralsForJava, rg = rngGlobalRG)  // not useful here, doesn't reliably achieve shuffling of elements with equal diffQuots due to IEEE arithmetics (e.g., -0 vs. 0)

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

      val newModelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingleRacing()

      if (newModelOpt.isEmpty)
        return (mutable.Seq[Array[Pred]](), ArrayBuffer[(Array[Eli], IntOpenHashSet)]())

      sampledModels.append(newModelOpt.get)

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
        println("\nOuter-outer sampling iteration " + it + " (of max " + maxIt + ") complete. " +
          "Current total cost: " + totalCost + " (threshold: " + threshold + ")")

      it += 1

    } while (samplingStopCriterion(it = it, totalCost = totalCost, costDifForStagn = costDifForStagn))

    if (stopSamplingOnStagnation && costDifForStagn < stagnationTol && totalCost > threshold)
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

      val showFreqsOf = symbols.sorted.filterNot(_.contains("aux")).map(symbolToEli(_))

      showFreqsOf.foreach(atomEli => {

        val freqInModels = sampledModels.count(_._1.contains(atomEli)).toDouble / sampledModels.length.toDouble

        println("Pr(" + symbols(atomEli) + ") =(approx.) " + freqInModels)

      })

    }

    if (totalCost <= threshold)
      println("\nSampling complete; specified threshold reached; cost reached: " + totalCost + "\n" + sampledModels.length + " model(s) sampled (with replacement)\n")
    else
      stomp(-5008, "\nCost reached: " + totalCost)

    println("Time for multi-model sampling: " + timerToElapsedMs(samplingTimer) + " ms\n")

    updateAtomsFreqs(None,
      measuredAtomsElis,
      sampledModels,
      fromScratch = true)

    val sampledModelsWithEvalResolved: ArrayBuffer[(Array[Eli], IntOpenHashSet)] = sampledModels.map { case (modelElis, _) => {

      val modelElisEvalResolved: Array[Eli] = modelElis.map((posEli: Eli) => {

        val sym = symbols(posEli) // e.g., _eval_("f(pn1(a))*2","?",1)  Note that after "?" there can be any number of user-specified extra arguments

        if (sym.startsWith(evalFactPrefix + "(") && sym.contains("\"?\"") /*<- important as there might be resolved _eval_ atoms also (i.e., without "?")*/ ) {

          val (term, extraArgs) = aspIOutils.splitEvalSymbol(sym)

          val evalFunOpt: Option[DifferentialFunction[DoubleReal]] = sampleMultiConf.prep.costsOpt.flatMap(_.evalExpressionToFct.get(term))

          if (evalFunOpt.isEmpty)
            stomp(-209, term)

          val resolvedEvalAtomSym = "_eval_(\"" + term + "\"," + (evalFunOpt.get.getReal * probabilisticFactProbDivider).toInt + extraArgs

          symbols = symbols.:+(resolvedEvalAtomSym) // hmmpff

          symbols.length - 1

        } else
          posEli

      })

      (modelElisEvalResolved, new IntOpenHashSet(modelElisEvalResolved))

    }

    }

    val sampledModelsSymbolic = sampledModelsWithEvalResolved.map(model => model._1.map(eli => symbols(eli)))
    // ^ NB: these are not yet the printed symbolic models; observe that in SAT mode, (classically-)negative literals (e.g., "-5") are
    // at this point atoms which don't occur in the model, whereas in ASP mode, classical negation is expressed using
    // prefix "-" which is part of the symbol itself. Default negation (which doesn't exist in SAT mode) is represented in ASP mode by
    // absence of the negative literals in the model.

    log("sampledModelsSymbolic:\n" + sampledModelsSymbolic.map(_.mkString(" ")).mkString("\n"))

    (sampledModelsSymbolic, sampledModelsWithEvalResolved)

  }

  @Contended var nogoodExchangePool = new java.util.concurrent.ConcurrentHashMap[IntArrayUnsafeS, Int /*producing thread*/ ]()

  /*@volatile*/ var prevUnassi = Int.MaxValue // not precise; for statistics/debugging only

  val threadConfs = Array.ofDim[SingleSolverConf](maxCompetingSolverThreads)

  case class SingleSolverConf(threadNo: Int /*>=1*/ ,
                              dependencyGraph: Int2ObjectOpenHashMap[List[Eli]],
                              progIsTight: Boolean,
                              var freeEliSearchApproach: Int,
                              restartTriggerConfR: (Int, Int, Double),
                              noHeapR: Int,
                              absEliScoreFact: Float,
                              rndmIgnLearnedNogoodThresholdR: Float,
                              prep: Preparation /*<-for debugging/crosschecks only*/ ,
                              arrangeEliPoolR: Int,
                              seed: Long,
                              rndmBranchR: Double)

  /** Samples a single model (answer set in case of ASP mode) using optionally multiple parallel solver threads which
    * compete against each other in discovering a model.
    * The model generated by this function consists of elis (literals represented as positive integers).
    *
    * @author Matthias Nickles
    * @return Option[model as array of elis, model as hash set of elis] or None (UNSAT)
    */
  def sampleSingleRacing(tempFacts: List[Eli] = Nil): Option[(Array[Eli], IntOpenHashSet)] = {

    @Contended @volatile var stopSolverThreads = false

    case class SolverThreadInfo(thread: Thread, progressNormalized: Double = 0d)

    val progressNormalizedPerThread = scala.collection.concurrent.TrieMap[Int, SolverThreadInfo]()

    val progressCheckEveryTrials = progressCheckEveryTrialsR

    var progressCheckEveryTrialsState = progressCheckEveryTrials

    val threadChangeCheckFreq = Math.abs(abandonOrSwitchSlowThreads).toInt.max(1)

    var threadChangeCheckFreqState = threadChangeCheckFreq

    /**
      * Computes a single model. Typically not called directly but via method sampleSingleRacing().
      *
      * @author Matthias Nickles
      * @param singleSolverConf
      * @return Option[model as array of elis, model as hash set of elis] or None (UNSAT) or null (aborted)
      */
    def sampleSingle(singleSolverConf: SingleSolverConf): Option[(Array[Eli], IntOpenHashSet)] = {

      import singleSolverConf._

      Thread.currentThread().setPriority(Thread.MAX_PRIORITY)

      progressNormalizedPerThread.put(threadNo, new SolverThreadInfo(thread = Thread.currentThread()))

      var trialsAtLastImprovement = 0 // used for abandonOrSwitchSlowThreads, see code

      var trialsSinceLastProgress = 0 // used for abandonOrSwitchSlowThreads, see code

      @inline def unsat: Unit = {

        stopSolverThreads = true

        println("\nUNSAT" + (if (verbose) "\n  (reporting: solver thread " + threadNo + ")" else ""))

      }

      val solverTimer = System.nanoTime()

      val rngLocal = /*rngLocalL*/ if (seed == -1l) new java.util.SplittableRandom() else new java.util.SplittableRandom(seed)

      val med: Int = if (noOfAllElis == 0) 1 else (0x7fffffff / noOfAllElis + 1)

      val medAbs: Int = if (noOfAllElis == 0) 1 else (0x7fffffff / noOfPosElis + 1)

      val rngLocalL = new XORShift32(if (seed == -1l) Optional.empty() else Optional.of(seed)) { // not thread-safe

        @inline def nextEli(): Eli = { // Remark: code generated by Scala 2.12.8 for this method is not yet understood by Graal as of 10 Feb 2019

          nextPosInt() / med

        }

        @inline def nextPosEli(): Eli = nextPosInt() / medAbs

      }

      var fastIntRandSeed = rngLocal.nextInt()

      /**
        * Fast but low quality. Not thread-safe.
        *
        */
      @inline def fastIntRand: Int = {

        fastIntRandSeed = 214013 * fastIntRandSeed + 2531011

        (fastIntRandSeed >> 16) & 0x7FFF

      }

      /**
        * Fast but low quality. Not thread-safe.
        *
        */
      @inline def fastFloatRand: Float = fastIntRand.toFloat / 0x7FFF

      @inline def nextFloatRngLocal(): Float = fastFloatRand

      val sccCache = mutable.HashMap[mutable.Seq[Eli], ArrayBuffer[ArrayBuffer[Eli]]]()

      val noHeap = noHeapR == 1

      var maxBurst = if (noHeap || useBurstWithHeap) maxBurstRR else 0

      var freeEliSearchApproach4or1or5or9 = freeEliSearchApproach == 4 || freeEliSearchApproach == 1 || freeEliSearchApproach == 5 || freeEliSearchApproach == 9

      var freeEliSearchApproach3or10 = freeEliSearchApproach == 3 || freeEliSearchApproach == 10

      @inline def useAbsElisInArrangementInFreeEliSearch = freeEliSearchApproach == 2 || freeEliSearchApproach == 5 || freeEliSearchApproach == 9 || freeEliSearchApproach == 1 || freeEliSearchApproach == 8

      @inline def useScoresInFreeEliSearch = freeEliSearchApproach == 2 || freeEliSearchApproach4or1or5or9 && freeEliSearchApproach != 9 ||
        freeEliSearchApproach == 3 || freeEliSearchApproach == 7

      val nogiToNogood: ObjectArrayList[IntArrayUnsafeS] = new ObjectArrayList(clarkNogoods)

      val loopNogoods: ObjectArrayList[IntArrayUnsafeS] = if (emitClauses) new ObjectArrayList[IntArrayUnsafeS]() else null.asInstanceOf[ObjectArrayList[IntArrayUnsafeS]]

      @inline def primeUnassignedProbWithFalse(eli: Eli) =
        eliToNogisClark(eli).length.toFloat / nogiToNogood.size.toFloat * noOfPosElis

      val arrangeEliPool = if (arrangeEliPoolR <= 4) arrangeEliPoolR else
        Math.floor(nextFloatRngLocal() / 0.2)

      val elisSeq = if (useAbsElisInArrangementInFreeEliSearch)
        (0 until noOfPosElis).toArray
      else
        (0 until noOfAllElis).toArray

      val elisArranged: IntArrayUnsafeS = if (arrangeEliPool == 0)
        null.asInstanceOf[IntArrayUnsafeS]
      else if (arrangeEliPool == 3 || arrangeEliPool == 4) {

        val elisSeqUnsafe = new IntArrayUnsafeS(elisSeq, aligned = true)

        //shuffleArrayUnsafe(elisSeqUnsafe, rngLocal)

        elisSeqUnsafe

      } else {

        new IntArrayUnsafeS(elisSeq.sortBy({ case ((eli: Eli)) =>

          if (useAbsElisInArrangementInFreeEliSearch)
            (eliToNogisClark(eli).length + eliToNogisClark(negateEli(eli)).length) * (if (arrangeEliPool == 1) 1 else -1)
          else
            (eliToNogisClark(eli).length) * (if (arrangeEliPool == 1) 1 else -1)

        }), aligned = true)

      }

      val absEliScore = new FloatArrayUnsafeS(noOfPosElis, absEliScoreInitVal, true)

      val unassignedAbsElisQueue = if (freeEliSearchApproach == 11) {

        val r = new IntHeapPriorityQueue(noOfPosElis * 2, new IntComparator {

          @inline override def compare(o1: Eli, o2: Eli): Int = (absEliScore.get(o2) - absEliScore.get(o1)).toInt

        })

        (0 until noOfPosElis).foreach(r.enqueue(_))

        r

      } else null.asInstanceOf[IntHeapPriorityQueue]

      val entryFreeEliSearchFrom0Threshold = (Math.sqrt(nogiToNogood.size).toInt).max(1024)

      val nogiCapacityInit = next2Pow(clarkNogoods.length * 2)

      nogiToNogood.ensureCapacity(nogiCapacityInit)

      val eliToNogis: Array[ArrayValExtensibleIntUnsafe] = eliToNogisClark.clone().map(ausf => new ArrayValExtensibleIntUnsafe(ausf.getContent.clone()))

      var eliScoreUpdateFact = absEliScoreFact

      var warnMessageEliScoreOutOfRangeShown = false

      val restartTriggerConf = restartTriggerConfR

      //val localSolverParallelThreshForUnitProp = localSolverParallelThresh

      val useNogisPerEliAsOrderForAbsEliPool = (arrangeEliPool == 1 || arrangeEliPool == 2) /*<- not the same, but the same principle*/ &&
        freeEliSearchApproach3or10

      val useEliScoresAsOrderForAbsEliPool = false && freeEliSearchApproach == 3 // not recommended

      val noNogisPerAbsEliForAbsEliPool: Array[Int] = if (useNogisPerEliAsOrderForAbsEliPool)
        (0 until noOfPosElis).map(absEli =>
          eliToNogis(absEli).length + eliToNogis(negatePosEli(absEli)).length).toArray else null.asInstanceOf[Array[Int]]

      val priorityCompNogisPerEliForAbsEliPool = new IntComparator {

        @inline override def compare(o1: Eli, o2: Eli) = {

          val delta = if (arrangeEliPool == 1) noNogisPerAbsEliForAbsEliPool(o2) - noNogisPerAbsEliForAbsEliPool(o1) else noNogisPerAbsEliForAbsEliPool(o1) - noNogisPerAbsEliForAbsEliPool(o2)

          if (delta > 0f)
            1
          else if (delta < 0f)
            -1
          else
            0

        }

      }

      val priorityCompEliScoresForAbsEliPool = new IntComparator { // TODO: not ideal - see comment further below

        @inline override def compare(o1: Eli, o2: Eli) = {

          val delta = absEliScore.get(o2) - absEliScore.get(o1)

          if (delta > 0f)
            1
          else if (delta < 0f)
            -1
          else
            0

        }

      }

      val allowSwitchFreeEliSearchApproach = abandonOrSwitchSlowThreads != 0d && slowThreadAction == 3

      val unassignedAbsElisPool = if (freeEliSearchApproach3or10 || allowSwitchFreeEliSearchApproach) {

        assert(!useEliScoresAsOrderForAbsEliPool || !useNogisPerEliAsOrderForAbsEliPool)

        if (useEliScoresAsOrderForAbsEliPool) // NB: if we don't do this, we still consider eli scores in findFreeEli if freeEliSearchApproach == 3
          new Int2BooleanRBTreeMap(priorityCompEliScoresForAbsEliPool /* <- issue: this comparator is "dynamic" (changes scores after insertion), which messes up key removal and slows down tree operations */) {

            @inline def reassess(key: Int): Unit = { // doesn't work with GraalVM/substratevm if compiled with Scala 2.12

              if (containsKey(key))
                put(key, remove(key))


            }

          } else if (useNogisPerEliAsOrderForAbsEliPool)
          new Int2BooleanRBTreeMap(priorityCompNogisPerEliForAbsEliPool) {

            @inline def reassess(key: Int): Unit = {}

          } else
          new Int2BooleanRBTreeMap() {

            @inline def reassess(key: Int): Unit = {}

          }

      } else null

      @inline def rearrangeUnassignedAbsElisPool = {

        (0 until noOfPosElis).foreach(eli => unassignedAbsElisPool.put(eli, {

          if (true /*!primeUnassigned*/ )
            rngLocalL.nextFloat() < 0.5f /*.nextBoolean()*/
          else
            primeUnassignedProbWithFalse(eli) < 0.5f

        }))

      }

      if (unassignedAbsElisPool != null)
        rearrangeUnassignedAbsElisPool

      val useUnassignedAbsElisPoolCache = true // only relevant for the case where we have to loop over the unassigned absElis

      var unassignedAbsElisPoolCache = Array[Eli]()

      var unassignedAbsElisPoolCacheDirty = true

      @inline def resetAbsEliActi(clearUnassignedPool: Boolean = true) = {

        var absEliAddr = absEliScore.addr

        val absEliAddrMax = absEliAddr + (noOfPosElis << 2)

        while (absEliAddr < absEliAddrMax) {

          unsafe.putFloat(absEliAddr, absEliScoreInitVal)

          absEliAddr += 4

        }

        if (clearUnassignedPool && unassignedAbsElisPool != null) {

          unassignedAbsElisPool.clear()

          unassignedAbsElisPoolCacheDirty = true

        }

      }

      resetAbsEliActi(clearUnassignedPool = false)

      var someFreeEli1: Eli = rngLocalL.nextPosInt() / med // rngLocalL.nextEli()
      var someFreeEli2: Eli = rngLocalL.nextPosInt() / med // rngLocalL.nextEli()
      var someFreeEli3: Eli = rngLocalL.nextPosInt() / med // rngLocalL.nextEli()
      var someFreeEli4: Eli = rngLocalL.nextPosInt() / med //  rngLocalL.nextEli()

      class ForceElisIndexedSet(randomizeAccess: Boolean) extends IndexedSet(noOfAllElis, rngLocalL) with ForceElis {

        @inline override def addv(eli: Eli): Unit = {

          add(eli)

        }

        @inline override def hasMore: Boolean = {

          size > 0

        }

        @inline override def getNext: Eli = {

          if (randomizeAccess)
            getRemoveRandom()
          else
            getRemoveLast()

        }

        @inline override def reset: Unit = {

          clear()

        }

      }

      class ForceElisArraySet(maxSize: Int = next2Pow(noOfAllElis * 2), noDuplicates: Boolean) extends IntArrayUnsafeS(maxSize, aligned = true) with ForceElis {

        @Contended var addrCounter = addr

        @inline override def addv(eli: Eli): Unit = {

          if (addrCounter == addr || !noDuplicates || !contains(eli, addrCounter)) {

            unsafe.putInt(addrCounter, eli)

            addrCounter += 4l

          }

        }

        @inline override def hasMore: Boolean = {

          addrCounter > addr

        }

        @inline override def getNext: Eli = {

          addrCounter -= 4l

          unsafe.getInt(addrCounter)

        }

        @inline override def reset: Unit = {

          addrCounter = addr

        }

        @inline def getCounter: Int = (addrCounter - addr).toInt >> 2

      }

      val deficitOrderedUncertainLiteralsHalf = deficitOrderedUncertainLiteralsForJava.size / 2 // each variable appears twice (pos and neg polarity), we only need their lowest ranked literals

      val ignoreParamVariables = ignoreParamVariablesR || deficitOrderedUncertainLiteralsHalf == 0

      val rndmBranch = rndmBranchR

      val passPrevious = if (globalPassCache) passPreviousGlobal else {

        if (!freeEliSearchApproach3or10 || allowSwitchFreeEliSearchApproach)
          new ByteArrayUnsafeS(noOfPosElis, 0x00.toByte /*<- sensitive value*/ , true) // 0x01.toByte could be used to indicate "don't know", but doesn't seem to have a positive effect
        else
          null.asInstanceOf[ByteArrayUnsafeS]

      }

      if (primeUnassigned && passPrevious != null && !globalPassCache)
        (0 until noOfPosElis).foreach(posEli => {

          if (primeUnassignedProbWithFalse(posEli) < 0.5f)
            passPrevious.update(posEli, 0xFF.toByte)
          else
            passPrevious.update(posEli, 0x00.toByte)

        })

      val pass = new IntArrayUnsafeS(noOfAllElis, initialValue = 0, aligned = true) // the partial assignment. Item == 0: eli is unassigned or doesn't hold

      val dlToFirstOrder = new IntArrayUnsafeS(noOfPosElis + 1, initialValue = Int.MinValue, aligned = true)
      // We will use binary search in this, which should be fine as
      // the actual number of decision levels (upper bound of search area) is typically not that large (i.e., fits in cache or at least page).

      val orderToDlCache = new IntArrayUnsafeS(noOfPosElis + 1, initialValue = -1, aligned = true)

      var orderNo = 1 // sequence number of next eli assignment (not necessarily consecutive). Cannot be zero.

      var dl: Int = 0 // decision level (increased at each nondeterministic branching literal decision)

      val eliToRemainders = new Array[ObjectArrayList[NogoodRemainder]](next2Pow(noOfAllElis))

      val nogiToRemainder = new ObjectArrayList[NogoodRemainder]()

      nogiToRemainder.ensureCapacity(nogiCapacityInit)

      val useBurstableForceElis = false //!ignoreParamVariables || maxBurst != 0 && burstPlainElis
      // TODO: true ^ currently not supported, occasionally leads to inconsistencies for reasons tbd.

      assert(!useBurstableForceElis)

      val forceElis: ForceElis = if (noHeap) null else (if (!useBurstableForceElis) new ForceElisIndexedSet(randomizeAccess = true)
      else
        new ForceElisArraySet(next2Pow(noOfAllElis * 2), noDuplicates = true))
      // ^ the next batch of deductively inferable literals. Not used with noHeap = true.

      var conflictNogi = -1

      val maxAbsEliAddr = pass.getAddr + ((noOfPosElis - 1) << 2) // i.e. the last pos eli address

      val absEliAddrNegOffset = posNegEliBoundary << 2

      var entryFreeEliAddrSearch = pass.getAddr

      var entryFreeEliIAddrSearch = if (elisArranged != null) elisArranged.getAddr else -1l

      val maxEliIAddr = if (elisArranged != null) elisArranged.getAddr + (noOfAllElis << 2) else -1l // actually one behind max address

      val maxAbsEliIAddr = if (elisArranged != null) elisArranged.getAddr + (noOfPosElis << 2) else -1l

      log("solverTimer 1: " + timerToElapsedMs(solverTimer) + " ms")

      @inline def setDecisionLevel(newDl: Int, updateDlToFirstOrder: Boolean = true): Unit = {
        // NB: this function must only be called if afterwards at least one eli is assigned on the new level

        dl = newDl

        if (updateDlToFirstOrder) {

          dlToFirstOrder.update(dl, orderNo) // the next order goes to the new level

          orderToDlCache.update(orderNo, dl)

        }

      }

      @inline def dlFromOrder(o: Int, dlLow: Int): Int = {

        if (orderToDlCache.get(o) != -1)
          orderToDlCache.get(o)
        else {

          val r = dlToFirstOrder.binSearch(o, dlLow, dl /*<- inclusive*/)

          orderToDlCache.update(o, r)

          r

        }

      }

      var avgNormProgress = 0d

      val threadmxBean = ManagementFactory.getThreadMXBean()

      var noOfConflictsTotal = 0

      var noOfConflictsAfterRestart = 0

      var noOfTrialsAtLastRestart = 0

      var noOfRestarts = 0

      var firstRecordedNogi = -1

      class NogoodRemainder(val pool: IntArrayUnsafeS, var nogi: Nogi) {
        // NB: constructor doesn't set the two lits, so we need to call reset (unless we know both lits must be -1)

        var notsetCounter = pool.sizev // meaningless if is2

        var cachedUnsetItem: Eli = -1 // used only if useCounters

        var hdNotsetItem = -1 // not used if |pool| = 2. NB: observe the order of the two lits and their treatment at jump backs after conflicts.

        var tlNotsetItem = -1 // not used if |pool| = 2.

        val is2 = pool.sizev == 2

        val lastPoolAddr = pool.getAddr + ((pool.sizev - 1) << 2)

        var runningAddr = pool.addr

        @inline def count: Int = {

          assert(!is2)

          var counter = 0

          var start = lastPoolAddr

          while (start >= pool.addr) {

            if (isNotSetInPass(sharedDefs.unsafe.getInt(start))) {

              if (cachedUnsetItem == -1)
                cachedUnsetItem = sharedDefs.unsafe.getInt(start)

              counter += 1

            }

            start -= 4

          }

          counter

        }

        @inline def reset: Unit = { // resets counter or fills hdNotsetItem and tlNotsetItem lits with UNset items (e.g., unassignedPosElis elis), unless |pool| = 2.

          if (!is2) {

            if (useCounters) {

              cachedUnsetItem = -1

              notsetCounter = count

            } else {

              hdNotsetItem = -1

              tlNotsetItem = -1

              var start = pool.addr

              while (start <= lastPoolAddr) {

                if (isNotSetInPass(sharedDefs.unsafe.getInt(start))) {

                  if (hdNotsetItem == -1)
                    hdNotsetItem = sharedDefs.unsafe.getInt(start)
                  else if (sharedDefs.unsafe.getInt(start) != hdNotsetItem) {

                    tlNotsetItem = sharedDefs.unsafe.getInt(start)

                    return

                  }

                }

                start += 4

              }

            }

          }

        }

        @inline def unSetItem(item: Eli): Unit = {

          if (!is2) {

            if (useCounters) {

              notsetCounter += 1

              if (cachedUnsetItem == -1)
                cachedUnsetItem = item

            } else if (hdNotsetItem == -1 && item != tlNotsetItem) {

              hdNotsetItem = item

            } else if (tlNotsetItem == -1 && item != hdNotsetItem) {

              tlNotsetItem = item

            }

          }

        }

        @inline private def fillUp: Unit = {

          // assert(pool.sizev != 2)
          // assert(!useCounters)

          if (pool.sizev >= 2) {

            val start = runningAddr

            do {

              if (isNotSetInPass(sharedDefs.unsafe.getInt(runningAddr)) && sharedDefs.unsafe.getInt(runningAddr) != hdNotsetItem) {

                tlNotsetItem = sharedDefs.unsafe.getInt(runningAddr)

                /*if (runningAddr == lastPoolAddr)
                  runningAddr = pool.addr
                else
                  runningAddr += 4*/

                return

              }

              if (runningAddr == lastPoolAddr)
                runningAddr = pool.addr
              else
                runningAddr += 4

            } while (runningAddr != start)

          }

          tlNotsetItem = -1

        }

        @inline private def getIndicCase2: Int = {

          // assert(pool.sizev == 2)

          if (isSetInPass(pool.get(0))) {

            if (isSetInPass(pool.get(1)))
              -1
            else
              pool.get(1)

          } else if (isSetInPass(pool.get(1)))
            pool.get(0)
          else
            Int.MaxValue

        }

        @inline private def getIndicNot2NoCounters: Int = {

          // assert(pool.sizev != 2)
          // assert(!useCounters)

          if (hdNotsetItem == -1)
            -1
          else if (tlNotsetItem == -1)
            hdNotsetItem
          else
            Int.MaxValue

        }

        @inline private def getIndicNot2Counters: Int = {

          if (notsetCounter > 1)
            Int.MaxValue
          else if (notsetCounter == 0)
            -1
          else {

            if (cachedUnsetItem != -1)
              return cachedUnsetItem

            var start = pool.addr

            do {

              if (isNotSetInPass(sharedDefs.unsafe.getInt(start)))
                return sharedDefs.unsafe.getInt(start)

              start += 4

            } while (start <= lastPoolAddr)

            stomp(-10000, "Value of notsetCounter is inconsistent")

            Int.MaxValue

          }

        }

        @inline def getIndic: Int = {

          if (is2)
            getIndicCase2
          else if (useCounters)
            getIndicNot2Counters
          else
            getIndicNot2NoCounters

        }

        @inline private def setItemPureNot2(item: Eli) = {

          // assert(pool.sizev != 2)
          // assert(!useCounters)

          if (item == hdNotsetItem) {

            if (tlNotsetItem != -1) {

              hdNotsetItem = tlNotsetItem

              fillUp

            } else
              hdNotsetItem = -1

          } else if (item == tlNotsetItem)
            fillUp

        }

        @inline def setItemIndic(item: Eli): Int = {

          if (is2)
            getIndicCase2
          else if (useCounters) {

            if (item == cachedUnsetItem)
              cachedUnsetItem = -1

            notsetCounter -= 1

            getIndicNot2Counters

          } else {

            setItemPureNot2(item)

            getIndicNot2NoCounters

          }

        }

      }

      // class NogoodRemainderTEST last internal version: 9th Feb 2019

      @inline def isSetInPass(eli: Eli): Boolean = pass.get(eli) != 0

      @inline def isNotSetInPass(eli: Eli): Boolean = pass.get(eli) == 0

      @inline def isAbsSetInPass(eli: Eli): Boolean = {

        pass.get(eli) != 0 || {

          if (eli < posNegEliBoundary)
            pass.get(eli + posNegEliBoundary)
          else
            pass.get(eli - posNegEliBoundary)

        } != 0

      }

      @inline def isNotAbsSetInPass(eli: Eli): Boolean = {

        pass.get(eli) == 0 && {

          if (eli < posNegEliBoundary)
            pass.get(eli + posNegEliBoundary)
          else
            pass.get(eli - posNegEliBoundary)

        } == 0

      }

      @inline def isPosEliNotAbsSetInPass(eli: Eli): Boolean = {

        pass.get(eli) == 0 && pass.get(eli + posNegEliBoundary) == 0

      }

      @inline def isAbsNotSetInPassInt(eli: Eli): Int = {

        if (pass.get(eli) != 0 || {

          if (eli < posNegEliBoundary)
            pass.get(eli + posNegEliBoundary) != 0
          else
            pass.get(eli - posNegEliBoundary) != 0

        }) 0 else 1

      }

      @inline def setInPass(eli: Eli): Unit = { // this and setInPassIfUnassigned must be the only ways (besides initialization) of assigning True to an eli.

        //assert(!isAbsSetInPass(eli))  // must hold when calling this function!
        //assert(orderNo > 0)

        assert(isNotSetInPass(negateEli(eli))) // if this fails, first check that the branching eli and its negation are both unset after
        // findFreeEli.
        // Another possible failure reason: if setting an eli in pass doesn't immediately reduce the nogood remainders with that eli.
        //
        // (Remark: it's temporarily possible that both eli and its negation are set, when a conflict has stopped propagation of unit elis
        // (so that eli had been fired but not all set to "set" in all affected nogoods, so that -eli could still fire). However,
        // in that case jumping back after the conflict unsets eli.)

        pass.update(eli, orderNo)

        orderNo += 1

        if (freeEliSearchApproach3or10) {

          unassignedAbsElisPool.remove(toAbsEli(eli))

          //the following doesn't hold in general after ^, as we might dynamically change the order which messes up the search for keys:
          //   assert(!unassignedAbsElisPool.containsKey(toAbsEli(eli)))

        }

      }

      @inline def setInPassIfUnassigned(eli: Eli): Boolean = {

        pass.compareWithZeroAndUpdate(eli, orderNo) && {

          assert(isNotSetInPass(negateEli(eli))) // if this fails, first check that the branching eli and its negation are both unset after findFreeEli
          // and that no further elis are assigned after a conflict (before conflict resolution).
          // NB: see remark in setInPass()

          if (freeEliSearchApproach3or10) {

            unassignedAbsElisPool.remove(toAbsEli(eli))

            //the following doesn't hold in general after ^, as we might dynamically change the order which messes up the search for keys:
            //  assert(!unassignedAbsElisPool.containsKey(toAbsEli(eli)))

          }

          orderNo += 1

          true

        }

        /* semantically equivalent:

        if (isNotSetInPass(eli)) {

          setInPass(eli)

          true

        } else
          false
        */

      }

      @inline def clearInPass(eli: Eli) = { // must be the only way (after preprocessing/initialization) of assigning False to an eli. Must not update nogood remainder.

        assert(isSetInPass(eli))

        if (freeEliSearchApproach3or10) {

          unassignedAbsElisPool.put(toAbsEli(eli), isPosEli(eli))

          unassignedAbsElisPoolCacheDirty = true

        } else {

          if (isPosEli(eli))
            passPrevious.update(eli, true)
          else
            passPrevious.update(negateNegEli(eli), false)

          if (freeEliSearchApproach == 11)
            unassignedAbsElisQueue.enqueue(toAbsEli(eli))
          else if (freeEliSearchApproach4or1or5or9) {

            if (isSetInPass(someFreeEli1) || absEliScore.get(toAbsEli(eli)) > absEliScore.get(toAbsEli(someFreeEli1)))
              someFreeEli1 = eli
            else if (isSetInPass(someFreeEli2) || absEliScore.get(toAbsEli(eli)) > absEliScore.get(toAbsEli(someFreeEli2)))
              someFreeEli2 = eli
            else if (isSetInPass(someFreeEli3) || absEliScore.get(toAbsEli(eli)) > absEliScore.get(toAbsEli(someFreeEli3)))
              someFreeEli3 = eli
            else if (isSetInPass(someFreeEli4) || absEliScore.get(toAbsEli(eli)) > absEliScore.get(toAbsEli(someFreeEli4)))
              someFreeEli4 = eli

          }

        }

        pass.update(eli, 0)

        orderNo -= 1

      }

      @inline def orderOfEli(eli: Eli): Int = pass.get(eli)

      @inline def decisionLevelOfEli(eli: Eli) = { // result is only valid if eli is assigned (i.e., orderOfEli != 0),
        // otherwise result of this method is undefined.

        dlFromOrder(orderOfEli(eli), dlLow = 0)

      }

      trait ForceElis {

        @inline def addv(eli: Eli): Unit

        @inline def hasMore: Boolean

        @inline def getNext: Eli

        @inline def reset: Unit

      }

      class ForceElisSet extends it.unimi.dsi.fastutil.ints.IntRBTreeSet with ForceElis {

        @inline override def addv(eli: Eli): Unit = {

          add(eli)

        }

        @inline override def hasMore: Boolean = {

          !isEmpty

        }

        @inline override def getNext: Eli = {

          val eli = firstInt()

          remove(eli)

          eli

        }

        @inline override def reset: Unit = {

          clear()

        }

      }

      var ni = 0

      while (ni < nogiToNogood.size) {

        val remainder = new NogoodRemainder(pool = nogiToNogood.get(ni) /*<- we must assign the reference in nogiToNogood, not some copy*/ , ni)

        remainder.reset

        nogiToRemainder.add(remainder)

        ni += 1

      }

      var ei = 0

      while (ei < noOfAllElis) {

        eliToRemainders(ei) = new ObjectArrayList[NogoodRemainder]()

        eliToRemainders(ei).ensureCapacity(8192)

        eliToNogis(ei).traverseUntil(nogi => {

          eliToRemainders(ei).add(nogiToRemainder.get(nogi))

          false

        })

        ei += 1

      }

      @inline val propagate: Nogi => Boolean = if (rndmIgnLearnedNogoodThresholdR >= 0f)
        (triggerNogi: Nogi) => nextFloatRngLocal() > rndmIgnLearnedNogoodThresholdR * (firstRecordedNogi / triggerNogi.max(1).toFloat)
      else {

        (triggerNogi: Nogi) => {

          triggerNogi < firstRecordedNogi || noOfConflictsTotal < 3000 || triggerNogi > nogiToNogood.size - (nogiToNogood.size - firstRecordedNogi) * -rndmIgnLearnedNogoodThresholdR
          // Remark: there is no guarantee that the most recent x% contain any learned loop nogoods, but that's not an issue in practice, might just lead
          // to some more restarts if -rndmIgnLearnedNogoodThresholdR is too small.

        }

      }

      log("solverTimer 2: " + timerToElapsedMs(solverTimer) + " ms")

      @inline def checkFireNogood(remainder: NogoodRemainder, nogi: Nogi): Unit = {

        val indic = remainder.getIndic

        if (indic == -1)
          conflictNogi = nogi
        else if (indic != Int.MaxValue) { // the only remaining unassigned eli in nogood is unit resulting

          if (noHeap)
            setEliWithNogoodUpdatesNoHeap(negateEli(indic))
          else
            forceElis.addv(negateEli(indic))

        }

      }

      // (last internal ver with setEliWithNogoodUpdatesParNoHeap: 10 Feb 2019)

      @inline def setEliWithNogoodUpdatesNoHeap(eli: Eli): Unit = {

        if (conflictNogi == -1 && setInPassIfUnassigned(eli)) {

          val il = eliToRemainders(eli).size

          if (il == 0)
            return
          else {

            var ri = 0

            var prop = propagate(eliToRemainders(eli).get(il - 1).nogi)

            val rmiStore = if (prop) new IntOpenHashSet(32, 0.75f) else null // don't use any Unsafe or off-heap data structure here

            do {

              val rmi = eliToRemainders(eli).get(ri).setItemIndic(eli)

              if (rmi == -1) {

                if (conflictNogi == -1)
                  conflictNogi = eliToRemainders(eli).get(ri).nogi

                if (!useCounters)
                  return
                else
                  prop = false // we must not set any further elis after a conflict has been encountered

              } else if (prop && rmi != Int.MaxValue)
                rmiStore.add(rmi)

              ri += 1

            } while (ri < il)

            if (prop) {

              val it = rmiStore.iterator()

              while (it.hasNext() && conflictNogi == -1)
                setEliWithNogoodUpdatesNoHeap(negateEli(it.nextInt()))

            }

          }

        }

      }

      var nogi: Nogi = 0

      val ntngl = nogiToNogood.size

      while (nogi < ntngl) {

        val nogood = nogiToNogood.get(nogi)

        if (nogood.sizev == 0) {

          unsat

          return None

        }

        nogi += 1

      }

      @inline def activUpVar(absEli: sharedDefs.Eli) = {

        absEliScore.update(absEli, absEliScore.get(absEli) * eliScoreUpdateFact)

        if (freeEliSearchApproach3or10) {

          //unassignedAbsElisPool.reassess(absEli)

          if (unassignedAbsElisPool.isInstanceOf[Int2BooleanRBTreeMap]) {

            if (unassignedAbsElisPool.containsKey(absEli))
              unassignedAbsElisPool.put(absEli, unassignedAbsElisPool.remove(absEli))

          }

        }

      }

      def conflictAnalysis(conflNogi: Nogi):
      (Int /*new decision level to jump to*/ , IntArrayUnsafeS /*learned nogood*/ , Int /*sigmaEli*/ ) = {

        val conflNogood = nogiToNogood.get(conflNogi)

        if (useScoresInFreeEliSearch) {

          var i = conflNogood.sizev - 1

          while (i >= 0) {

            activUpVar(toAbsEli(conflNogood.get(i)))

            i -= 1

          }

        }

        val accumulatedNogoodBuilder = new ArrayValExtensibleIntUnsafe(conflNogood.clone(0))

        var lp = true

        var sigmaEli = -1

        var k = -1

        var accI = -1

        var sigmaOrder = -1

        var eli = -1

        while (lp) {

          accI = accumulatedNogoodBuilder.length - 1

          sigmaOrder = -1

          while (accI >= 0) {

            eli = accumulatedNogoodBuilder.get(accI)

            if (eli != -1) {

              val orderEli = orderOfEli(eli)

              if (orderEli > sigmaOrder) {

                sigmaOrder = orderEli

                sigmaEli = eli

              }

            }

            accI -= 1

          }

          val sigmaEliDecisionLevel = decisionLevelOfEli(sigmaEli)

          k = 0

          var pi = accumulatedNogoodBuilder.length - 1

          var shotOutSigma = -1

          while (pi >= 0) {

            if (accumulatedNogoodBuilder.get(pi) != -1) {

              if (accumulatedNogoodBuilder.get(pi) != sigmaEli) {

                val d = decisionLevelOfEli(accumulatedNogoodBuilder.get(pi))

                if (d > k)
                  k = d

              } else {

                shotOutSigma = pi

                accumulatedNogoodBuilder.buffer.update(pi, -1)

              }

            }

            pi -= 1

          }

          if (k == sigmaEliDecisionLevel) { // we haven't found a UIP yet

            val sigmaNot = negateEli(sigmaEli)

            val orderOfSigma = sigmaOrder

            // since current sigmaEli is not a decision literal, so there must have been some nogood which has "fired" sigmaEli:

            val candNogis = eliToNogis(sigmaNot).buffer

            val candNogisLength = eliToNogis(sigmaNot).length

            var candNogisI = 0

            var eps: Nogi = -1

            var candNogood = null.asInstanceOf[IntArrayUnsafeS]

            while (candNogisI < candNogisLength && eps == -1) {

              candNogood = nogiToNogood.get(candNogis.get(candNogisI))

              val fa: Boolean = {

                var i = 0

                while (i < candNogood.sizev) {

                  if (candNogood.get(i) == sigmaNot)
                    i += 1
                  else {

                    if (isNotSetInPass(candNogood.get(i))
                      /*<- effectively !isSetInPass(toAbsEli)*/ || orderOfEli(candNogood.get(i)) >= orderOfSigma)
                      i = Int.MaxValue
                    else
                      i += 1

                  }

                }

                i < Int.MaxValue

              }

              if (fa)
                eps = candNogis.get(candNogisI)
              else
                candNogisI += 1

            }

            if (eps == -1) // important check, don't disable! If this check fails, this
              stomp(-10000, "eps == -1 in conflictAnalysis") // typically (but not necessarily) indicates that elis have been assigned out of order, or an toAbsEli was assigned
            // after a conflict was detected.
            // E.g., neg(eli) is assigned True before the other elis within the unit-resulting nogood have been set to True.

            val ngEps = nogiToNogood.get(eps)

            val accLenOld = accumulatedNogoodBuilder.length

            var ngEpsI = ngEps.sizev - 1

            while (ngEpsI >= 0) {

              if (ngEps.get(ngEpsI) != sigmaNot && !accumulatedNogoodBuilder.contains(ngEps.get(ngEpsI), until = accLenOld.toInt))
                accumulatedNogoodBuilder.append(ngEps.get(ngEpsI))

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

      var noOfConflictsBeforeRestart: Double = restartTriggerConf._2

      val lubySeq = ArrayBuffer[Int]()

      lubySeq.sizeHint(if (restartTriggerConf._1 == 3) 4096 else 0)

      lubySeq.append(-1 /*<- dummy*/ , 1)

      val l2km1ForLuby = Array(/*k=1:*/ 1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383,
        32767, 65535, 131071, 262143, 524287, 1048575)

      val clearInJumpBackTasks = new ObjectArrayList[Runnable]()

      var remaindersToClear: ObjectArrayList[NogoodRemainder] = null

      var nweh = -1

      var eliToClear = -1

      var cdlcl = null.asInstanceOf[CountDownLatch]

      clearInJumpBackTasks.add(() => {

        var i = 0

        while (i < nweh) {

          remaindersToClear.get(i).unSetItem(eliToClear)

          i += 1

        }

        cdlcl.countDown()

      })

      clearInJumpBackTasks.add(() => {

        var i = nweh

        val il = nweh * 2

        while (i < il) {

          remaindersToClear.get(i).unSetItem(eliToClear)

          i += 1

        }

        cdlcl.countDown()

      })

      clearInJumpBackTasks.add(() => {

        var i = nweh * 2

        val il = remaindersToClear.size

        while (i < il) {

          remaindersToClear.get(i).unSetItem(eliToClear)

          i += 1

        }

        cdlcl.countDown()

      })

      @inline def fireSingletonNogoods: Boolean = {

        if (initiallyResolveSingletonNogoods) {

          assert(dl == 0)

          if (noHeap) {

            var nogi = 0

            val nogil = nogiToRemainder.size

            while (nogi < nogil) {

              val remainder = nogiToRemainder.get(nogi)

              val nogood = nogiToNogood.get(remainder.nogi)

              if (nogood.size == 1) {

                setEliWithNogoodUpdatesNoHeap(negateEli(nogood.get(0)))

                if (conflictNogi != -1)
                  return true

              }

              nogi += 1

            }

          } else {

            nogiToRemainder.forEach(remainder => {

              val nogood = nogiToNogood.get(remainder.nogi)

              if (nogood.size == 1)
                forceElis.addv(negateEli(nogood.get(0)))

            })

          }

        }

        false

      }

      @inline def jumpBack(newLevel: Int): Unit = {

        val oldOrder = orderNo

        log("Jumping back to decision level " + newLevel)

        // We remove everything with a decision level > newLevel. NB: Level newLevel itself won't be cleared, new elis are assigned
        // in additions to any which are on level newLevel already.

        conflictNogi = -1

        if (!noHeap)
          forceElis.reset

        var posEli = 0

        while (posEli < noOfPosElis) {

          @inline def clear(eli: Eli): Unit = {

            remaindersToClear = eliToRemainders(eli)

            clearInPass(eli)

            assert(isNotAbsSetInPass(eli))

            if (remaindersToClear.size < localSolverParallelThresh) {

              var i = remaindersToClear.size - 1

              while (i >= 0) {

                remaindersToClear.get(i).unSetItem(eli)

                i -= 1

              }

            } else {

              nweh = remaindersToClear.size / 3

              eliToClear = eli

              cdlcl = new CountDownLatch(3)

              localSingleSamplerThreadPool.execute(clearInJumpBackTasks.get(0))

              localSingleSamplerThreadPool.execute(clearInJumpBackTasks.get(1))

              localSingleSamplerThreadPool.execute(clearInJumpBackTasks.get(2))

              cdlcl.await()

            }

          }

          if (isSetInPass(posEli) && decisionLevelOfEli(posEli) > newLevel) // NB: decisionLevelOfEli doesn't check if eli is set
            clear(posEli)
          else if (isSetInPass(negatePosEli(posEli)) && decisionLevelOfEli(negatePosEli(posEli)) > newLevel)
            clear(negatePosEli(posEli))

          posEli += 1

        }

        var dlOi: Int = newLevel + 1

        val firstOrderNoToClear = dlToFirstOrder.get(dlOi).max(0) // dlToFirstOrder can be Int.MinValue for dlOi=0 (because it's unsure that level 0 contains
        // any elis)

        //assert(firstOrderNoToClear >= 0 && firstOrderNoToClear < orderToDlCache.sizev)

        while (dlOi <= dl + 1) {

          dlToFirstOrder.update(dlOi, Int.MinValue)

          dlOi += 1

        }

        if (newLevel == -1) { // we restart from scratch

          setDecisionLevel(0, updateDlToFirstOrder = false /*<- since the new level already exists and might be populated already*/)

          noOfConflictsAfterRestart = 1

          if (fireSingletonNogoods) {

            // unsat  // TODO (remove line after checks)

            return

          }

        } else {

          setDecisionLevel(newLevel, updateDlToFirstOrder = false /*<- since the new level already exists and might be populated already*/)

          noOfConflictsAfterRestart += 1

          noOfConflictsTotal += 1

          noOfConflictsTotalAllThreads += 1

        }

        //orderToDlCache.clear()

        var oi = firstOrderNoToClear

        while (oi <= oldOrder) {

          orderToDlCache.update(oi, -1)

          oi += 1

        }

      }

      @inline def addNogood(newNogood: IntArrayUnsafeS): Nogi = {

        val newNogi = nogiToNogood.size

        if (firstRecordedNogi == -1)
          firstRecordedNogi = newNogi

        nogiToNogood.add(newNogood)

        val newNogoodRemainder = new NogoodRemainder(pool = newNogood /*<- we must assign the reference within nogiToNogood, not some clone of the nogood */ , newNogi)

        nogiToRemainder.add(newNogoodRemainder)

        newNogoodRemainder.reset

        var i = newNogood.size - 1

        while (i >= 0) {

          val eliInNewNogood = newNogood.get(i)

          eliToNogis(eliInNewNogood).append(newNogi)

          if (noNogisPerAbsEliForAbsEliPool != null)
            noNogisPerAbsEliForAbsEliPool.update(toAbsEli(eliInNewNogood), noNogisPerAbsEliForAbsEliPool(toAbsEli(eliInNewNogood)) + 1)

          eliToRemainders(eliInNewNogood).add(newNogoodRemainder)

          i -= 1

        }

        checkFireNogood(newNogoodRemainder, newNogi)

        if (maxCompetingSolverThreads > 1 && nogoodShareProbability > 0.000001f)
          nogoodExchangePool.put(newNogood, threadNo)

        newNogi

      }

      var modelOpt: Option[(Array[Eli], IntOpenHashSet)] = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

      val xForLevelledRestarts = -Math.log10(noOfPosElis)

      @inline def printSingleLineProgress(peak: Int, trials: Int) = {

        if (!stopSolverThreads && peak >= 0) {

          print("\r")

          print("@ " + timerToElapsedMs(solverTimer) / 1000 + "sec: Peak: " + peak + "%, " +
            "Thread $" + threadNo + ": " +
            "Unassigned: " + (if (prevUnassi < 5) "< 5" else prevUnassi) + ", " +
            "#Conflicts: " + noOfConflictsTotal + ", " +
            "#Learned nogoods: " + (if (firstRecordedNogi >= 1) nogiToRemainder.size - firstRecordedNogi else 0) + ", " +
            "#Restarts: " + noOfRestarts + ", #trials (inner loop): " + trials)

          // NB: remaining unassigned literals < 1 doesn't mean we are finished, since there might still be an unresolved conflict.

        }

      }

      var uncertainEliSearchStart = 0

      var (r1, r2, r3, r4) = (-1f, -1f, -1f, -1f)

      val rndEveryTrials = ((1000000000d * rndmBranch).toInt).max(1) // (remark: 1 has same effect as diversify=true)

      log("rndEveryTrials = " + rndEveryTrials)

      var rndEveryTrialsIt = rndEveryTrials

      //println(""Time (ms) for singleSolver initialization:" + timerToElapsedMs(startSingleSolverInit))

      tempFacts.foreach(tempFactEli => {

        val factNogood = new IntArrayUnsafeS(Array(negateEli(tempFactEli)), aligned = false)

        addNogood(factNogood)

      })

      while (modelOpt == null && !stopSolverThreads) { // bounce-back loop; if program is tight or sat-mode, there is only a single iteration

        var incompleteModuloConflict = true

        var trials = 0 // inner loop trials (for truth assignment search), not sampling trials

        var maxApproachSwitches = maxApproachSwitchesPerSolverThread

        @inline def literally(eli: Eli) = -eli - 1

        val maxIAddr = if (useAbsElisInArrangementInFreeEliSearch) maxAbsEliIAddr else maxEliIAddr

        def findFreeEli: Int /*freeEli < 0: enforce -freeEli-1. Max.Int: no absfree eli found*/ = {

          // Branching decision heuristics & parameter eli decision using symbolic or automatic differentiation (partial derivative)

          /* if (variableOrNogoodElimConfig._1 && variableOrNogoodElimConfig._5) {  // TODO: (reactivate after optimization)

            val removedElisFreeOpt = removedNogoodsPerAtomOpt.flatMap(_.keys.find(!isAbsSetInPass(_)))

            if (removedElisFreeOpt.isDefined)
              return literally(removedElisFreeOpt.get)

          } */

          if (!ignoreParamVariables) {

            // We check the parameter atoms (random variables) in the order provided by the sorted partial derivatives (over multiple atoms, this
            // implicitly gives the gradient):

            var i = uncertainEliSearchStart // if there wasn't a conflict after the previous parameter eli assignment, we
            // don't need to start searching from start again. (Similar effect as with maxBurst != 0)

            while (i < deficitOrderedUncertainLiteralsHalf) {

              val uncertainEli = deficitOrderedUncertainLiteralsForJava(i)

              if (isNotAbsSetInPass(uncertainEli)) {

                uncertainEliSearchStart = if (i + 1 >= deficitOrderedUncertainLiteralsHalf) 0 else i + 1

                return literally(uncertainEli)

              }

              i += 1

            }

          }

          rndEveryTrialsIt -= 1

          if (!diversify && rndEveryTrialsIt > 0) {

            if (noOfConflictsAfterRestart > entryFreeEliSearchFrom0Threshold)
              entryFreeEliAddrSearch = pass.getAddr

            @inline def findFreeVarInElisArranged(useActivities: Boolean): Eli = {

              var freeEli = -1

              var freeVarActiv = -Float.MaxValue // NB: -Float.MaxValue in Scala (but not Java) is same as Float.MinValue

              if (arrangeEliPool > 0) {

                var eliIAddr = entryFreeEliIAddrSearch

                do {

                  if (isNotAbsSetInPass(unsafe.getInt(eliIAddr))) {

                    if (useActivities) {

                      if (absEliScore.get(toAbsEli(unsafe.getInt(eliIAddr))) > freeVarActiv) {

                        freeEli = unsafe.getInt(eliIAddr)

                        freeVarActiv = absEliScore.get(toAbsEli(unsafe.getInt(eliIAddr)))

                        if (freeEliSearchApproach == 5) {

                          entryFreeEliIAddrSearch = if (eliIAddr + 4l >= maxIAddr) elisArranged.getAddr else eliIAddr + 4l

                          return freeEli

                        }

                      }

                    } else {

                      entryFreeEliIAddrSearch = if (eliIAddr + 4l >= maxIAddr) elisArranged.getAddr else eliIAddr + 4l

                      return unsafe.getInt(eliIAddr)

                    }

                  }

                  if (eliIAddr + 4l < maxIAddr)
                    eliIAddr += 4l
                  else
                    eliIAddr = elisArranged.getAddr

                } while (eliIAddr != entryFreeEliIAddrSearch)

                entryFreeEliIAddrSearch = if (eliIAddr + 4l >= maxIAddr) elisArranged.getAddr else eliIAddr + 4l

                freeEli

              } else { // no specific arrangement, so we just iterate through all the elis in their original sequence

                // NB: here we always look only at the abs (ri.e., positive) elis, since we record activities for abs elis only and
                // the elis arrangement is considered arbitrary (it could still have an influence, but unlikely).

                val entryFreeEliAddrSearchStart = entryFreeEliAddrSearch

                do {

                  if (unsafe.getInt(entryFreeEliAddrSearch + absEliAddrNegOffset) == 0 && unsafe.getInt(entryFreeEliAddrSearch) == 0) {

                    if (useActivities) {

                      val absEliCand = ((entryFreeEliAddrSearch - pass.getAddr) >>> 2).toInt

                      if (freeEliSearchApproach == 5)
                        return absEliCand
                      else if (absEliScore.get(absEliCand) > freeVarActiv) {

                        freeVarActiv = absEliScore.get(absEliCand)

                        freeEli = absEliCand

                      }

                    } else {

                      val r = (((entryFreeEliAddrSearch - pass.getAddr) >>> 2)).toInt

                      if (entryFreeEliAddrSearch >= maxAbsEliAddr)
                        entryFreeEliAddrSearch = pass.getAddr
                      else
                        entryFreeEliAddrSearch += 4l

                      return r

                    }
                  }

                  if (entryFreeEliAddrSearch >= maxAbsEliAddr)
                    entryFreeEliAddrSearch = pass.getAddr
                  else
                    entryFreeEliAddrSearch += 4l

                } while (entryFreeEliAddrSearch != entryFreeEliAddrSearchStart)

                freeEli

              }

            }

            if (freeEliSearchApproach4or1or5or9) {

              r1 = isAbsNotSetInPassInt(someFreeEli1) * absEliScore.get(toAbsEli(someFreeEli1))

              r2 = isAbsNotSetInPassInt(someFreeEli2) * absEliScore.get(toAbsEli(someFreeEli2))

              r3 = isAbsNotSetInPassInt(someFreeEli3) * absEliScore.get(toAbsEli(someFreeEli3))

              r4 = isAbsNotSetInPassInt(someFreeEli4) * absEliScore.get(toAbsEli(someFreeEli4))

              if (r1 != 0f && r1 > r2 && r1 > r3 && r1 > r4) return someFreeEli1
              if (r2 != 0f && r2 > r1 && r2 > r3 && r2 > r4) return someFreeEli2
              if (r4 != 0f && r3 > r1 && r3 > r2 && r3 > r4) return someFreeEli3
              if (r1 != 0f && r4 > r1 && r4 > r2 && r4 > r3) return someFreeEli4

              val freeEli = findFreeVarInElisArranged(useActivities = freeEliSearchApproach != 9)

              if (freeEli != -1) {

                return freeEli

              }

            } else if (freeEliSearchApproach == 11) {

              while (!unassignedAbsElisQueue.isEmpty) {

                val pe = unassignedAbsElisQueue.dequeueInt()

                if (isNotAbsSetInPass(pe)) {

                  return literally(pe)

                }

              }

            } else if (freeEliSearchApproach3or10) {

              if (!useScoresInFreeEliSearch || useEliScoresAsOrderForAbsEliPool) {

                if (!unassignedAbsElisPool.isEmpty) {

                  val eliCand = (
                    if (unassignedAbsElisPool.get(unassignedAbsElisPool.firstIntKey))
                      unassignedAbsElisPool.firstIntKey
                    else
                      negatePosEli(unassignedAbsElisPool.firstIntKey)
                    )

                  // doesn't necessarily hold in case we've used a tree order which changes after inserting a node (because then we cannot reliably
                  // remove keys from tree anymore): assert(isNotAbsSetInPass(x))

                  if (isNotAbsSetInPass(eliCand)) // see above
                    return literally(eliCand)

                }

              } else {

                var freeEli = -1

                var freeVarActiv = -Float.MaxValue // NB: -Float.MaxValue in Scala (but not Java) is same as Float.MinValue

                if (useUnassignedAbsElisPoolCache) {

                  if (unassignedAbsElisPoolCacheDirty) {

                    unassignedAbsElisPoolCache = unassignedAbsElisPool.keySet.toIntArray

                    unassignedAbsElisPoolCacheDirty = false

                  }

                  var i = 0

                  while (i < unassignedAbsElisPoolCache.length) {

                    val absEliCand = unassignedAbsElisPoolCache(i)

                    if (absEliScore.get(absEliCand) > freeVarActiv && isNotAbsSetInPass(absEliCand)) { // we need the isNotAbsSet check because the cache is not always up-to-date

                      freeVarActiv = absEliScore.get(absEliCand)

                      freeEli = absEliCand

                    }

                    i += 1

                  }

                } else {

                  unassignedAbsElisPool.forEach { case (absEliCand, _) => { // (strangely, this seems to be faster than iterating over the keySet)

                    if (absEliScore.get(absEliCand) > freeVarActiv) {

                      freeVarActiv = absEliScore.get(absEliCand)

                      freeEli = absEliCand

                    }

                  }
                  }

                }

                if (freeEli != -1)
                  return literally(
                    if (unassignedAbsElisPool.get(freeEli))
                      freeEli
                    else
                      negatePosEli(freeEli)
                  )

              }

            } else if (freeEliSearchApproach != 6) {

              val freeEli = findFreeVarInElisArranged(useActivities = useScoresInFreeEliSearch)

              if (freeEli != -1)
                return freeEli

            }

          } else
            rndEveryTrialsIt = rndEveryTrials

          do {

            val freeEliCand = rngLocalL.nextPosInt() / med //rngLocalL.nextEli()

            if (isNotAbsSetInPass(freeEliCand))
              return literally(freeEliCand)

          } while (true)

          Int.MaxValue

        }

        var burstsBeforeConflictsRatios: Double = 0d

        var burstsBeforeConflictsRatiosN = 0

        val forceElisArray = if (forceElis.isInstanceOf[ForceElisArraySet]) forceElis.asInstanceOf[ForceElisArraySet] else null

        @inline def updateburstsBeforeConflictsRatios(burstCountInitial: Int, burstIndex: Long): Unit = {

          val x = (burstCountInitial - ((/*burstCount*/ burstIndex >> 2) + 1)) / burstCountInitial.toDouble

          burstsBeforeConflictsRatios = (x + burstsBeforeConflictsRatiosN * burstsBeforeConflictsRatios) / (burstsBeforeConflictsRatiosN + 1d)

          burstsBeforeConflictsRatiosN += 1

        }

        def unitPropsHeap(burstCountInitial: Int): Unit = { // Boolean Constraint Propagation (BCP)

          if (!useBurstableForceElis) {

            while (forceElis.hasMore) {

              val eli = forceElis.getNext

              if (setInPassIfUnassigned(eli)) {

                var j = eliToRemainders(eli).size() - 1

                //var prop = propagate(eliToRemainders(eli).get(j).nogi)

                while (j >= 0) {

                  val htIndic = eliToRemainders(eli).get(j).setItemIndic(eli)

                  if (htIndic == -1) {

                    if (conflictNogi == -1)
                      conflictNogi = eliToRemainders(eli).get(j).nogi

                    if (!useCounters)
                      return
                    else
                      forceElis.reset

                  } else if (htIndic != Int.MaxValue && conflictNogi == -1 && /*prop*/ propagate(eliToRemainders(eli).get(j).nogi)) // TODO: more experiments needed to determine optimal prop criterion
                    forceElis.addv(negateEli(htIndic))

                  j -= 1

                }

              }

            }

          } else {

            assert(forceElis.isInstanceOf[ForceElisArraySet])

            var burstCountAddr = forceElisArray.addr + (burstCountInitial << 2)

            val oldDl = dl

            while (forceElisArray.hasMore) {

              forceElisArray.addrCounter -= 4

              val eli = unsafe.getInt(forceElisArray.addrCounter)

              if (if (forceElisArray.addrCounter < burstCountAddr) {

                if (isSetInPass(negateEli(eli))) { // we need to reduce maxBurst in that case as otherwise all or many bursted parameter elis would
                  // be invalidated (not set), leading to non-convergence against threshold.
                  // See below why we need to check for isSetInPass(negateEli(eli)) at all.

                  // TODO: this approach to reducing maxBurst is probably not optimal:
                  maxBurst = maxBurst >> 1 //too weak: updateburstsBeforeConflictsRatios(burstCountInitial, burstCountAddr - forceElisArray.addr)

                  jumpBack(oldDl)

                  return

                }

                isNotSetInPass /*isNotAbsSetInPass [see below]*/ (eli) && {
                  // ^ we check for isSetInPass(negateEli(eli)) above or alternatively absSetInPass here instead of just setInPass, because with
                  // bursting of elis, we might not reduce the remainder direclty after setting
                  // the bursted eli, which means there might be some firing event which sets negation(eli) before we set eli, which wouldn't
                  // be allowed.

                  setDecisionLevel(dl + 1)
                  // We need to make sure that each of the "burst" elis and all elis which
                  // are triggered by that respective burst toAbsEli are assigned on a new decision level. The burst
                  // elis are on level 0..burstCount-1 and triggered elis are added at the end (ri.e., forceElisSize++).

                  burstCountAddr = forceElisArray.addrCounter

                  setInPass(eli)

                  true

                }

              } else setInPassIfUnassigned(eli)) {

                var j = 0

                while (j < eliToRemainders(eli).size) {

                  val htIndic = eliToRemainders(eli).get(j).setItemIndic(eli)

                  if (htIndic == -1) {

                    conflictNogi = eliToNogis(eli).buffer.get(j)

                    if (burstCountInitial > 0 && dynamicallyAdaptMaxBurst) { // we keep track of how much bursting triggers conflicts

                      updateburstsBeforeConflictsRatios(burstCountInitial, burstCountAddr - forceElisArray.addr)

                    }

                    return

                  } else if (htIndic != Int.MaxValue) {

                    if (propagate(eliToRemainders(eli).get(j).nogi)) {

                      unsafe.putInt(forceElisArray.addrCounter, negateEli(htIndic))

                      forceElisArray.addrCounter += 4

                    }

                  }

                  j += 1

                }

              }

            }

          }

        }

        var burstCount = 0

        var bi = 0

        if (fireSingletonNogoods) {

          unsat

          return None

        }

        @inline def setPlainElisByBurst = {

          var maxTry = maxBurst //<< 1

          if (noHeap) {

            while (burstCount < maxBurst && maxTry >= 0 && conflictNogi == -1) {

              val candPosEli = rngLocalL.nextPosEli()

              if (isPosEliNotAbsSetInPass(candPosEli)) {

                setDecisionLevel(dl + 1)

                if (passPrevious.getBoolean(candPosEli))
                  setEliWithNogoodUpdatesNoHeap(candPosEli)
                else
                  setEliWithNogoodUpdatesNoHeap(negatePosEli(candPosEli))

                burstCount += 1

                if (conflictNogi != -1 && dynamicallyAdaptMaxBurst) // we keep track of how much bursting triggers conflicts
                  updateburstsBeforeConflictsRatios(maxBurst, burstCount)

              } else
                maxTry -= 1

            }

          } else {

            while (burstCount < maxBurst && maxTry >= 0) {

              val candPosEli = rngLocalL.nextPosEli()

              if (isPosEliNotAbsSetInPass(candPosEli)) {

                if (passPrevious.getBoolean(candPosEli))
                  forceElis.addv(candPosEli)
                else
                  forceElis.addv(negatePosEli(candPosEli))

                burstCount += 1

              } else
                maxTry -= 1

            }

          }

        }

        val noOfPosElisPlus1 = noOfPosElis + 1

        while (incompleteModuloConflict && !stopSolverThreads) { // inner loop of solver ----------------------------
          // Behind this loop, we have a single supported model (as a truth assignments to elis)

          trials += 1

          if (!noHeap) {

            unitPropsHeap(burstCount) // BCP

            forceElis.reset

          }

          if (conflictNogi == -1) {

            incompleteModuloConflict = orderNo != noOfPosElisPlus1

            if (incompleteModuloConflict) {

              // Branching...

              burstCount = 0

              // Parameter literal bursting (optional). Has a more pronounced effect with noHeap = false.
              // Notice the similar effect of uncertainEliSearchStart.

              if (noHeap) {

                if (!ignoreParamVariables) {

                  bi = uncertainEliSearchStart

                  while (bi < deficitOrderedUncertainLiteralsHalf && burstCount < maxBurst && conflictNogi == -1) {

                    val uncertainEli = deficitOrderedUncertainLiteralsForJava(bi)

                    if (isNotAbsSetInPass(uncertainEli)) {

                      uncertainEliSearchStart = if (bi + 1 >= deficitOrderedUncertainLiteralsHalf) 0 else bi + 1

                      setDecisionLevel(dl + 1)

                      setEliWithNogoodUpdatesNoHeap(uncertainEli)

                      burstCount += 1

                    }

                    bi += 1

                  }

                }

                if (burstPlainElis)
                  setPlainElisByBurst

              } else {

                if (!ignoreParamVariables) {

                  bi = uncertainEliSearchStart

                  while (bi < deficitOrderedUncertainLiteralsHalf && burstCount < maxBurst) {

                    val uncertainEli = deficitOrderedUncertainLiteralsForJava(bi).toInt

                    if (isNotAbsSetInPass(uncertainEli)) {

                      uncertainEliSearchStart = if (bi + 1 >= deficitOrderedUncertainLiteralsHalf) 0 else bi + 1

                      forceElis.addv(uncertainEli)

                      burstCount += 1

                    }

                    bi += 1

                  }

                }

                if (burstPlainElis) {

                  bi = 0

                  while (burstCount < maxBurst && bi < noOfPosElis) {

                    if (isPosEliNotAbsSetInPass(bi)) {

                      forceElis.addv(bi)

                      burstCount += 1

                    }

                    bi += 1

                  }

                }

              }

              progressCheckEveryTrialsState -= 1 // (before full compilation checking this is faster than trials % ... == 0)

              val freeEliW = if (burstCount > 0) Int.MaxValue else findFreeEli // invokes branching heuristics or finds free parameter literal using differentiation

              if (freeEliW != Int.MaxValue) {

                val branchingEli: Eli = if (freeEliW < 0)
                  -freeEliW - 1
                else {

                  // we end up here if freeEliW is abs-unassigned without preference for any polarity

                  if (passPrevious != null) {

                    if (isPosEli(freeEliW)) {

                      if (passPrevious.get(freeEliW) == 0x00.toByte)
                        negatePosEli(freeEliW)
                      else
                        freeEliW

                    } else {

                      if (passPrevious.get(negateNegEli(freeEliW)) == 0xFF.toByte)
                        negateNegEli(freeEliW)
                      else
                        freeEliW

                    }

                  } else {

                    if (nextFloatRngLocal() <= 0.5f /* rngLocal.nextBoolean() <- inaccurate */ )
                      freeEliW
                    else
                      negateEli(freeEliW)

                  }

                }

                setDecisionLevel(dl + 1)

                assert(isNotAbsSetInPass(branchingEli))

                if (noHeap)
                  setEliWithNogoodUpdatesNoHeap(branchingEli)
                else
                  forceElis.addv(branchingEli)

                if (progressCheckEveryTrialsState == 0) {

                  progressCheckEveryTrialsState = progressCheckEveryTrials

                  threadChangeCheckFreqState -= 1

                  if (abandonOrSwitchSlowThreads != 0 && threadChangeCheckFreqState == 0) {

                    threadChangeCheckFreqState = threadChangeCheckFreq

                    if (abandonOrSwitchSlowThreads > 0) { // we sample and average progress

                      val norm = (if (threadmxBean.isCurrentThreadCpuTimeSupported) threadmxBean.getCurrentThreadCpuTime() / 10000000 else trials).toDouble

                      val normalizedProgress = orderNo.toDouble / norm.toDouble

                      val n = trials.toDouble / (noOfPosElis / Math.abs(abandonOrSwitchSlowThreads * 100)).toDouble

                      avgNormProgress = (normalizedProgress + n * avgNormProgress) / (n + 1) // cumulative moving average

                    }

                    val stagn = trialsSinceLastProgress / progressCheckEveryTrials.toDouble / 100d

                    lazy val remainingSolverThreads: collection.Set[Int] = progressNormalizedPerThread.keySet

                    val abCrit2 = (abandonOrSwitchSlowThreads < 0 || maxCompetingSolverThreads == 1) &&
                      maxApproachSwitches > 0 &&
                      stagn > (if (abandonOrSwitchSlowThreads > 0) 0.1 else -(abandonOrSwitchSlowThreads - Math.ceil(abandonOrSwitchSlowThreads)))


                    val abCrit1 = abandonOrSwitchSlowThreads > 0 && !abCrit2 && maxCompetingSolverThreads > 1 &&
                      avgNormProgress > 0 && {

                      progressNormalizedPerThread.synchronized {

                        remainingSolverThreads.size >= 2 && {

                          progressNormalizedPerThread.put(threadNo, new SolverThreadInfo(progressNormalizedPerThread.get(threadNo).get.thread, avgNormProgress))

                          lazy val avgNormProgressAllThreads = remainingSolverThreads.map(progressNormalizedPerThread.get(_).get.progressNormalized).sum /
                            remainingSolverThreads.size.toDouble

                          //println("normalized progress for thread " + threadNo + " = " + avgNormProgress + ", avg: " + avgNormProgressAllThreads)

                          avgNormProgressAllThreads > avgNormProgress

                        }

                      }

                    }

                    if (abCrit2 || abCrit1) {

                      val identicalApproaches = false && (maxCompetingSolverThreads == 1 || threadConfs.map(conf => conf.freeEliSearchApproach).distinct.length == 1
                        /*^ deactivated; even if all approaches are the same, switching the "slowest" to a different approach can make sense. */)

                      if (slowThreadAction != 3 || identicalApproaches) {

                        progressNormalizedPerThread.synchronized {

                          if (slowThreadAction == 0 && remainingSolverThreads.size >= 2) {

                            progressNormalizedPerThread.remove(threadNo)

                            if (verbose && showProgressStats) {

                              println("\n>> >> >> Abandoning solver thread $" + threadNo + " after " + trials + " trials")

                              println("   Current #threads total: " + (java.lang.Thread.activeCount))

                              return null

                            }

                          } else {

                            val newPriority: Int = if (slowThreadAction == 2) (Thread.currentThread().getPriority + 1).min(Thread.MAX_PRIORITY) else (Thread.currentThread().getPriority() - 1).max(Thread.MIN_PRIORITY)

                            if (newPriority != Thread.currentThread().getPriority()) {

                              if (verbose)
                                println("\nChanging priority of thread $" + threadNo + " after " + trials + " trials\n from " + Thread.currentThread().getPriority() + " to " + newPriority)

                              Thread.currentThread().setPriority(newPriority)

                            } else {

                              if (verbose)
                                println("\n" + (if (slowThreadAction == 2) "Decreasing" else "Increasing") + " priorities of threads other than thread $" + threadNo + " after " + trials + " trials")

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

                      } else if (!identicalApproaches) {

                        maxApproachSwitches -= 1

                        val newApproach = freeEliSearchConfigsP((freeEliSearchConfigsP.indexOf(freeEliSearchApproach) + 1) % freeEliSearchConfigsP.length)

                        if (verbose && showProgressStats)
                          println("\n>> >> >> Switching solver thread $" + threadNo + " to decision heuristics " + newApproach + "... (after " + trials + " trials)")

                        freeEliSearchApproach = newApproach

                        threadConfs(threadNo - 1).freeEliSearchApproach = newApproach

                        freeEliSearchApproach4or1or5or9 = freeEliSearchApproach == 1 || freeEliSearchApproach == 5 || freeEliSearchApproach == 4 || freeEliSearchApproach == 9

                        freeEliSearchApproach3or10 = freeEliSearchApproach == 3 || freeEliSearchApproach == 10

                      }

                    }

                  }

                  progressCheckEveryTrialsState = progressCheckEveryTrials

                  // We adapt the burst rate, depending on how quick bursted elis lead to a conflict (ri.e., indirectly how independent parameter variables are from each other):
                  if (dynamicallyAdaptMaxBurst && burstsBeforeConflictsRatios > 0d) {

                    // The larger burstsBeforeConflictsRatios is, the larger maxBurst can be:

                    val oldMaxBurst = maxBurst

                    maxBurst = (maxBurst * (burstsBeforeConflictsRatios / 2 + maxBurstAdaptOffset)).toInt // we can use the offset to ensure that
                    // maxBurst can grow

                    if (maxBurst <= 1) {

                      burstPlainElis = false

                      maxBurst = 0

                      dynamicallyAdaptMaxBurst = false

                    }

                    println("\n\nnew maxBurst: " + maxBurst + "  [old: " + oldMaxBurst)

                    burstsBeforeConflictsRatiosN = 0

                  }

                  if (noOfPosElis - orderNo < prevUnassi) {

                    prevUnassi = noOfPosElis - orderNo

                    if (abandonOrSwitchSlowThreads != 0) {

                      trialsSinceLastProgress = trials - trialsAtLastImprovement

                      trialsAtLastImprovement = trials

                    }

                    if (showProgressStats && trials % (progressCheckEveryTrials * 10) == 0) {

                      val peak = ((noOfPosElis - prevUnassi).toDouble / noOfPosElis.toDouble * 100).toInt

                      if (singleLineProgress) {

                        printSingleLineProgress(peak, trials)

                      } else {

                        println("\n##### Assigned (peak, all threads): " + peak + "%  @ " + timerToElapsedMs(solverTimer) / 1000 + " sec")

                        println("  remaining unassigned atoms thread $" + threadNo + ": ca. " + prevUnassi + ", conflictNogi: " + conflictNogi)
                        // note that prevUnassi <= 0 doesn't mean we are finished since conflictNogi might be != -1

                        println("  conflicts after restart: thread $" + threadNo + ": " + noOfConflictsAfterRestart)

                        println("  Learned nogoods: " + (nogiToRemainder.size - firstRecordedNogi))

                        //println("  Time since last progress: " + timeSinceLastProgressNs + " ms")

                      }

                    }

                  } else if (showProgressStats && trials % (progressCheckEveryTrials * 3) == 0) {

                    printSingleLineProgress(peak = ((noOfPosElis - prevUnassi).toDouble / noOfPosElis.toDouble * 100).toInt, trials)

                  }

                }

              }

            }

          } else {

            if (dl == 0) {

              unsat

              return None

            }

            if (noOfConflictsAfterRestart >= noOfConflictsBeforeRestart) { // Restart

              if (showProgressStats) {

                if (singleLineProgress) {

                  printSingleLineProgress(peak = ((noOfPosElis - prevUnassi).toDouble / noOfPosElis.toDouble * 100).toInt, trials)

                } else {

                  println("Restarting... (Thread: " + threadNo + "$, #conflicts: " + noOfConflictsTotal +
                    ", #restarts: " + noOfRestarts + " @ " + timerToElapsedMs(solverTimer) / 1000 + " sec, " +
                    //"rndmBranch = " + rndmBranch +
                    //", savePhases = " + savePhases +
                    //", maxBurst = " + maxBurst +
                    //", absEliScoreFact = " + absEliScoreFact +
                    //", rndmIgnLearnedNogoodThreshold = " + rndmIgnLearnedNogoodThresholdP +
                    ", thread time: " + (if (threadmxBean.isCurrentThreadCpuTimeSupported) (threadmxBean.getCurrentThreadCpuTime / 1e9).toInt + "sec" else "??") + ")")

                }

              }

              noOfRestarts += 1

              noOfTrialsAtLastRestart = trials

              if (rearrangeEliPoolOnRestart) {

                if (elisArranged != null)
                  shuffleArrayUnsafe(elisArranged, rngLocal)

                if (unassignedAbsElisPool != null)
                  rearrangeUnassignedAbsElisPool

              }

              if (restartTriggerConf._1 == 2)
                noOfConflictsBeforeRestart *= restartTriggerConf._3
              else {

                val bsr = java.util.Arrays.binarySearch(l2km1ForLuby, noOfRestarts + 1)

                val k = if (bsr >= 0) bsr + 1 else -(bsr + 1) + 1

                lubySeq.append(if (bsr >= 0)
                  1 << (k - 1)
                else
                  lubySeq(noOfRestarts + 1 - (1 << (k - 1)) + 1))

                noOfConflictsBeforeRestart = lubySeq(noOfRestarts + 1) * restartTriggerConf._3

              }

              if (nogoodShareProbability > 0f && maxCompetingSolverThreads > 1 && !stopSolverThreads) {

                nogoodExchangePool.synchronized {

                  // TODO: in rare cases there is still toAbsEli race related to nogood exchange - fix without introducing locking in remainder updates or BCP

                  import scala.collection.JavaConverters._
                  val moveoverNogoods = nogoodExchangePool.entrySet().asScala.filter((value: Map.Entry[IntArrayUnsafeS, Int]) => {

                    nextFloatRngLocal() <= nogoodShareProbability && value.getValue != threadNo && value.getKey.size() < nogoodShareSizeThresh

                  })

                  if (moveoverNogoods.size > 0) {

                    log("  This thread: $" + threadNo + ", fetching " + moveoverNogoods.size + " nogoods from other threads...")

                    moveoverNogoods.foreach { case (value: Map.Entry[IntArrayUnsafeS, Int]) => {

                      nogoodExchangePool.remove(value.getKey)

                      addNogood(value.getKey)

                    }

                    }

                  }

                }

              }

              val jbt = if (levelledRestarts) rngLocalL.nextTriangular(xForLevelledRestarts, dl, xForLevelledRestarts).toInt.max(-1) else -1

              jumpBack(jbt)

              if (unassignedAbsElisQueue != null)
                unassignedAbsElisQueue.changed()

            }

          }

          if (conflictNogi != -1) { // Conflict handling

            uncertainEliSearchStart = 0

            incompleteModuloConflict = true

            if (dl == 0) {

              unsat

              return None

            }

            val (newLevel: Int, newNogood: IntArrayUnsafeS, sigma: Eli) = conflictAnalysis(conflictNogi)

            if (useScoresInFreeEliSearch && noOfConflictsAfterRestart % reviseScoreFreq == 0) {

              var absEliAddr = absEliScore.addr

              val absEliAddrMax = absEliAddr + (noOfPosElis << 2)

              var activSum = 0d

              while (absEliAddr < absEliAddrMax) {

                unsafe.putFloat(absEliAddr, unsafe.getFloat(absEliAddr) * reviseScoreFact)

                activSum += unsafe.getFloat(absEliAddr)

                absEliAddr += 4

              }

              //println("activSum = " + activSum)

              if (activSum == 0f || activSum.isInfinite || activSum.isNaN || activSum <= 1E-30d) {

                if (verbose && !warnMessageEliScoreOutOfRangeShown) {

                  stomp(-5010, "activSum: " + activSum + ", eliScoreUpdateFact = " + eliScoreUpdateFact + "; thread: $" + threadNo)

                  warnMessageEliScoreOutOfRangeShown = true

                }

                if (activSum == 0f)
                  eliScoreUpdateFact *= scaleScoreUpdateFactOutOfRange
                else if (activSum.isInfinite)
                  eliScoreUpdateFact /= scaleScoreUpdateFactOutOfRange

                resetAbsEliActi(clearUnassignedPool = true)

              }

            }

            val newNogi = addNogood(newNogood)

            jumpBack(newLevel)

            assert(nogiToRemainder.get(newNogi).notsetCounter > 0)

            if (noHeap)
              setEliWithNogoodUpdatesNoHeap(negateEli(sigma))
            else
              forceElis.addv(negateEli(sigma))

          }

        } // -------------------------------------------------------------------------------------------------------------

        if (!stopSolverThreads) {

          log("\nEnd of inner loop reached! SolverTimer end: " + timerToElapsedMs(solverTimer) + " ms\n")

          assert(orderNo - 1 == noOfAllElis / 2)

          val modelCandidate: (Array[Eli], IntOpenHashSet) = { // we don't just return an array here but also a hash set, since we might use the result as a cache key

            import scala.collection.JavaConverters._

            lazy val restoredNogoods: ArrayBuffer[IntArrayUnsafeS] = nogiToNogood.asScala.toArray.to[ArrayBuffer]

            removedNogoodsPerAtomOpt.foreach { removedNogoodsPerAtom: mutable.TreeMap[Eli /*atom*/ , ArrayBuffer[IntArrayUnsafeS]] => {
              // we've performed variable elimination in class Preparation and need to restore
              // now the removed variables (atoms) with their correct polarities:satmo

              val removedNogoodsPerAtomArray = removedNogoodsPerAtom.toArray

              removedNogoodsPerAtomArray.foreach { case (atom: Eli, _) => {

                clearInPass(atom)

                clearInPass(negatePosEli(atom))

              }
              }

              removedNogoodsPerAtomArray.reverse.foreach { case (atom: Eli, removedNogoods: ArrayBuffer[IntArrayUnsafeS]) => {

                restoredNogoods.appendAll(removedNogoods)

                setInPass(atom)

                val isAtomPos = restoredNogoods.forall((nogood: IntArrayUnsafeS) => {

                  nogood.toArray.exists(!isSetInPass(_)) // TODO: optimize restoredNogoods handling

                })

                if (!isAtomPos) {

                  clearInPass(atom)

                  setInPass(negatePosEli(atom))

                }

                log(" ok restored eliminated positive toAbsEli " + atom)

              }
              }

            }

            }

            val modelCand = new it.unimi.dsi.fastutil.ints.IntArrayList(noOfPosElis)

            var mci: Eli = 0

            while (mci < noOfPosAtomElis) { // the atom elis in the model candidate must be in increasing numerical order
              // (as we use toAbsEli subset of toAbsEli bounced model directly as toAbsEli cache key)

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

            def sanityChecks = { // we perform a few simple tests with the discovered model. Not a correctness proof - for debugging purposes only.

              // TODO: due to incomplete locking (takes some time to propagate stopSolverThreads), we occasionally end up here >= twice

              stopSolverThreads = true

              println("\n\nPerforming informal sanity checks on resulting model candidate... (free eli search approach was: " + freeEliSearchApproach + ")\n")

              if (!satMode) {

                val r = checkASPWithEliRules(modelCandidate, rulesOpt.get)

                if (!r._1) {

                  println("Answer set check fail!") // indicates that tightness recognition gave wrong result, as otherwise the model would have
                  // been bounced back

                  sys.exit(-1)

                } else
                  println("Answer set check OK")

              }

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

              dimacsDirectClauseNogoodsOpt.foreach((directDIMACSClauseNogoods: Array[IntArrayUnsafeS]) => {

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

              // NB: There is a further (and for satMode/DIMACS the most important) informal enforceSanityChecks check in delSAT.scala

              if (!allElitsCovered || !noInconsistencies || violatedNogoods > 0 || violatedDNogoods > 0) {

                println("\n\\/\\/\\/\\/ Internal error: Initial sanity checks failed on model candidate!\n")

                sys.exit(-5)

              }

            }

            //log("pass:\n " + pass.mkString(","))

            if (enforceSanityChecks || debug)
              sanityChecks

            if (satMode) log("+++ ++ + Found toAbsEli satisfying assignment") else log("*** ** * Found an answer set ")

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
            // for the latter (not the earlier version of this paper). But in contrast to ASSAT, we use regular CDNL conflict handling on loop nogood violations.

            val mMinusR = checkResult._2

            val loopsOverMminus: mutable.Seq[ArrayBuffer[Eli]] = {

              sccCache.getOrElseUpdate(mMinusR, {

                val t = {

                  val tR = new Int2ObjectOpenHashMap[List[Eli]]() // this is ugly, but Java's HashMaps are in this case faster than Scala's (as of 2.12)

                  /*
                  val dgEntries = positiveDependencyGraph.entrySet.iterator

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

                val tKeys: IntSet = t.keySet()

                val tKeysIterator = t.keySet().iterator()

                val dependencyGraphInducedByMminus = new Int2ObjectOpenHashMap[List[Eli]]()

                while (tKeysIterator.hasNext()) {

                  val key = tKeysIterator.nextInt()

                  dependencyGraphInducedByMminus.put(key, t.get(key).filter((eli: Eli) => {

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

                val newLoopNogoodUnsafe = new IntArrayUnsafeS(newLoopNogood.size, aligned = false)

                newLoopNogoodUnsafe.setFromIntArray(newLoopNogood.toArray)

                log("Adding loop nogood: " + newLoopNogoodUnsafe)

                addNogood(newLoopNogoodUnsafe)

                if (emitClauses)
                  loopNogoods.add(newLoopNogoodUnsafe)

                noOfGenLoopNogoods += 1

                j += 1

              }

              i += 1

            }

            log("Restarting after addition of " + noOfGenLoopNogoods + " loop nogoods...\n")

            jumpBack(-1)

          }

        }

      }

      // End bounce back loop for generating a single answer set or SAT model

      if (verbose) {

        if (stopSolverThreads)
          println("\nSingle model solving time (thread $" + threadNo + "): " + timerToElapsedMs(solverTimer) + " ms (discarded) ")
        else
          println("\n***** Single model solving time (thread $" + threadNo + "): " + timerToElapsedMs(solverTimer) + " ms")

      }

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

          println("p cnf " + noOfPosElis + " " + (clarkNogoods.length + loopNogoods.size))

          clarkNogoods.foreach((nogood: IntArrayUnsafeS) => printClause(nogood))

          loopNogoods.forEach((nogood: IntArrayUnsafeS) => printClause(nogood))

          println

        }

      }

      modelOpt

    }

    assert(dimacsClauseNogoodsOpt.isDefined || rulesOpt.isDefined)

    if (verbose) {

      println("#symbols (variables): " + symbols.length)

      println("#literals (including body literals): " + noOfAllElis)

      println("#initial nogoods = " + clarkNogoods.length)

      println("#Parameter atoms: " + parameterAtomsElis.length)

      println

    }

    nogoodExchangePool.clear()

    prevUnassi = Int.MaxValue // not precise even for single solver thread. For statistics/debugging purposes only!

    stopSolverThreads = false

    val r: Option[(Array[Eli], IntOpenHashSet)] = if (maxCompetingSolverThreads == 1) {

      val freeEliSearchApproach = freeEliSearchConfigsP(0)

      val singleSolverConf = SingleSolverConf(threadNo = 1,
        dependencyGraph = positiveDependencyGraph,
        progIsTight = progIsTight,
        freeEliSearchApproach = freeEliSearchApproach,
        restartTriggerConfR = (restartTriggerConfP._1, restartTriggerConfP._2.head, restartTriggerConfP._3.head),
        arrangeEliPoolR = arrangeEliPoolP.head,
        noHeapR = noHeapP.head,
        absEliScoreFact = absEliScoreFactP.head,
        rndmIgnLearnedNogoodThresholdR = rndmIgnLearnedNogoodThresholdP.head,
        prep = prep /*<-for debugging/crosschecks only*/ ,
        seed = seedP.head,
        rndmBranchR = rndmBranchP.head)

      threadConfs(0) = singleSolverConf

      if (verbose)
        println("Single solver thread:\n  freeEliSearchApproach: " + singleSolverConf.freeEliSearchApproach +
          "\n  arrangeEliPoolR: " + singleSolverConf.arrangeEliPoolR +
          "\n  rndmBranchR: " + singleSolverConf.rndmBranchR +
          "\n  restartTriggerConfR._2: " + singleSolverConf.restartTriggerConfR._2 +
          "\n  restartTriggerConfR._3: " + singleSolverConf.restartTriggerConfR._3 +
          //"\n  absEliScoreFact: " + singleSolverConf.absEliScoreFact +
          "\n  rndmIgnLearnedNogoodThreshold: " + singleSolverConf.rndmIgnLearnedNogoodThresholdR +
          "\n  noHeapR: " + singleSolverConf.noHeapR + "\n")

      val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(singleSolverConf)

      log("\nSolver task complete\n")

      modelOpt

    } else {

      uncertainAtomsUpdateExecutorService.purge()

      @volatile var firstModelOpt = null.asInstanceOf[Option[(Array[Eli], IntOpenHashSet)]]

      val paramCombs = (for (freeEliSearchApproachR <- freeEliSearchConfigsP;
                             prearrangeEliPoolR <- arrangeEliPoolP;
                             rndmBranchR <- rndmBranchP;
                             restartTriggerConf2 <- restartTriggerConfP._2;
                             restartTriggerConf3 <- restartTriggerConfP._3;
                             absEliActivFact <- absEliScoreFactP;
                             rndmIgnLearnedNogoodThreshold <- rndmIgnLearnedNogoodThresholdP;
                             noHeapR <- noHeapP;
                             seed <- seedP)
        yield (freeEliSearchApproachR, prearrangeEliPoolR, rndmBranchR, restartTriggerConf2, restartTriggerConf3, absEliActivFact, rndmIgnLearnedNogoodThreshold, noHeapR, seed))

      // Remark: we are not using a global thread pool here anymore, since by default we switch to the fastest configuration and a single solver thread
      // after the first round and the overhead was not justified anymore.

      val callables = (1 to maxCompetingSolverThreads).map(ci => new Runnable {
        override def run() = {

          val (freeEliSearchApproachR: Int,
          prearrangeEliPoolR: Int,
          rndmBranchR: Double,
          restartTriggerConf2: Int,
          restartTriggerConf3: Double,
          absEliActivFact: Float,
          rndmIgnLearnedNogoodThreshold: Float,
          noHeapR: Int, seed: Long) = if (maxCompetingSolverThreads == 1) paramCombs.head else
            paramCombs((ci - 1) % maxCompetingSolverThreads.min(paramCombs.length))

          val singleSolverConf = SingleSolverConf(threadNo = ci,
            //costsOpt = costsOpt,
            dependencyGraph = positiveDependencyGraph,
            progIsTight = progIsTight,
            freeEliSearchApproach = freeEliSearchApproachR,
            arrangeEliPoolR = prearrangeEliPoolR,
            restartTriggerConfR = (restartTriggerConfP._1, restartTriggerConf2, restartTriggerConf3),
            absEliScoreFact = absEliActivFact,
            rndmIgnLearnedNogoodThresholdR = rndmIgnLearnedNogoodThreshold,
            noHeapR = noHeapR,
            prep = prep /*<-for debugging/crosschecks only*/ ,
            seed = seed,
            rndmBranchR = rndmBranchR)

          threadConfs(ci - 1) = singleSolverConf

          if (verbose)
            println("Starting solver thread $" + ci + ":\n  freeEliSearchApproachR: " + freeEliSearchApproachR +
              "\n  arrangeEliPoolR: " + singleSolverConf.arrangeEliPoolR +
              "\n  rndmBranchR: " + singleSolverConf.rndmBranchR +
              "\n  restartTriggerConfR._2: " + singleSolverConf.restartTriggerConfR._2 +
              "\n  restartTriggerConfR._3: " + singleSolverConf.restartTriggerConfR._3 +
              //"\n  absEliScoreFact: " + singleSolverConf.absEliScoreFact +
              "\n  rndmIgnLearnedNogoodThreshold: " + singleSolverConf.rndmIgnLearnedNogoodThresholdR +
              "\n  noHeapR: " + singleSolverConf.noHeapR + "\n")

          val modelOpt: Option[(Array[Eli], IntOpenHashSet)] = sampleSingle(singleSolverConf)

          if (modelOpt != null) {

            stopSolverThreads.synchronized {

              if (!stopSolverThreads) {

                if (verbose)
                  println("Successful portfolio thread: $" + ci)

                if (sampledModels.size == 0 /*<- if > 0, we would switch after the nth model this way, to minimize influence from JVM hotspot compilation */ &&
                  switchToBestConfigAfterFirstModel > 0) { // we switch to a singleton portfolio, but we could theoretically also switch to some other subset:

                  freeEliSearchConfigsP = freeEliSearchConfigsP.map(_ => freeEliSearchApproachR)

                  arrangeEliPoolP = arrangeEliPoolP.map(_ => prearrangeEliPoolR)

                  rndmIgnLearnedNogoodThresholdP = rndmIgnLearnedNogoodThresholdP.map(_ => rndmIgnLearnedNogoodThreshold)

                  absEliScoreFactP = absEliScoreFactP.map(_ => absEliActivFact)

                  noHeapP = noHeapP.map(_ => noHeapR)

                  seedP = seedP.map(_ => seed)

                  restartTriggerConfP = (restartTriggerConfP._1, restartTriggerConfP._2, restartTriggerConfP._3.map(_ => restartTriggerConf3))

                  if (verbose)
                    println("\nFor additional models, switching to portfolio set\n freeEliSearchConfigsP: " + freeEliSearchConfigsP +
                      "\n  arrangeEliPoolP: " + arrangeEliPoolP +
                      "\n  rndmIgnLearnedNogoodThreshold: " + rndmIgnLearnedNogoodThreshold +
                      //"\n  absEliScoreFactP: " + absEliScoreFactP +
                      "\n  restartTriggerConfP._2: " + restartTriggerConfP._2 +
                      "\n  restartTriggerConfP._3: " + restartTriggerConfP._3 +
                      "\n  seed: " + seed +
                      "\n  rndmBranchR: " + rndmBranchR +
                      "\n  noHeapP: " + noHeapP)

                  if (switchToBestConfigAfterFirstModel == 2)
                    maxCompetingSolverThreads = 1

                }

                stopSolverThreads = true

              }

            }

            firstModelOpt = modelOpt

          }

        }
      })

      val solverThreads = callables.map(c => {

        val t = new Thread(c)

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
