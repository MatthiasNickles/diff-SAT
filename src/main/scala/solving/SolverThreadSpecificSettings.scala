/**
  * diff-SAT
  *
  * Copyright (c) 2018, 2022 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package solving

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap

import sharedDefs.Eli

/** Includes only those settings which can be different across individual solver threads, including
  * all settings whose names end with ...P in sharedDefs.scala */
case class SolverThreadSpecificSettings(var threadNo: Int /*>=1*/ ,
                                        positiveDependencyGraph: Int2ObjectOpenHashMap[List[Eli]], // TODO: move elsewhere
                                        assureProgIsTight: Boolean,
                                        var freeEliSearchApproach: Int,
                                        restartTriggerConfR: (Int, Int, Double),
                                        traverseReduciblesUpwardsInUnitProp: Boolean,
                                        initAbsElisArrangement: Int,
                                        prep: Preparation /*<-for debugging/crosschecks only*/ ,
                                        seed: Long,
                                        restartFrequencyModifierFactorR: Float,
                                        useSLSinPhaseMemoRephasingR: Boolean,
                                        nogoodRemovalThreshRatio: Double,
                                        absEliScoringApproach: Int,
                                        nogoodRemovalThreshInit: Int,
                                        noisePhaseMemoR: Float,
                                        localRestarts: Boolean,
                                        scoringForRemovalOfLearnedNogoodsR: Int,
                                        weakRephasingAtRestartEvery: Int,
                                        rephasePhaseMemo: Boolean,
                                        nogoodBCPtraversalDirection: Int,
                                        absEliScoringApproach15NoOfBins: Int,
                                        var singleSolverThreadDataOpt: Option[SingleSolverThreadData])
