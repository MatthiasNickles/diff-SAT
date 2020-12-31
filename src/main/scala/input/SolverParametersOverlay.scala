/**
  * diff-SAT
  *
  * Copyright (c) 2018,2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package input

import scala.collection.mutable

/**
  * Solver and sampling settings. For advancedSolverArgs and use, see [[sharedDefs]]
  *
  * @param noOfModels           -1: sample until accuracy threshold (thresholdOpt) has been reached
  * @param noOfSecondaryModels  sample n models uniformly from the original sample
  * @param offHeapGarbageCollectionModeR
  * @param thresholdOpt
  * @param assureMSE            guarantees that the cost functions are in MSE form (see README.md), enables certain performance optimizations
  * @param showauxInSATmode
  * @param advancedSolverArgs   See [[sharedDefs]]
  */
case class SolverParametersOverlay(
                                    noOfModels: Int,
                                    noOfSecondaryModels: Int,
                                    offHeapGarbageCollectionModeR: Int,
                                    thresholdOpt: Option[Double],
                                    assureMSE: Boolean,
                                    showauxInSATmode: Boolean, // TODO: this works in SAT mode only
                                    advancedSolverArgs: mutable.HashMap[(String /*param name*/ , Int /*<-thread*/ ), String /*param value*/ ] = mutable.HashMap()

                                  )
