/**
  * diff-SAT
  *
  * Copyright (c) 2018,2022 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details).
  *
  */

package solving

import java.util.concurrent.ConcurrentHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import sharedDefs._
import utils.{ByteArrayUnsafeS, FiniteQueue}
/*import vmm.API
import vmm.API.VMMType.PPMC
import vmm.algs.PPMCPredictor */

class SharedAmongSingleSolverThreads(noOfAbsElis: Int) {

  var refreshedBestPhasesGlobal: Int = 0

  val bestPhasesQueueGlobal: FiniteQueue[ByteArrayUnsafeS] = if (globalBestPhaseMemo &&
    (weakRephasingAtRestartEveryP.getAllAlternativeValues.find(_ > 0).isDefined || rephasePhaseMemoP.getAllAlternativeValues.contains(true))) // i.e., we are using a global array here. TODO: more tests whether thread-local is mostly better or not
  new FiniteQueue[ByteArrayUnsafeS](scala.collection.mutable.Queue[ByteArrayUnsafeS]())
    else
    null

  var greedilyBestThread: Int = 0

  val fmStackGlobalCapacity: Int = 500000

  val fmStackGlobal: LongArrayList = if (freeOrReassignDeletedNogoodMemory &&
    (freeDeletedNogoodMemoryApproach == 3)) new LongArrayList(fmStackGlobalCapacity)
  else
    null

  val nogoodReducibleExchangePoolSourceThreadsForCyclicSharingPrevention: ConcurrentHashMap[NogoodReducible, Int] = new java.util.concurrent.ConcurrentHashMap[NogoodReducible, Int /*producing thread*/ ]()

  val nogoodReducibleExchangePool: ConcurrentHashMap[NogoodReducible, Int] =
  /*TODO: use of this comes with heavy boxing*/ new java.util.concurrent.ConcurrentHashMap[NogoodReducible, Int /*producing thread*/ ]()

  val scoresFromSLS: ConcurrentHashMap[Eli, Float] = new java.util.concurrent.ConcurrentHashMap[Eli, Float]()

  //var minViolNogoodCountSum = Int.MaxValue

  var threadConfsOpt: Option[Array[SolverThreadSpecificSettings]] = None

}
