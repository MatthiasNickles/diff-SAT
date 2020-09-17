/**
  * delSAT
  *
  * Copyright (c) 2018, 2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package solving

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import sharedDefs.Eli

import scala.collection.mutable

/**
  * The result of a sampler call
  *
  * @param modelsSymbolic Sequence of models represented as arrays of symbolic literals
  * @param modelsUsingElis Sequence of models represented as arrays of elis (literals represented as pos/neg Ints) and hash sets of elis
  * @param samplingDurationNs Sampling duration in nanoseconds
  */
case class SamplingResult(modelsSymbolic: mutable.Seq[Array[String]],
                          modelsUsingElis: mutable.ArrayBuffer[(Array[Eli], IntOpenHashSet)],
                          samplingDurationNs: Long)
