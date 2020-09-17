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

package input

import aspIOutils.Pred
import diff.UncertainAtomsSeprt
import input.AspifPlainParser.{AspifEli, AspifRule}
import sharedDefs.{Eli, Rule}
import utils.IntArrayUnsafeS

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** Result of the aspif or dimacs parser. Also see [[input.InputData]] */
final case class AspifOrDIMACSPlainParserResult(symbols: Array[String],
                                                rulesOrClauseNogoods: Either[
                                                  /*from aspif:*/ ArrayBuffer[Rule],
                                                  /*from DIMACS:*/ Array[IntArrayUnsafeS]],
                                                noOfPosBlits: Int,
                                                noOfDummySymbols: Int,
                                                externalAtomElis: Seq[Eli], // for aspif. TODO: #external not implemented yet
                                                assumptionElis: Seq[Eli], // filtering assumptions
                                                emptyBodyBlit: Int = -1,
                                                clausesForChecksOpt: Option[Array[Array[Int]]],
                                                symbolToEliOpt: Option[Predef.Map[String, Eli]],
                                                additionalUncertainAtomsInnerCostsStrs: (Array[String], Array[String], Array[String] /*<-original _eval_ terms*/ ),
                                                // ^ we allow probabilistic parameter atoms to be
                                                // stated as ASP facts too in the aspif, in addition to those provided using "pats" and "cost" lines.
                                                // They are treated as MSE inner cost functions.

                                                // The following elements are useful if the parser result should be extended with further rules, which
                                                // needs to happen on the aspif-eli level, not on the eli-level:
                                                aspifEliToSymbolOpt: Option[mutable.HashMap[AspifEli, Pred]] = None,
                                                aspifRulesOpt: Option[mutable.ArrayBuffer[AspifRule]] = None
                                               )

/** Input data for the sampler/solver */
final case class InputData(aspifOrDIMACSPlainParserResult: AspifOrDIMACSPlainParserResult,
                           costsOpt: Option[UncertainAtomsSeprt])