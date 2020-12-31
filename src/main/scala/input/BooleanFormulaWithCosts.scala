/**
  * diff-SAT
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
import diffSAT.invokeSampler
import utils.ArrayValExtensibleIntUnsafe
import solving.SamplingResult
import utils.IntArrayUnsafeS

import scala.collection.mutable.ArrayBuffer


/**
  * A collection of probabilistic and/or non-probabilistic Boolean clauses (disjunctions of literals)
  *
  * User API part for probabilistic SAT solving and multimodel optimization (for the User API part for probabilistic Answer Set
  * Programming see [[input.ProbabilisticAnswerSetProgram]])
  *
  * Example:
  * Construct CNF and specify multimodel optimization goal:
  * {{{

      // The following API calls corresponds to solving the following Enhanced DIMACS CNF file:
      //
      //  1 -1 0
      //  2 -2 0
      //  -1 -2 0
      //
      //  pats 1 2
      //
      //  cost (0.2-f(v1))^2
      //  cost (0.5-f(v2))^2
      //

      val clause1 = BooleanClause(literals = Set(BooleanLiteral(1), BooleanLiteral(-1)))

      val clause2 = BooleanClause(literals = Set(BooleanLiteral(2), BooleanLiteral(-2)))

      val clause3 = BooleanClause(literals = Set(BooleanLiteral(-1), BooleanLiteral(-2)))

      val booleanFormula: BooleanFormulaWithCosts = BooleanFormulaWithCosts(Set(clause1, clause2, clause3))

      val probabilisticObjectives =  // Parameter atoms are "1" and "2". Atom "1" has probability 0.2, "2" has probability 0.5
        """pats 1 2

           cost (0.2-f(v1))^2
           cost (0.5-f(v2))^2
        """
        // (Alternatively, cost (loss) terms can be constructed programmatically (see ParseOptimizationTerms to get an idea how to do
        // this. Also consider using the ASP User API ([[input.ProbabilisticAnswerSetProgram]]) which allows to work
        // with symbolic atoms and rules.)
     }}}
     Invoke sampler and examine the resulting sample (a set of models):
     {{{

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until desired accuracy (thresholdOpt) has been reached. A positive
         // number would specify a minimum sample size (number of answer sets).
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(0.001d), // the desired accuracy (lower = more accurate but sampling requires more time)
        assureMSE = true, // true = the loss function is assured to be of type MSE (false works too but true is more efficient)
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](  // advanced solver parameters (corresponding to --solverarg commandline parameters)
            ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = booleanFormula.solve(solverParams,
        paramAtomsAndInnerCostsStrOpt = Some(probabilisticObjectives))

      // Print sample and the result of ad hoc query Pr[p(a):-not q AND p(b):-not q]:

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults,
      adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = true,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("1"), Seq("2")),
        adHocDisjunctiveQueries = Seq(),
        adHocConjunctionOfSimpleGroundRulesQuery = Seq(),
        printAdHocQueryResults = true,
        printAnswers = true)

      println(adHocConjunctiveQueriesResults)

  }}}
  *
  * Further examples can be found in the source code of [[userAPItests.APITests]]
  *
  * @param clauses
  * @param maxVar : largest (by name) propositional variable. If -1 it will be automatically determined.
  */
case class BooleanFormulaWithCosts(clauses: Set[Clause], var maxVar: Int = -1) {

  val patsFromProbabilisticClauses = ArrayBuffer[Pred]()

  val costsFromProbabilisticClauses = ArrayBuffer[String]() // format of an inner cost term obtained from a probabilistic
  // clause is "(probability-f(vx))^2"

  // We need to know maxVar upfront 1) to fill "gaps" in the enumeration of variables (symbols) and 2) for new variables introduced for extra clauses from probabilistic clauses

  if (maxVar < 0) {

    clauses.foreach {

      case BooleanClause(literals: Set[BooleanLiteral]) =>
        literals.foreach(lit => maxVar = maxVar.max(Math.abs(lit.value)))

      case ProbabilisticBooleanClause(literals: Set[BooleanLiteral], _: Double) =>
        literals.foreach(lit => maxVar = maxVar.max(Math.abs(lit.value)))

    }

  }

  val originalMaxVar = maxVar

  val directClauseNogoods = clauses.flatMap {

    case BooleanClause(literals: Set[BooleanLiteral]) => {

      val arrayUS = new IntArrayUnsafeS(values = literals.map(lit => {

        -lit.value // (-value since diff-SAT internally works with nogoods, not clauses)

      }).toArray)

      Set(arrayUS)

    }

    case ProbabilisticBooleanClause(literals: Set[BooleanLiteral], probability: Double) => {

      maxVar += 1

      val llc = new ArrayValExtensibleIntUnsafe(buffer = new IntArrayUnsafeS(1024))

      llc.append(0) // placeholder required in createExtraClausesNogoodsFromProbabilisticClauseNogood()

      literals.foreach(literal => llc.append(-literal.value))

      patsFromProbabilisticClauses.append(maxVar.toString) // the parameter variables (which in this case are also measured variables)

      val (extraClauseA: ArrayValExtensibleIntUnsafe, extraClausesB: Array[ArrayValExtensibleIntUnsafe],
      costTermForProbClause: String) =
        DIMACPlainSparser.createExtraClausesNogoodsFromProbabilisticClauseNogood(llc,
          clauseHandleVar = maxVar,
          weightStr = probability.toString)

      costsFromProbabilisticClauses.append(costTermForProbClause)

      Set(extraClauseA.getContentUnsafe) ++ extraClausesB.map(_.getContentUnsafe)

    }

  }.toArray

  println("Auxiliary Boolean variables introduced for PCNF: " + (originalMaxVar to maxVar).mkString(","))

  /**
    * Calls the sampler for this propositional formula. Optionally with additional multimodel cost terms (in addition
    * to those generated from any probabilistic clauses)
    *
    * @param solverParametersOverlay
    * @param paramAtomsAndInnerCostsStrOpt An optional string with a specification of parameter atoms and cost terms
    *                                      (see README.md). These costs are in addition to those specified indirectly using
    *                                      probabilistic clauses.
    * @return SamplingResult               The list of models is in SamplingResult.modelsSymbolic. Since sampling
    *         is with replacement, the list represents a multiset of models.
    */
  def solve(solverParametersOverlay: SolverParametersOverlay,
            paramAtomsAndInnerCostsStrOpt: Option[String] = None): SamplingResult = {

    val symbolsArray = (1 to maxVar).map(_.toString).toArray

    //println(directClauseNogoods.mkString("\n"))

    val pcnf = AspifOrDIMACSPlainParserResult(symbols = symbolsArray,
      rulesOrClauseNogoods = Right(directClauseNogoods),
      noOfPosBlits = 0,
      noOfDummySymbols = 0,
      externalAtomElis = Seq(),
      assumptionElis = Seq(),
      clausesForChecksOpt = None,
      symbolToEliOpt = None,
      additionalUncertainAtomsInnerCostsStrs = (patsFromProbabilisticClauses.toArray,
        costsFromProbabilisticClauses.toArray,
        Array[String]()))

    val (inputData: InputData, _) = ParseOptimizationTerms.parseOptimizationTerms(mse = solverParametersOverlay.assureMSE,
      paramAtomsAndInnerCostsStrOpt = paramAtomsAndInnerCostsStrOpt,
      satMode = true,
      aspifOrDIMACSParserResult = pcnf)

    val (samplingResult: SamplingResult, _: AspifOrDIMACSPlainParserResult) =
      invokeSampler(inputData, solverParametersOverlay, baseSettingsForBatchTestsOpt = None, satMode = true)

    samplingResult

  }

}

class Clause

/**
  * A disjunctive set of literals (hard clause)
  *
  * @param literals
  */
case class BooleanClause(literals: Set[BooleanLiteral]) extends Clause {}

/**
  * A disjunctive set of literals, annotated with a probability (soft clause).
  * Observe that every probabilistic clause causes diff-SAT to introduce a new auxiliary propositional variable
  *
  * @param literals
  */
case class ProbabilisticBooleanClause(literals: Set[BooleanLiteral], probability: Double) extends Clause {}


/**
  * A literal, represented as a positive or negative integer value. The sign represents its logical polarity.
  * Value 0 is not allowed.
  *
  * @param value
  */
case class BooleanLiteral(value: Int) extends AnyVal

