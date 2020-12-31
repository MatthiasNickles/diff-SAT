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

/**
  *
  * Scala User API for probabilistic Answer Set Programming and multimodel optimization
  *
  */

package input

import java.util.regex.Matcher

import aspIOutils.Pred
import diffSAT.{fileNameOpt, invokeSampler, obtainInputFromText}
import input.AspifPlainParser.{AspifEli, AspifRule, addAspifRules, aspifRulesToEliRules, resolveDisjunctiveHead}
import sharedDefs.Eli
import solving.SamplingResult

import scala.collection.mutable.ArrayBuffer
import scala.collection.{Set, mutable}

/**
  * User API representation of a probabilistic or non-probabilistic ASP ground program,
  * consisting of a set of [[input.GroundSymbolicASPRule]] rules (for the User API for probabilistic Boolean clauses, see [[input.BooleanFormulaWithCosts]]).
  *
  * Some forms of non-ground rules are supported too (see [[input.SymbolicASPRule]]) but these must be grounded into
  * sets of ground rules by calling [[input.SymbolicASPRule.genGroundInstances]] before solving/sampling.
  *
  * Optionally, a background program in aspif format can be specified using parameter backgroundProgramAspifOpt.
  * In this case, the rules specified using GroundSymbolicASPRule are added to those in the background program.
  *
  * To specify arbitrary differentiable loss functions (beyond those indirectly specified using probabilistic rule weights) and parameter
  * atoms, use parameter paramAtomsAndInnerCostsStrOpt in method solve(). An example for this is analogous to the example
  * in [[input.BooleanFormulaWithCosts]].
  *
  * For how to use complex non-ground answer set programs (in aspif format), please refer to README.md
  *
  * Solver settings are provided using [[input.SolverParametersOverlay]].
  * The names and default values of available advanced settings (advancedSolverArgs) within this structure are listed in [[sharedDefs]]
  *
  * ==API usage example 1: Sampling with probabilistic ground rules==
  *
  * {{{
  *       val rules: Set[GroundSymbolicASPRule] = Set(
  *
  *         /*
  *             [0.7] p :- not q.  % rule has probability 0.7
  *             {q}. % we need this choice rule just to ensure predicate q is defined
  *             {p}.
  *         */
  *
  *         GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not q"),
  *          probabilityOpt = Some(0.7d) // Probability of the ground rule (use 'None' for a hard rule)
  *          )
  *         , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("p")))
  *         , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("q")))
  *
  *       )
  *
  *       val solverParams = SolverParametersOverlay(
  *         noOfModels = -1, // -1 means sample until desired accuracy (loss threshold) has been reached. A positive
  *         // number would specify a minimum sample size (in terms of number of answer sets).
  *         noOfSecondaryModels = 0,
  *         offHeapGarbageCollectionModeR = 0,
  *         thresholdOpt = Some(1e-5d), // the desired accuracy (lower = more accurate but sampling requires more time)
  *         assureMSE = true, // true = the loss function (which in this example is automatically generated from the probabilistic facts)
  *          // is assured to be of type MSE
  *         showauxInSATmode = false,
  *         advancedSolverArgs = mutable.HashMap[(String, Int), String]( // advanced settings, see sharedDefs
  *           ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
  *           , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
  *         )
  *       )
  *
  *       // Create the program from the rules and parameters and sample models:
  *       val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
  *         solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)
  *
  *       // Print sample and the result of ad hoc query Pr(q AND p):
  *       val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
  *         satMode = false,
  *         samplingResult = sampled,
  *         adHocConjunctiveQueries = Seq(),
  *         adHocDisjunctiveQueries = Seq(Seq("q", "p")),
  *         printAdHocQueryResults = true,
  *         printAnswers = true)
  *
  *  }}}
  *
  * ==API usage example 2: Sampling with probabilistic non-ground rules==
  *
  * {{{
  *       val domainAtoms = Seq("p(a)", "p(b)") // For grounding. Observe that these atoms don't automatically become facts or body literals.
  *
  *       val uncertainNongroundRuleGroundings: Seq[GroundSymbolicASPRule] = SymbolicASPRule(
  *         headLiterals = Set("p(X)"),
  *         bodyLiterals = Set("not q"),
  *         domainAtoms = domainAtoms,
  *         probabilityOpt = Some(0.7d),  // Probability of the rule (use 'None' for a hard rule)
  *         distrPrOverGroundings = false // with false, the probability applies to the entire non-ground rule.
  *          // With true (which might be more useful in practice), it would apply to each ground instance rule individually.
  *         ).genGroundInstances
  *
  *       println("\n------------- Ground instances of [0.7] p(X) :- not q :\n" + uncertainNongroundRuleGroundings.mkString("\n"))
  *
  *       val groundRules: Set[GroundSymbolicASPRule] = { // all ground rules of the program
  *         /*
  *               #domain p(a).
  *               #domain p(b).
  *
  *               [0.7] p(X) :- not q.
  *               {p(a)}.
  *               {p(b)}.
  *               {q}.
  *           */
  *
  *         uncertainNongroundRuleGroundings ++
  *           SymbolicASPRule(choiceHeadOpt = Some(Seq("p(a)"))).genGroundInstances ++
  *           SymbolicASPRule(choiceHeadOpt = Some(Seq("p(b)"))).genGroundInstances ++
  *           Seq(GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("not q"))))
  *
  *
  *       }.toSet
  *
  *       //println("\n------------- Grounding:\n" + groundRules.mkString("\n"))
  *
  *       val solverParams = SolverParametersOverlay(
  *         noOfModels = -1, // -1 means sample until desired accuracy (thresholdOpt) has been reached. A positive
  *         // number would specify a minimum sample size (number of answer sets).
  *         noOfSecondaryModels = 0,
  *         offHeapGarbageCollectionModeR = 0,
  *         thresholdOpt = Some(1e-20d), // the desired accuracy (lower = more accurate but sampling requires more time)
  *         assureMSE = true, // true = the loss function (which in this example is automatically generated from the probabilistic facts)
  *         // is assured to be of type MSE
  *         showauxInSATmode = false,
  *         advancedSolverArgs = mutable.HashMap[(String, Int), String]( // advanced settings, see sharedDefs
  *           ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
  *           , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
  *         )
  *       )
  *
  *       // Create the program from the rules and parameters and sample models:
  *
  *       val sampled: SamplingResult = ProbabilisticAnswerSetProgram(groundRules, backgroundProgramAspifOpt = None).
  *         solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)
  *
  *       // Print sample and the result of ad hoc query Pr[p(a):-not q AND p(b):-not q]:
  *
  *       val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults,
  *       adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
  *         satMode = false,
  *         samplingResult = sampled,
  *         adHocConjunctiveQueries = Seq(),
  *         adHocDisjunctiveQueries = Seq(),
  *         adHocConjunctionOfSimpleGroundRulesQuery = Seq(("p(a)", Seq("not q")), ("p(b)", Seq("not q"))), // we use
  *         // adHocConjunctionOfSimpleGroundRulesQuery because distrPrOverGroundings = false in the grounding of the
  *         // probabilistic rule.
  *         printAdHocQueryResults = true,
  *         printAnswers = true)
  *
  * }}}
  *
  * ==Further examples can be found in the source code of [[userAPItests.APITests]]==
  *
  * @see [[input.SymbolicASPRule]], [[input.GroundSymbolicASPRule]], [[sharedDefs]], [[diffSAT#queryAndPrintSolverResult(boolean, boolean, solving.SamplingResult, scala.Option, scala.collection.immutable.Seq, scala.collection.immutable.Seq, scala.collection.immutable.Seq, scala.collection.immutable.Seq, boolean, boolean)]]
  * @constructor                     Creates a probabilistic or non-probabilistic answer set program
  * @param groundSymbolicASPRules    Set of ground rules. If backgroundProgramAspifOpt is defined, the symbolicASPRules added to the rules obtained by parsing the string in backgroundProgramAspifOpt
  * @param backgroundProgramAspifOpt Aspif format with optional costs and parameter specs
  * @author Matthias Nickles
  *
  * */
case class ProbabilisticAnswerSetProgram(groundSymbolicASPRules: Set[GroundSymbolicASPRule],
                                         backgroundProgramAspifOpt: Option[String] = None) {

  val inputDataFromBackgroundProgOpt =
    backgroundProgramAspifOpt.map(backgroundProgStr => {

      val (inputData: InputData,
      satMode: Boolean,
      inlineArgsOpt: Option[_],
      (commentInFileSaysUNSAT: Boolean, commentInFileSaysSAT: Boolean),
      (inlineProbabilityChecksOpt: Option[_]),
      inlineAllModelsCheckTokensOpt: Option[_],
      inlineAllModelsMultilineCheckTokensOpt: Option[_]) = if (fileNameOpt.isEmpty)
        obtainInputFromText(Right(backgroundProgStr), mseInCommandLineOpt = None)

      inlineArgsOpt.foreach(_ => input.diffSAT.stomp(-5014, "Inline arguments in background program ignored"))

      if (satMode)
        input.diffSAT.stomp(-100, "Background program cannot be cnf data")

      if (inlineProbabilityChecksOpt.isDefined || inlineAllModelsCheckTokensOpt.isDefined || inlineAllModelsMultilineCheckTokensOpt.isDefined)
        input.diffSAT.stomp(-5014, "Inline checks in background program ignored")

      if (inputData.aspifOrDIMACSPlainParserResult.aspifEliToSymbolOpt.isEmpty || inputData.aspifOrDIMACSPlainParserResult.aspifRulesOpt.isEmpty)
        input.diffSAT.stomp(-10000, "Aspif rules missing in parser result from backgroundProgramOpt")

      (inputData.aspifOrDIMACSPlainParserResult.aspifEliToSymbolOpt.get, inputData.aspifOrDIMACSPlainParserResult.aspifRulesOpt.get,
        inputData.aspifOrDIMACSPlainParserResult.symbols)

    })

  val aspifEliToSymbol = inputDataFromBackgroundProgOpt.map(_._1).getOrElse(mutable.HashMap[AspifEli, String]()) // TODO: dito

  val initialAspifRules = inputDataFromBackgroundProgOpt.map(_._2).getOrElse(ArrayBuffer[AspifRule]())

  val symbolsSet: mutable.HashMap[Pred, AspifEli] = aspifEliToSymbol.map(kv => (kv._2, kv._1)) // inputDataFromBackgroundProgOpt.map(_._3).getOrElse(mutable.HashMap[Pred, AspifEli]()) // TODO: gets updated via side effect

  // Further rules (symbolicASPRules) are simply appended to the list of rules defined in backgroundProgramAspifOpt:

  val aspifRulesBeforeShiftUnfold: ArrayBuffer[AspifRule] = {

    val aspifRulesBeforeShiftUnfold = initialAspifRules

    groundSymbolicASPRules.to(ArrayBuffer).foreach((symRule: GroundSymbolicASPRule) => {

      val (headPosAtomsAspifElis,
      headNegAtomsAspifElis,
      bodyPosAtomsAspifElis,
      litsFromDoubleNegatedInBody: Set[AspifEli],
      bodyNegAtomsAspifElis,
      weightBodyOpt,
      choiceHeadOpt,
      probabilityOpt
        ) =
        symRule.translateSymbolicRuleToSetsOfAspifElis(aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)

      addAspifRules(
        bodyGivenPosAspifLits = bodyPosAtomsAspifElis,
        bodyGivenNegAspifLits = bodyNegAtomsAspifElis,
        headGivenPosAspifLits = headPosAtomsAspifElis,
        headGivenNegAspifLits = headNegAtomsAspifElis,
        aspifRulesBuffer = aspifRulesBeforeShiftUnfold,
        aspifEliToSymbol = aspifEliToSymbol,
        aspifElisFromDoubleNegatedInBody = litsFromDoubleNegatedInBody,
        weightBodyOpt = weightBodyOpt,
        choiceHeadOpt = choiceHeadOpt,
        probabilityOpt = probabilityOpt)

    })

    aspifRulesBeforeShiftUnfold

  }

  if (sharedDefs.generateIntegrityRulesForAPIdefinedClassicNegation >= 1) {

    aspifEliToSymbol.foreach((aspifEliAndSymbol: (AspifEli, String)) => {

      if (aspifEliAndSymbol._2.startsWith("-")) { // we generate an integrity rule :- x,-x. Remark: We do this only for API-provided rules
        // with classical negation, not for classical negation in aspif-files (where we assume the grounder has added integrity constraints already)

        val bodyGivenPosAspifLits: Set[AspifEli] = Set(aspifEliAndSymbol._1, {

          aspifEliToSymbol.find(_._2 == aspifEliAndSymbol._2.stripPrefix("-")).getOrElse({

            input.diffSAT.stomp(-5019, "Classically negated atom " + aspifEliAndSymbol._2 + " found but there is no " + aspifEliAndSymbol._2.stripPrefix("-"))

            (0, "")

          })._1

        })

        val bodyGivenNegAspifLits = Set[AspifEli]()

        addAspifRules(
          bodyGivenPosAspifLits = bodyGivenPosAspifLits.toArray,
          bodyGivenNegAspifLits = bodyGivenNegAspifLits.toArray,
          headGivenPosAspifLits = Array(), headGivenNegAspifLits = Array(),
          weightBodyOpt = None,
          choiceHeadOpt = None,
          aspifRulesBuffer = aspifRulesBeforeShiftUnfold,
          aspifEliToSymbol = aspifEliToSymbol,
          probabilityOpt = None)

      }

    })

  }

  val aspifRulesAfterShiftUnfold = resolveDisjunctiveHead(sharedDefs.maxNoOfUnfolds, aspifRulesBeforeShiftUnfold)

  val symbols: Array[String] = aspifEliToSymbol.values.toArray // needs to be the complete set of all symbols (before we can assign blits to rule bodies below)

  val (rules: ArrayBuffer[sharedDefs.Rule], noOfPosBlits: Int, emptyBodyBlit, symbolToEli: Map[String, Eli],
  additionalUncertainAtomsInnerCostsStrs, assumptionElis) =
    aspifRulesToEliRules(symbols, aspifRulesAfterShiftUnfold, Some(aspifEliToSymbol), Seq[AspifEli]())

  if (sharedDefs.debug)
    println("Eli rules (including background program) in ProbabilisticAnswerSetProgram:\n" + rules.map(_.toString(symbols)).mkString("\n"))


  /**
    * Calls the sampler for this logic program. Optionally with additional multimodel cost terms (in addition
    * to those generated from any probabilistic clauses)
    *
    * @param solverParametersOverlay
    * @param paramAtomsAndInnerCostsStrOpt An optional string with a specification of parameter atoms and cost terms
    *                                      (see README.md). These costs are in addition to those specified indirectly using
    *                                      probabilistic clauses.
    * @return SamplingResult The list of models is in SamplingResult.modelsSymbolic. Since sampling
    *         is with replacement, the list represents a multiset of models.
    */
  def solve(solverParametersOverlay: SolverParametersOverlay,
            paramAtomsAndInnerCostsStrOpt: Option[String] = None): SamplingResult = {


    val pcnfFromASP: AspifOrDIMACSPlainParserResult = AspifOrDIMACSPlainParserResult(symbols = symbols,
      rulesOrClauseNogoods = Left(rules),
      noOfPosBlits = noOfPosBlits,
      noOfDummySymbols = 0,
      externalAtomElis = Seq(),
      assumptionElis = assumptionElis,
      emptyBodyBlit = emptyBodyBlit,
      clausesForChecksOpt = None, symbolToEliOpt = Some(symbolToEli),
      additionalUncertainAtomsInnerCostsStrs = additionalUncertainAtomsInnerCostsStrs)

    val (inputData: InputData, _) = ParseOptimizationTerms.parseOptimizationTerms(mse = solverParametersOverlay.assureMSE,
      paramAtomsAndInnerCostsStrOpt = paramAtomsAndInnerCostsStrOpt,
      satMode = false,
      aspifOrDIMACSParserResult = pcnfFromASP)

    val (samplingResult: SamplingResult, _: AspifOrDIMACSPlainParserResult) =
      invokeSampler(inputData, advancedSolverParametersOverlay = solverParametersOverlay, baseSettingsForBatchTestsOpt = None,
        satMode = false)

    samplingResult

  }

}

/**
  * Allows to represent all fundamental rule types in Answer Set Programming except weak rules :~.
  * Additionally, it supports probabilistic rules (rules with a probabilistic weight).
  * More complex ASP rule types can be created as combinations or desugarings using these basic types, see, e.g., Lifschitz, Turner: Nested Expressions in Logic Programs, 1999.
  * This data type fully supports ground rules but also has limited support for non-ground rules (for more advanced grounding
  * needs, it is recommended to use diff-SAT with an aspif file produced from the non-ground answer set program with a tool such as clingo).
  *
  * This class also provides some support for non-ground rules, using parameters variableBindings and domainAtoms.
  * The rule can be grounded by calling [[input.SymbolicASPRule.genGroundInstances]].
  *
  * However, for more complex grounding requirements, the answer set program should be translated into aspif format before calling diff-SAT,
  * using, e.g., clingo.
  *
  * Complete examples can be found in [[input.ProbabilisticAnswerSetProgram]] and [[userAPItests.APITests]]
  *
  * ==Default and classical negation==
  * To represent a classically ("strong") negated atom a, write -p(a). Allowed in head and body literals. "--p(a)" is not allowed.
  * To represent default negation in head or body literals, use prefix "not" (e.g., "not p(a)").
  * Double negation ("not not ") is also allowed, both in head and body literals. Triple negation ("not not not") is not supported.
  *
  * Redundant whitespace in literals is not allowed. There must be exactly one space character after a "not" and there
  * mustn't be any whitespaces in literals except to separate "not".
  * E.g., "not f(X)" is ok, "  not  f ( X) " is invalid.
  *
  * Supported rule types:
  *
  * ==Integrity constraints==
  * These are simply rules where the head is the empty set.
  *
  * =="Weight rules" (ASP terminology. Unrelated to rules with probabilistic weights!)==
  * Instead of bodyLiterals there can be a weightBodySymbolicOpt in the form of Some(lowerBound, Seq((weight1, literal1), ..., (weightN, literalN)))
  * literal can here be "atom" or "not atom" (but not "not not atom"). Observe that more complex weight rules (e.g.,
  * with upper bound) can be desugared into multiple more basic rules.
  * If weightBodySymbolicOpt is defined, bodyLiterals must be empty (but rules with both weight aggregates and plain literals can
  * be created as combinations of more basic rules).
  *
  * ==Choice rules==
  * Instead of headLiterals, choiceHeadOpt can be present in form of Some(Seq(literal1, ..., literalN)), where
  * each literal can here be an "atom" (but not "not atom" or "not not atom"). Again, more complex rules (such as choice in bodies)
  * can be expressed as combinations of simpler rules.
  * Choice rules are often preferable in terms of complexity over disjunctions (i.e., more than one literal) in the head,
  * but observe that their semantics is different.
  * If choiceHeadOpt is defined, headLiterals must be empty.
  *
  * ==Probabilistic rules==
  *
  * To express probabilistic facts, use special predicates _pr_ and _cost_ (must be facts, i.e., in head, with empty body).
  * E.g., "_pr_(heads(coin), 5000)" or  "_cost_(1 - f(coin))".
  *
  * To attach a probability to an entire normal rule, you can use probabilityOpt. In this case, the rule must be normal, i.e,
  * have exactly one head literal which is positive and double negation or a weight body in the body aren't allowed.
  *
  * A probability is represented as a double number w, 0<=w<=1.
  *
  * Probabilistic rules don't have to be probabilistically independent from each other.
  *
  * If the probabilityOpt=Some(-1), the probability is unknown (informally meaning 'rule v not rule', i.e., a
  * so-called _spanning rule_ [Nickles,Mileo 2015]).
  *
  * ==Basic grounding==
  *
  * There is limited support for rule grounding (for a more powerful approach to grounding, use clingo/gringo or some
  * other modern ASP grounder to generate an aspif file which you can then use directly with diff-SAT):
  *
  * Grounding is performed if variableBindings and/or variableDomains are provided.
  *
  * variableBindings are processed linearly. E.g., rule r(X,Y) :- q(X), p(Y) with variableBindings Seq((X,"a"),(Y,"b"),(X,"c"))
  * results in a single ground rule r(a,b) :- q(a), p(b), because the second binding of X is ignored. To explore
  * all combinations, use something like concurrentBindings.flatMap(bindings -> SymbolicASPRule(...,bindings,...))
  *
  * In contrast to variableBindings, domainAtoms are processed by using all possible combinations.
  * E.g., r(X,Y) :- q(X), p(Y) with domainAtoms Seq("q(a)", "p(b)", "q(c)") results in two ground rules
  * r(a,b) :- q(a), p(b) and r(c,b) :- q(c), p(b)
  *
  * variableBindings are processed before domainAtoms, so if any variable is already bound by variableBindings,
  * it cannot be re-bound by any domainAtoms.
  *
  * domainAtoms (as a parameter of SymbolicASPRule) are not necessarily actually facts (in the logical sense) and they are
  * not automatically added as literals to the rule. If you want that, you need to add those "facts" explictly to
  * the bodyLiterals or make them actual facts as rules of their own.
  *
  * Approaches (outside the scope of diff-SAT) to obtain domainAtoms could be, e.g., to deduce them as extension from given
  * ground rules where the involved predicates don't recursively depend on each other (as in lparse 1.0), or - less powerful -
  * to simply use all given ground facts (ground rules with empty body), or to use ground atoms in the body of the non-ground rule.
  *
  * If a probability w is provided for a non-ground normal rule using probabilityOpt, it refers either to the conjunction of the
  * ground rules generated from the non-ground rule or to each individual ground rule, depending on distrPrOverGroundings.
  * E.g., with distrPrOverGroundings=false, Pr[p(X):-q(Y)] = w is equivalent to Pr[(p(a):-q(b)) ^ (p(c):-q(a)) ^ ...] = w,
  * if the ground instances of p(X):-q(Y) are p(a):-q(b), p(c):-q(a), ...
  * Whereas with distrPrOverGroundings=true, Pr[p(X):-q(Y)] = w is equivalent to Pr[p(a):-q(b)]=w ^ Pr[p(c):-q(a)]=w ^ ...
  *
  * ASP variables are words consisting of characters and digits which start with an uppercase letter.
  * Variables can occur in any literals in the head and/or body.
  *
  * Observe that gringo-style anonymous variables (_) or character ' in variables are not allowed here (but such variables
  * can be used when using clingo/gringo output with diff-SAT).
  *
  * Variables in terms are recognized up to parantheses nesting level three.
  *
  * diff-SAT doesn't distinguish between the case that a variable occurs in the head and the case it occurs in the body.
  *
  * @constructor                 Create an instance of this case class
  * @param headLiterals          A disjunction of positive or negative or double negative or classical-negative literals (can be empty)
  * @param bodyLiterals          A conjunction of positive or negative or double negative or classical-negative literals (can be empty)
  * @param choiceHeadOpt         See above
  * @param weightBodySymbolicOpt See above (NB: the term "weight" here is ASP terminology and unrelated to probabilistic weights!)
  * @param probabilityOpt        An optional double value 0 <= p <= 1 or -1 (see above)
  * @param variableBindings      A list containing variable names (words starting with an uppercase letter) paired with ground terms.
  *                              For example, Seq(("X", "a1"), ("X", "a2"), ("Y", "b1"), ...).
  *                              Alternatively or additioally, domainAtoms can be provided to ground rules.
  * @param domainAtoms           A list of ground atoms, e.g., "fac1(a,b)", "fac1(c,d)", "fac2(a)", ...).
  *                              Like variableBindings, they are used to ground rules (by determining further variable bindings).
  *                              NB: Ground facts listed here serve only to instantiate variables, they do not automatically become
  *                              body literals or even global facts. If you wish to add them, e.g., to the rule body, you need to append them
  *                              to bodyLiterals.
  *                              NB: redundant whitespace is not allowed in domain atoms and rule literals
  * @param distrPrOverGroundings If true (default), the probability probabilityOpt (if defined) is assumed to be the probability of each individual
  *                              ground instances of the rule (corresponding to weight syntax [[pr]] in PrASP).
  *                              If false, the given probability (probabilityOpt, if defined) is the probability of the
  *                              entire conjunction of all ground instances of this rule (corresponding to weight syntax [pr] in PrASP).
  *                              Only relevant if there are variables in the literals, variableDomains is not empty, and probabilityOpt is defined.
  */
case class SymbolicASPRule(headLiterals: Set[Pred] = Set(),
                           bodyLiterals: Set[Pred] = Set(),
                           choiceHeadOpt: Option[Seq[Pred /*"atom" or "not atom"*/ ]] = None,
                           weightBodySymbolicOpt: Option[(Int /*lower bound*/ ,
                             Seq[(Int /*weight_i*/ , Pred /*"atom" or "not atom"*/ )])] = None,
                           probabilityOpt: Option[Double] = None,
                           variableBindings: Seq[(String, String)] = Seq(),
                           domainAtoms: Seq[String] = Seq(),
                           distrPrOverGroundings: Boolean = true
                          ) {

  override def toString: String = {

    val head = if (choiceHeadOpt.isDefined) {

      "{" + choiceHeadOpt.get.mkString(";") + "}"

    } else
      headLiterals.mkString(";")

    val body = if (weightBodySymbolicOpt.isDefined) {
      weightBodySymbolicOpt.get._1 + "<={" + weightBodySymbolicOpt.get._2.map((wLit: (Int, String)) => wLit._1 + ":" + wLit._2) + "}"

    } else
      bodyLiterals.mkString(",")

    head + " :- " + body + "."

  }

  val anyVariableNameRegex = """\b[A-Z]\w*\b""".r // (observe that _ isn't allowed as first variable character in our implementation of ASP variable names)

  /**
    * Grounds this rule using the domains specified by variableBindings and domainAtoms.
    *
    * ASP variables are words consisting of characters and digits which start with an uppercase letter.
    * Variables can occur in any literals in the head and/or body.
    * Observe that gringo-style anonymous variables (_) or character ' in variables are not allowed here (but such variables
    * can be used when using clingo/gringo output with diff-SAT).
    * Variables in terms are recognized up to parantheses nesting level three.
    * Literals must not contain any redundant space. E.g., "not f(X)" is ok, "  not  f(X) " is invalid.
    * Also observe that diff-SAT doesn't care if a variable is in the head or in the body, and that it
    * does not automatically add domain facts to the knowledge base.
    *
    * A probabilistic rule weight is resolved using the semantics specified by flag distrPrOverGroundings in the rule constructor.
    *
    * @return a list of symbolic ground rules (the instances of the non-ground rule, plus helper rules in
    *         case of a probabilistic rule). Result is empty if unification failed (grounding impossible).
    */
  def genGroundInstances: Seq[GroundSymbolicASPRule] = {

    if(probabilityOpt.isDefined && !distrPrOverGroundings) {

      /* We emulate Pr( H :- B ) = w (with non-ground H and/or B) using
      		aux :- B, not H.
		      H :- B, not aux.
		      {aux}.
          _pr_(aux, (1-w)*1000).

          The effect is as Pr ( r1 ^ ... ^ rn ) = w, with ri being the ground instances of H:-B.
          Note that sensible use may require further rules (provided by the user), e.g., spanning rules for predicates in H or B.

          The above translation using aux is essentially the same translation of probabilistic rules which is applied
          in aspifRulesToEliRules(), but on a higher level before any grounding.

       */

      // Remark: we don't check if the rule is actually non-ground. If it isn't, the following translation is redundant but harmless.

      val auxPred = "__aux" + Math.abs(this.hashCode) // TODO: use proper aux naming scheme

      val rule1 = SymbolicASPRule(headLiterals = Set(auxPred),
      bodyLiterals
      = this.bodyLiterals ++ this.headLiterals.map("not " + _),
      choiceHeadOpt = this.choiceHeadOpt,
      weightBodySymbolicOpt = this.weightBodySymbolicOpt,
      probabilityOpt= None,
      variableBindings = this.variableBindings,
      domainAtoms = this.domainAtoms,
      distrPrOverGroundings = false)

      val rule2 = SymbolicASPRule(headLiterals = this.headLiterals,
        bodyLiterals
          = this.bodyLiterals ++ Seq("not " + auxPred),
        choiceHeadOpt = this.choiceHeadOpt,
        weightBodySymbolicOpt = this.weightBodySymbolicOpt,
        probabilityOpt = None,
        variableBindings = this.variableBindings,
        domainAtoms = this.domainAtoms,
        distrPrOverGroundings = false)

      /* nope:
      val rule3 = GroundSymbolicASPRule(headLiterals = Set(),
        bodyLiterals = Set(),
        choiceHeadOpt = Some(Seq(auxPred)),
        weightBodySymbolicOpt = this.weightBodySymbolicOpt,
        probabilityOpt = None) */

      val rule4 = GroundSymbolicASPRule(headLiterals = Set(sharedDefs.probabilisticFactPrefix + "(" +
        auxPred + "," + ((1d-probabilityOpt.get) * sharedDefs.probabilisticFactProbDivider).toInt + ")"),
        bodyLiterals = Set(),
        choiceHeadOpt = None,
        weightBodySymbolicOpt = None,
        probabilityOpt = None)

      val groundInstancesRule1 = rule1.genGroundInstancesRec.map(sr => GroundSymbolicASPRule(sr.headLiterals,
        sr.bodyLiterals,
        sr.choiceHeadOpt,
        sr.weightBodySymbolicOpt,
        sr.probabilityOpt
      )).filterNot(rule => rule.headLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined) ||
        rule.bodyLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined))

      val groundInstancesRule2 = rule2.genGroundInstancesRec.map(sr => GroundSymbolicASPRule(sr.headLiterals,
        sr.bodyLiterals,
        sr.choiceHeadOpt,
        sr.weightBodySymbolicOpt,
        sr.probabilityOpt
      )).filterNot(rule => rule.headLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined) ||
        rule.bodyLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined))


      groundInstancesRule1 ++ groundInstancesRule2 ++ Seq(/*rule3,*/ rule4)


    } else {  // in this case, the given probability (if any) is simply attached to each ground instance

      val groundInstancesNG = genGroundInstancesRec

      val groundInstances = groundInstancesNG.map(sr => GroundSymbolicASPRule(sr.headLiterals,
        sr.bodyLiterals,
        sr.choiceHeadOpt,
        sr.weightBodySymbolicOpt,
        sr.probabilityOpt
      ))

      //println(groundInstances.mkString("\n"))

      groundInstances.filterNot(rule => {

        val allLiterals: Set[Pred] = rule.headLiterals.union(rule.bodyLiterals).union(rule.choiceHeadOpt.getOrElse(Seq[Pred]()).toSet).union(rule.weightBodySymbolicOpt.getOrElse((-1, Seq[(Int, Pred)]()))._2.unzip._2.toSet)

        allLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined)

      })

    }

  }

  /**
    * Don't call directly, call via genGroundInstances()
    *
    * @return Set of SymbolicASPRule (empty if unification failed)
    */
  protected def genGroundInstancesRec: Seq[SymbolicASPRule] = {

    /*
        In the following, domainAtoms are only considered when there aren't anymore explicit (varName=varValue) bindings
        (variableBindings). If domainAtoms match against non-ground literals, they create new explicit (varName=varValue) bindings
        for the variables in the literals. Important: These bindings are not necessarily valid for the entire rule - thus the result
        of genGroundInstancesRec needs to be examined for rules with remaining variables - these
        are invalid and need to be dismissed (in genGroundInstances) - see example later in the code.
     */

    //println("\n--------- genGroundInstancesRec for " + this)

    lazy val allLiterals: Set[Pred] = headLiterals.union(bodyLiterals).union(choiceHeadOpt.getOrElse(Seq[Pred]()).toSet).union(weightBodySymbolicOpt.getOrElse((-1, Seq[(Int, Pred)]()))._2.unzip._2.toSet)

    lazy val containsVariables = allLiterals.exists(literal => anyVariableNameRegex.findFirstIn(literal).isDefined)

    if (variableBindings.isEmpty && domainAtoms.isEmpty)
      Seq(SymbolicASPRule(headLiterals,
        bodyLiterals,
        choiceHeadOpt,
        weightBodySymbolicOpt,
        probabilityOpt
      ))
    else if (!containsVariables) {

      Seq(SymbolicASPRule(headLiterals,
        bodyLiterals,
        choiceHeadOpt,
        weightBodySymbolicOpt,
        probabilityOpt
      ))

    } else if (!variableBindings.isEmpty) { // any explicit (varName=varValue) bindings?

      //println("variableBindings: " + variableBindings.mkString(","))

      val (varName, varValue) = variableBindings.head

      val variableNameRegex: String = """\b""".r + varName + """\b""".r

      val tailVarVal = variableBindings.tail

      val partiallyGroundedHeadLiterals = headLiterals.map(_.replaceAll(variableNameRegex, varValue))

      val partiallyGroundedBodyLiterals = bodyLiterals.map(_.replaceAll(variableNameRegex, varValue))

      val partiallyGroundedChoiceHeadLiteralsOpt: Option[Seq[Pred]] = choiceHeadOpt.map(_.map(_.replaceAll(variableNameRegex, varValue)))

      val partiallyGroundedWeightBodySymbolicOpt: Option[(Int, Seq[(Int, Pred)])] = weightBodySymbolicOpt.map((tuple: (Int, Seq[(Int, Pred)])) => {

        (tuple._1, tuple._2.map((tuple2: (Int, Pred)) => (tuple2._1, tuple2._2.replaceAll(variableNameRegex, varValue))

        ))

      })

      val partiallyGroundedRuleA = SymbolicASPRule(partiallyGroundedHeadLiterals,
        partiallyGroundedBodyLiterals,
        partiallyGroundedChoiceHeadLiteralsOpt,
        partiallyGroundedWeightBodySymbolicOpt,
        probabilityOpt,
        variableBindings = tailVarVal,
        domainAtoms = domainAtoms,
        distrPrOverGroundings
      )

      val r = partiallyGroundedRuleA.genGroundInstancesRec

      r

    } else {
      // In this case, we use ground facts from which we generate new variable bindings by
      // pattern matching against rule literals with variables.

      assert(variableBindings.isEmpty)

      val literals = allLiterals //headLiterals.union(bodyLiterals)

      val newVarBindingsFromdomainAtoms: Set[Seq[(String, String)]] = literals.flatMap(literal => {

        val termRegEx = /*"([^()]*|\\\\([^()]*\\\\))*"*/
        // ^ recognizes nested terms up to depth 2
          "([^()]*|\\\\(([^()]*|\\\\([^()]*\\\\))*\\\\))*" // up to depth 3
        // for debugging, https://www.freeformatter.com/java-regex-tester.html#ad-output might be useful

        //@inline def placeholderRegex(varName: Pred): String = "\\\\b(?<" + varName + ">\\" + termRegEx + "\\\\b)"
        @inline def placeholderRegex(varName: Pred): String = "(?<" + varName + ">\\" + termRegEx + ")" // regex group names broken in Scala 2.13(?), so we use Java's regex directly

        val aspVarNames: Seq[String] = anyVariableNameRegex.findAllMatchIn(literal).map(_.matched).distinct.toSeq

        //println("aspVarNamesMatches: " + aspVarNames.mkString(","))

        val literalParanthProtect = literal.replaceAllLiterally("(", "\\(").replaceAllLiterally(")", "\\)")

        val literalWithPlaceholders = aspVarNames.foldLeft(literalParanthProtect) { case (literal, varName) => {

          val varNameInMatchAsRegex = "\\b" + varName + "(?!\\>)\\b"
          
          val literalPos = literal.stripPrefix("not ").stripPrefix("not ")
          
          val literalFirstReplaced = literalPos.replaceFirst(varNameInMatchAsRegex, placeholderRegex(varName))

          val literalRestReplaced = literalFirstReplaced.replaceAll(varNameInMatchAsRegex, "\\\\k<" + varName + ">")

          literalRestReplaced

        }

        }

        //println("literalWithPlaceholders: " + literalWithPlaceholders)

        //println(domainAtoms)

        val varBindingsForLiteral: Seq[Seq[(String, String)]] = domainAtoms.flatMap {

          case (domainAtom: String) => {

            //println(domainAtom)

            val compile = java.util.regex.Pattern.compile(literalWithPlaceholders)

            val matcher: Matcher = compile.matcher(domainAtom)

            if (matcher.matches) {

              val groupMatched = aspVarNames.map(varName => {

                val r = matcher.group(varName)

                //println(r)

                (varName, r)

              })

              //println("groupMatched = " + groupMatched.mkString(","))

              Some(groupMatched)

            } else
              None

          }

        }

        varBindingsForLiteral

      }
      )

      val newVarBindingsFromdomainAtomsCleaned = newVarBindingsFromdomainAtoms.filterNot(_.isEmpty)

      /* Observe that some of those binding sequences may be invalid, namely if when genGroundInstancesRec is
       called recursively not all variables have been substituted. Example:

         d(a,b).  // domain fact
         d(a,c).  // domain fact
         d(c,a).  // domain fact

         foo(X,Y,Z) :- d(X,Y), d(Y,Z), not bar(X,Y,Z).

         d(X,Y) matches against d(a,b), which generates new bindings { X/a, Y,b }. However, this doesn't
         lead to a fully grounded rule, since foo(a,b,Z) :- d(a,b), d(b,Z), not bar(a,b,Z) cannot be further
         grounded. Thus this partially grounded rule needs to be dismissed in the end.

       */

      //println("New variable bindings:\n" + newVarBindingsFromdomainAtomsCleaned.mkString("\n") + "\n")

      val r: Seq[SymbolicASPRule] = if (newVarBindingsFromdomainAtomsCleaned /*.flatten*/ .isEmpty)
        Seq(SymbolicASPRule(headLiterals,
          bodyLiterals,
          choiceHeadOpt,
          weightBodySymbolicOpt,
          probabilityOpt,
          distrPrOverGroundings = distrPrOverGroundings,
          variableBindings = variableBindings,
          domainAtoms = domainAtoms
        ))
      else
        newVarBindingsFromdomainAtomsCleaned.flatMap((newVarBinding: Seq[(String, String)]) => {

          SymbolicASPRule(headLiterals,
            bodyLiterals,
            choiceHeadOpt,
            weightBodySymbolicOpt,
            probabilityOpt,
            distrPrOverGroundings = distrPrOverGroundings,
            variableBindings = newVarBinding ++ variableBindings,
            domainAtoms = domainAtoms // these are all kept, as they might generate bindings of other variables
          ).genGroundInstancesRec

        }).toSeq

      //println("\n**** r: " + r.mkString("\n"))

      r

    }

  }

}


/**
  * As [[input.SymbolicASPRule]], but without variables. See [[input.SymbolicASPRule]] for supported rule types.
  *
  * @param headLiterals          A disjunction of positive or negative or double negative or classical-negative literals (can be empty)
  * @param bodyLiterals          A conjunction of positive or negative or double negative or classical-negative literals (can be empty)
  * @param choiceHeadOpt         See above
  * @param weightBodySymbolicOpt See above (NB: the term "weight" here is ASP terminology and unrelated to probabilistic weights used elsewhere)
  * @param probabilityOpt        An optional double value 0 < p < 1 or -1 (see above)
  */
case class GroundSymbolicASPRule(headLiterals: Set[Pred] = Set(),
                                 bodyLiterals: Set[Pred] = Set(),
                                 choiceHeadOpt: Option[Seq[Pred /*"atom" or "not atom"*/ ]] = None,
                                 weightBodySymbolicOpt: Option[(Int /*lower bound*/ ,
                                   Seq[(Int /*weight_i*/ , Pred /*"atom" or "not atom"*/ )])] = None,
                                 probabilityOpt: Option[Double] = None
                                ) {

  override def toString: String = {

    val head = if (choiceHeadOpt.isDefined) {

      "{" + choiceHeadOpt.get.mkString(";") + "}"

    } else
      headLiterals.mkString(";")

    val body = if (weightBodySymbolicOpt.isDefined) {
      weightBodySymbolicOpt.get._1 + "<={" + weightBodySymbolicOpt.get._2.map((wLit: (Int, String)) => wLit._1 + ":" + wLit._2) + "}"

    } else
      bodyLiterals.mkString(",")

    head + " :- " + body + "."

  }

  private val defaultNegPrefix = "not "

  private val defaultDoubleNegPrefix = defaultNegPrefix + defaultNegPrefix

  if (weightBodySymbolicOpt.isDefined && !bodyLiterals.isEmpty)
    input.diffSAT.stomp(-5004, "weightBodySymbolicOpt must be None in case bodyLiterals is not empty:\n " + this)

  if (choiceHeadOpt.isDefined && !headLiterals.isEmpty)
    input.diffSAT.stomp(-5004, "choiceHeadOpt must be None in case headLiterals is not empty:\n " + this)

  probabilityOpt.foreach(probability => {

    if (headLiterals.size != 1 || choiceHeadOpt.isDefined || weightBodySymbolicOpt.isDefined)
      input.diffSAT.stomp(-5004, "probabilityOpt can only be used with normal rules:\n " + this)

    if (headLiterals.size != 1 || choiceHeadOpt.isDefined || weightBodySymbolicOpt.isDefined)
      input.diffSAT.stomp(-5004, "probabilityOpt can only be used with normal rules:\n " + this)

    if (probability != -1d && (probability < 0d || probability > 1d))
      input.diffSAT.stomp(-5004, "probabilityOpt value out of range: " + probability)

  })

  protected def translateSymbolicAtomToAspifEli(symbolicAtomR: Pred,
                                      aspifEliToSymbol: mutable.HashMap[AspifEli, String],
                                      symbolsSet: mutable.HashMap[Pred, AspifEli]): (AspifEli, Boolean /*<-- true if from double negation*/ ) = {

    val fromDoubleNegation = symbolicAtomR.startsWith(defaultDoubleNegPrefix)

    if (fromDoubleNegation && probabilityOpt.isDefined)
      input.diffSAT.stomp(-10000, "probabilityOpt can only be used with normal rules:\n " + this)

    val isNeg = !fromDoubleNegation && symbolicAtomR.startsWith(defaultNegPrefix)

    val symbolicAtom = symbolicAtomR.stripPrefix(defaultNegPrefix).trim.stripPrefix(defaultNegPrefix).trim

    val aspifEliAbs = symbolsSet.getOrElseUpdate(symbolicAtom, symbolsSet.size + 1)

    aspifEliToSymbol.put(aspifEliAbs, symbolicAtom)

    val aspifEli = if (isNeg) -aspifEliAbs else aspifEliAbs

    (aspifEli, fromDoubleNegation)

  }

  def translateSymbolicRuleToSetsOfAspifElis(aspifEliToSymbol: mutable.HashMap[AspifEli, String],
                                             symbolsSet: mutable.HashMap[Pred, AspifEli]):
  (Array[AspifEli], Array[AspifEli], Array[AspifEli], Set[AspifEli], Array[AspifEli],
    Option[(Int /*lower bound*/ , Seq[(Int /*weight_i*/ , AspifEli)])],
    Option[Seq[AspifEli]],
    Option[Double]) = {

    val (doubleNegatedHeadLiterals, headLiteralsC) = headLiterals.partition(_.startsWith(defaultDoubleNegPrefix))
    // not not a :- ... <=> :- ..., not a

    val bodyLiteralsC = bodyLiterals ++ doubleNegatedHeadLiterals.map(_.stripPrefix(defaultNegPrefix))

    val (headNegAtoms, headPosAtoms): (Set[Pred], Set[Pred]) = headLiteralsC.partition((atom: Pred) =>
      atom.startsWith(defaultNegPrefix) && !atom.startsWith(defaultDoubleNegPrefix))

    // Remark: We keep single-negated literals in the head, but they will be eliminated later in addAspifRule()

    val (bodyNegAtoms, bodyPosAtoms): (Set[Pred], Set[Pred]) = bodyLiteralsC.partition((atom: Pred) =>
      atom.startsWith(defaultNegPrefix) && !atom.startsWith(defaultDoubleNegPrefix))

    val bodyPosAtomsWithDoubleNegInfo = bodyPosAtoms.toArray.zipWithIndex.map(symbolicAtomWithIndex => translateSymbolicAtomToAspifEli(symbolicAtomR = symbolicAtomWithIndex._1, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet))

    val bodyPosAtomsDoubleNegInfo: Set[AspifEli] = bodyPosAtomsWithDoubleNegInfo.filter(_._2).unzip._1.toSet
    // ^those literals in the body which stem from "not not". We simply remove any "not not" in the body, but we need to keep
    // track of these literals as we need to give them a special handling in the stable model check after solving.
    //
    // In contrast, double negation in the head is removed (by shifting into single negation in body) without the
    // need to keep track, see above.
    //
    // NB: we need to expect "not not" only in symbolic User API. In ASPIF files no double negation can occur (desugared by grounder).

    val r = (headPosAtoms.toArray.zipWithIndex.map(symbolicAtomWithIndex => translateSymbolicAtomToAspifEli(symbolicAtomR = symbolicAtomWithIndex._1, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)).unzip._1,
      headNegAtoms.toArray.zipWithIndex.map(symbolicAtomWithIndex => translateSymbolicAtomToAspifEli(symbolicAtomR = symbolicAtomWithIndex._1, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)).unzip._1,
      bodyPosAtomsWithDoubleNegInfo.unzip._1,
      bodyPosAtomsDoubleNegInfo,
      bodyNegAtoms.toArray.zipWithIndex.map(symbolicAtomWithIndex => translateSymbolicAtomToAspifEli(symbolicAtomR = symbolicAtomWithIndex._1, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)).unzip._1,
      /* (has nothing to do with probabil. weight-->)*/weightBodySymbolicOpt.map((tuple: (Int, Seq[(Int, Pred)])) => (tuple._1, tuple._2.
        map((weightedLitSymbolic: (Int, Pred)) => (weightedLitSymbolic._1,
          translateSymbolicAtomToAspifEli(symbolicAtomR = weightedLitSymbolic._2, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)._1)))),
      choiceHeadOpt.map((seqChoiceLits: Seq[Pred]) => seqChoiceLits.map(choiceLit =>
        translateSymbolicAtomToAspifEli(symbolicAtomR = choiceLit, aspifEliToSymbol = aspifEliToSymbol, symbolsSet = symbolsSet)._1)),
      probabilityOpt
    )

    r

  }

}