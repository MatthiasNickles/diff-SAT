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

package userAPItests

import input.diffSAT
import sharedDefs.enforceWriteRuntimeStatsToFileOpt
import solving.SamplingResult

import scala.collection.mutable

/**
  * User API tests.
  *
  * Work in progress to replace older diff-SAT utests in Prasp2. TODO: add more tests
  *
  * Observe that we are using two major approaches: [[input.ProbabilisticAnswerSetProgram]] for (probabilistic or plain) answer set programming,
  * and [[input.BooleanFormulaWithCosts]] for (probabilistic or plain) Boolean formulas (in CNF). Each of these can
  * also be used with arbitrary differentiable cost functions (in fact probabilistic weights are translated into such functions anyway).
  *
  * From the commandline, run using --apitests
  *
  * For higher level blackbox testing with .cnf, .aspif and .opt files, use batch tests (--batchtests <folder>)
  *
  */
trait APITests {

  this: diffSAT.type =>

  def runAllAPITests: Unit = {

    import input._

    println("******** Running API tests... *********\n")

    enforceWriteRuntimeStatsToFileOpt = Some(false)

    var (testAttempted, testsSuccessful) = (0, 0)

    def testHeader(testHeader: (Boolean, String)): Boolean = {

      testHeader._1 && {

        println("\n~~~~~~~ Test '" + testHeader._2 + "'...")

        testAttempted += 1

        true

      }

    }

    def singleTestResult(success: Boolean): Boolean = {

      if (success)
        testsSuccessful += 1
      else
      /*System.err.*/ println("\nAPI Test failed!") // .err prints out of order?!

      success

    }

    val collective = true

    if (testHeader((collective, "Classic negation test 1 (UNSAT)"))) { //  ------------------------------------------------------------------------

      /*

        a.
        -a.
        :- a, -a.  % automatically added

      */

      val rules = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set()),

        GroundSymbolicASPRule(headLiterals = Set("-a"), bodyLiterals = Set())

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1"
          , ("diversify", 0) -> "false"
          , ("maxSolverThreadsR", 0) -> "4"
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 0)

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Integrity constraint test 1 (UNSAT)"))) { //  --------------------------------------------------------------------

      /*

        a.
        b.
        :- a, b.

      */

      val rules = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set())

        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set())

        , GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set("a", "b"))

      )

      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 0)

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, ":- p (SAT)"))) { //  --------------------------------------------------------------------

      /*

        :- p.

      */

      val rules = Set(

        GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set("p"))

      )

      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 1 && sampled.modelsSymbolic.head.toSet == Set())

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Negation test 1 (UNSAT)"))) { //  --------------------------------------------------------------------

      /*

        :- not p.

      */

      val rules = Set(

        GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set("not p"))

      )

      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 0)

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Fact test 1"))) { //  --------------------------------------------------------------------

      /*

        a.

      */

      val rules = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set())

      )

      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 1 && sampled.modelsSymbolic.head.toSet == Set("a"))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Empty test 1 (SAT)"))) { //  --------------------------------------------------------------------

      val rules: Set[GroundSymbolicASPRule] = Set()

      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 1 && sampled.modelsSymbolic.head.toSet == Set())


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Empty test 2 (UNSAT)"))) { //  --------------------------------------------------------------------

      /*
      
        :-.
      
       */

      val rules: Set[GroundSymbolicASPRule] = Set(GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set()))


      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 0)


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "p, :-p (UNSAT)"))) { //  --------------------------------------------------------------------

      /*

        p.
        :- p.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set())

        , GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set("p"))

      )


      val solverParams = SolverParametersOverlay(
        noOfModels = 1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, _, _, _, _) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = sampled.modelsSymbolic.length == 0)


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Double negation test 1"))) { //  --------------------------------------------------------------------

      /*

        p :- not not p.

        Two answer sets { p } and { }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not not p")))

      val solverParams = SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      //println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Double negation test 2"))) { //  --------------------------------------------------------------------

      /*

        a :- not not a.
        b :- not a.

        Two answer sets { a } and { b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not not a"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("not a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a"), Seq("b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      //println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Negation test 2"))) { //  --------------------------------------------------------------------

      /*

        a :- a
        b :- not a.

        One answer set: { b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("a"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("not a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a"), Seq("b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b" &&
          queryAndFrequency._2 == 1d

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Negation test 3"))) { //  --------------------------------------------------------------------

      /*

        p :- not q.
        q :- not p.

        Two answer sets { p }, { q }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not q"))
        , GroundSymbolicASPRule(headLiterals = Set("q"), bodyLiterals = Set("not p"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p"), Seq("q")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "q" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Double negation test 3"))) { //  --------------------------------------------------------------------

      /*

        a :- not not a.
        a :- b.
        b :- a.

        Two answer sets { }, { a b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not not a"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("b"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Double negation test 4"))) { //  --------------------------------------------------------------------

      /*

        a :- not not b.
        b :- not not a.

        Two answer sets { }, { a b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not not a"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("b"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Double negation test 5"))) { //  --------------------------------------------------------------------

      /*

        a :- not not b.
        b :- not not a.

        Two answer sets { }, { a b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not not a"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("b"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Head negation test 1"))) { //  --------------------------------------------------------------------

      /*

        not a :- b.
        a :- not not a.
        b :- not not b.
        a :- not b.

        Two answer sets { a }, { b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("not a"), bodyLiterals = Set("b"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not not a"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("not not b"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not b"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a") /*<-non-exclusive, includes a^b, otherwise we'd have to write Seq("a", "not b")*/ ,
          Seq("b"), Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 == 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b" &&
          queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Head double negation test 1"))) { //  --------------------------------------------------------------------

      /*

        not not p :- q.
        p :- not not p.
        q :- not not q.

        Three answer sets { }, { p }, { p q }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("not not p"), bodyLiterals = Set("q"))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not not p"))
        , GroundSymbolicASPRule(headLiterals = Set("q"), bodyLiterals = Set("not not q"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p", "not q"), Seq("q", "not p"), Seq("p", "q")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p ^ q" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p ^ not q" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "q ^ not p" &&
          queryAndFrequency._2 == 0d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Head negation test 2"))) { //  --------------------------------------------------------------------

      /*

        not p :- q, p.
        p :- not not p.
        q :- not not q.

        Three answer sets { }, { p }, { q }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("not p"), bodyLiterals = Set("q", "p"))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not not p"))
        , GroundSymbolicASPRule(headLiterals = Set("q"), bodyLiterals = Set("not not q"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p", "not q"), Seq("q", "not p"), Seq("p", "q")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p ^ q" &&
          queryAndFrequency._2 == 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p ^ not q" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "q ^ not p" &&
          queryAndFrequency._2 > 0d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Head negation test 3"))) { //  --------------------------------------------------------------------

      /*

        b; not b :- a.
        a.

        Two answer sets { a }, { a b }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("b", "not b"), bodyLiterals = Set("a"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set())

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a") /*<-non-exclusive, includes a^b, otherwise we'd have to write Seq("a", "not b")*/ ,
          Seq("b", "not a"), Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b ^ not a" &&
          queryAndFrequency._2 == 0d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Loop test 1"))) { //  --------------------------------------------------------------------

      /*

        a :- not d.
        a :- c.
        b :- c.
        c :- a, b.

        One answer set: { a }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not d"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("c"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("c"))
        , GroundSymbolicASPRule(headLiterals = Set("c"), bodyLiterals = Set("a", "b"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 == 1d

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Loop test 2"))) { //  --------------------------------------------------------------------

      /*

        a :- a.

        One answer set: { }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 == 0d

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Loop test 3"))) { //  --------------------------------------------------------------------

      /*

        a :- b.
        b :- a.
        a :- not c.
        c :- d.
        d :- c.
        c :- not a.

        Answer sets: { a, b }, { c, d }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

          GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("b"))
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set("a"))
        , GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set("not c"))
        , GroundSymbolicASPRule(headLiterals = Set("c"), bodyLiterals = Set("d"))
        , GroundSymbolicASPRule(headLiterals = Set("d"), bodyLiterals = Set("c"))
        , GroundSymbolicASPRule(headLiterals = Set("c"), bodyLiterals = Set("not a"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a", "b"), Seq("c", "d")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 >= 0.47d && queryAndFrequency._2 <= 0.53d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "c ^ d" &&
          queryAndFrequency._2 >= 0.47d && queryAndFrequency._2 <= 0.53d  // TODO: occasionally fails (interval too small?)

      }))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Weight rule test 1"))) { //  --------------------------------------------------------------------

      /*

        a :- 3 <= #sum {3,x:b; 2,y:c; 2,z:d}.  % recall that { } has set semantics in clingo, so we need x,y,z to sum or count the same value multiple times

        c.
        d.

        One answer set { a c d }.

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("a"), bodyLiterals = Set(),
          weightBodySymbolicOpt = Some((3 /*lower bound*/ ,
            Seq((3, "b"), (2, "c"), (2, "d")))))


        , GroundSymbolicASPRule(headLiterals = Set("c"), bodyLiterals = Set())
        , GroundSymbolicASPRule(headLiterals = Set("d"), bodyLiterals = Set())
      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a", "c", "d")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ c ^ d" &&
          queryAndFrequency._2 == 1d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Choice rule test 1"))) { //  --------------------------------------------------------------------

      /*

        {a,b} :-.

        Four answer sets {}, { a }, { b }, { a, b }

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set(),
          choiceHeadOpt = Some(Seq("a", "b"))
        )

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("a"), Seq("b"), Seq("a", "b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b" &&
          queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a ^ b" &&
          queryAndFrequency._2 > 0d

      })

      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Choice with weight rule test 1"))) { //  --------------------------------------------------------------------

      /*

        {p;q} :- 3 <= #sum {3,x:b; 2,y:c; 2,z:d}.
        b.

        Four answer sets { b }, { b q }, { b p }, { b p q }

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set(),

          choiceHeadOpt = Some(Seq("p", "q")),

          weightBodySymbolicOpt = Some((3 /*lower bound*/ ,
            Seq((3, "b"), (2, "c"), (2, "d"))))

        )
        , GroundSymbolicASPRule(headLiterals = Set("b"), bodyLiterals = Set())

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("b"), Seq("b", "p"), Seq("b", "p", "q"), Seq("not b")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b" && queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b ^ p" && queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b ^ p" && queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "b ^ p ^ q" && queryAndFrequency._2 > 0d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "not b" && queryAndFrequency._2 == 0d

      })

      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "_pr_() test 1"))) { //  --------------------------------------------------------------------

      /*

        {p} :-.
        _pr_(p, 5000).

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set(), choiceHeadOpt = Some(Seq("p")))
        , GroundSymbolicASPRule(headLiterals = Set("_pr_(p,3333)"), bodyLiterals = Set())

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = true,
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = sampled.modelsSymbolic.length == 500 && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p" && queryAndFrequency._2 > 0.32d && queryAndFrequency._2 < 0.34d

      })

      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "_pat_ and _cost_() test 1"))) { //  --------------------------------------------------------------------

      /*

      _pat_(h).

      0{h}1.

      e1 :- h.  % e1, e2 and e3 are so-called measured atoms (measured variables). h is a parameter atom.
      e2 :- h.
      e3 :- h.

      _cost_("abs(0.5 - (f(e1) * f(e2) * f(e3)))").

       */

      val rules: Set[GroundSymbolicASPRule] = Set(

        GroundSymbolicASPRule(headLiterals = Set("_pat_(h)"), bodyLiterals = Set())
        , GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set(), choiceHeadOpt = Some(Seq("h")))
        , GroundSymbolicASPRule(headLiterals = Set("e1"), bodyLiterals = Set("h"))
        , GroundSymbolicASPRule(headLiterals = Set("e2"), bodyLiterals = Set("h"))
        , GroundSymbolicASPRule(headLiterals = Set("e3"), bodyLiterals = Set("h"))
        , GroundSymbolicASPRule(headLiterals = Set("_cost_(\"abs(0.5 - (f(e1) * f(e2) * f(e3)))\")"), bodyLiterals = Set())

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = false, /* ! */
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("h"), Seq("e1"), Seq("e2"), Seq("e3"), Seq("e1", "e2", "e3")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = {

        val prHHH = Math.pow(adHocConjunctiveQueriesResults.find(_._1 == "h").get._2, 3)

        prHHH > 0.45d && prHHH < 0.55d

      }
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test background knowledge + additional rules 1"))) { //  --------------------------------------------------------------------

      val rules: Set[GroundSymbolicASPRule] = Set(

        /*
        not not p :- q.
        p :- not not p.
        q :- not not q.

        Three answer sets { }, { p }, { p q }.
        */

        GroundSymbolicASPRule(headLiterals = Set("not not p"), bodyLiterals = Set("q"))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not not p"))
        , GroundSymbolicASPRule(headLiterals = Set("q"), bodyLiterals = Set("not not q"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 500,
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = None,
        assureMSE = false, /* ! */
        showauxInSATmode = false, advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = Some(
        """

        asp 1 0 0
        1 0 2 2 -2 0 1 1
        1 0 1 1 0 0
        4 1 a 1 1
        4 1 b 1 2
        0

              """.trim.split('\n').map(_.trim).mkString("\n") // trailing space not allowed in aspif lines

      )).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = true,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p"), Seq("q"), Seq("p", "q"), Seq("a"), Seq("p", "q", "a")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "a" && queryAndFrequency._2 == 1d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test probabilistic rules 1"))) { //  --------------------------------------------------------------------

      val rules: Set[GroundSymbolicASPRule] = Set(

        /*
            [0.9] p.
            [0.3] nope.

            [0.7] z.
            [0.1] zz.

            p :- nope.

            :- z, zz.

            p :- z.
        */

        GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set(), probabilityOpt = Some(0.9d))
        , GroundSymbolicASPRule(headLiterals = Set("nope"), bodyLiterals = Set(), probabilityOpt = Some(0.3d))
        , GroundSymbolicASPRule(headLiterals = Set("z"), bodyLiterals = Set(), probabilityOpt = Some(0.7d))
        , GroundSymbolicASPRule(headLiterals = Set("zz"), bodyLiterals = Set(), probabilityOpt = Some(0.1d))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("nope"))
        , GroundSymbolicASPRule(headLiterals = Set(), bodyLiterals = Set("z", "zz"))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("z"))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until loss threshold has been reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(0.001d), // the desired accuracy (lower = more accurate)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("p"), Seq("nope"), Seq("z"), Seq("zz")),
        adHocDisjunctiveQueries = Seq(),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p" && queryAndFrequency._2 >= 0.85d && queryAndFrequency._2 <= 0.95d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "nope" && queryAndFrequency._2 >= 0.25d && queryAndFrequency._2 <= 0.35d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test probabilistic rules 2"))) { //  --------------------------------------------------------------------

      val rules: Set[GroundSymbolicASPRule] = Set(

        /*
            [0.73] p :- q.
            {p}. % a so-called spanning rule for p [Nickles,Mileo'15]
            {q}.
        */

        GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("q"), probabilityOpt = Some(0.73d))
        , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("p")))
        , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("q")))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until loss threshold has been reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-10d), // the desired accuracy (lower = more accurate but slower)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(Seq("not q", "p")),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocDisjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "not q v p" && queryAndFrequency._2 == 0.73d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test probabilistic rules 3"))) { //  --------------------------------------------------------------------

      val rules: Set[GroundSymbolicASPRule] = Set(

        /*
            [0.7] p :- not q.
            {p}.
            {q}.
        */

        GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not q"), probabilityOpt = Some(0.7d))
        , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("p")))
        , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("q")))

      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until loss threshold has been reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-10d), // the desired accuracy (lower = more accurate but slower)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(Seq("q", "p")),
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocDisjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "q v p" && queryAndFrequency._2 == 0.7d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test probabilistic rules 4"))) { //  --------------------------------------------------------------------

      val b2pr = (Seq("p", "v"), 0.9d) // must be >= (ca.) 0.8 or else probabilistic inconsistency

      val rules: Set[GroundSymbolicASPRule] = Set(

        /*
            [0.2] v.
            [0.9] u :- p, v.
            [0.5] p :- not q.
        */

        GroundSymbolicASPRule(headLiterals = Set("v"), bodyLiterals = Set(), probabilityOpt = Some(0.2d))
        , GroundSymbolicASPRule(headLiterals = Set("u"), bodyLiterals = b2pr._1.toSet, probabilityOpt = Some(b2pr._2))
        , GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not q"), probabilityOpt = Some(0.5d))
      )

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until loss threshold reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-5d), // the desired accuracy (lower = more accurate but slower)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(Seq("v")),
        adHocDisjunctiveQueries = Seq(),
        adHocSimpleGroundRuleQueries = Seq(("u", b2pr._1), ("p", Seq("not q"))),
        printAdHocQueryResults = true,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "v" && queryAndFrequency._2 >= 0.19d && queryAndFrequency._2 <= 0.21d

      }) && adHocRuleQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "u:-" + b2pr._1.mkString(",") && queryAndFrequency._2 >= b2pr._2 - 0.01d && queryAndFrequency._2 <= b2pr._2 + 0.01d

      }) && adHocRuleQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "p:-not q" && queryAndFrequency._2 >= 0.49d && queryAndFrequency._2 <= 0.51d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test 1"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        /*

          d(a,b).
          d(a,c).
          d(c,a).

          foo(X,Y,Z) :- d(X,Y), d(Y,Z), not bar(X,Y,Z).
          bar(X,Y,Z) :- d(X,Y), d(Y,Z), not foo(X,Y,Z).

          Grounding obtained using clingo --text (which omits ground facts in bodies).
          (the grounding shown in the lparse 1.0 documentation is wrong):

            d(a,b).
            d(a,c).
            d(c,a).
            foo(c,a,b):-not bar(c,a,b).
            foo(c,a,c):-not bar(c,a,c).
            foo(a,c,a):-not bar(a,c,a).
            bar(c,a,b):-not foo(c,a,b).
            bar(c,a,c):-not foo(c,a,c).
            bar(a,c,a):-not foo(a,c,a).

       */

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly.
          "d(a,b)",
          "d(a,c)",
          "d(c,a)"
        )

        SymbolicASPRule(headLiterals = Set("foo(X,Y,Z)"), bodyLiterals = Set("d(X,Y)", "d(Y,Z)", "not bar(X,Y,Z)"),
          domainAtoms = domainAtoms).genGroundInstances ++
          SymbolicASPRule(headLiterals = Set("bar(X,Y,Z)"), bodyLiterals = Set("d(X,Y)", "d(Y,Z)", "not foo(X,Y,Z)"),
            domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      //println("\n------------- Grounding:\n" + rules.mkString("\n"))

      val expectedGrounding =
        """
             bar(c,a,c) :- d(c,a),d(a,c),not foo(c,a,c).
             foo(c,a,c) :- d(c,a),d(a,c),not bar(c,a,c).
             foo(a,c,a) :- d(a,c),d(c,a),not bar(a,c,a).
             foo(c,a,b) :- d(c,a),d(a,b),not bar(c,a,b).
             bar(c,a,b) :- d(c,a),d(a,b),not foo(c,a,b).
             bar(a,c,a) :- d(a,c),d(c,a),not foo(a,c,a).
             """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Grounding test 2"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        /*
           fly(X) :- bird(X), not neg_fly(X).
       */

        SymbolicASPRule(headLiterals = Set("fly(X)"), bodyLiterals = Set("bird(X)", "not neg_fly(X)"),
          domainAtoms = Seq(
            /* ("X", "tweety"),
             ("X", "tux")*/
            "bird(tweety)"
          )).genGroundInstances

      }.toSet

      //println("\n------------- Groundings:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
      fly(tweety) :- bird(tweety),not neg_fly(tweety).
      """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test 3"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        SymbolicASPRule(headLiterals = Set("p(X,Y)"), bodyLiterals = Set("p(X)", "not q(Y)"),
          variableBindings = Seq(
            ("X", "a"),
            ("Y", "b"),
            ("X", "c"), // this one is ignored since X already bound to X. In contrast to domainAtoms, variableBindings
            // are processed linearly.
          ),
          /* domainAtoms = Seq(
             "bird(flappy)"
           )*/).genGroundInstances

      }.toSet

      println("\n------------- Groundings:\n" + groundRules.mkString("\n"))


      val expectedGrounding =
        """
      p(a,b) :- p(a),not q(b).
      """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test 4"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        SymbolicASPRule(headLiterals = Set("p(f(X),Y)"), bodyLiterals = Set("p(f(X))", "not q(Y)"),
          variableBindings = Seq(
            ("X", "a"),
            ("Y", "f(b)"),
            ("X", "c"), // this one is ignored since X already bound to a at that point. In contrast to domainAtoms, variableBindings
            // are processed linearly.
          ),
          /* domainAtoms = Seq(
             "bird(flappy)"
           )*/).genGroundInstances

      }.toSet

      //println("\n------------- Groundings:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
      p(f(a),f(b)) :- p(f(a)),not q(f(b)).
      """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test 5"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        SymbolicASPRule(headLiterals = Set("w(f(X),f(Y))"), bodyLiterals = Set("p(f(X))", "not q(f(Y))"),
          variableBindings = Seq(),
          domainAtoms = Seq(
            "p(f(a))",
            "q(f(b))"
          )).genGroundInstances

      }.toSet

      println("\n------------- Groundings:\n" + groundRules.mkString("\n"))


      val expectedGrounding =
        """
      w(f(a),f(b)) :- p(f(a)),not q(f(b)).
      """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))


    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "Grounding test 6"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        /*

          d(a,b).
          d(a,c).
          d(c,a).

          foo(X,Y,Z) :- d(X,Y), d(Y,Z), not bar(X,Y,Z).
          bar(X,Y,Z) :- d(X,Y), d(Y,Z), not foo(X,Y,Z).

          Grounding obtained using clingo --text (which omits ground facts in bodies).
          (the grounding shown in the lparse 1.0 documentation is wrong):

            d(a,b).
            d(a,c).
            d(c,a).
            foo(c,a,b):-not bar(c,a,b).
            foo(c,a,c):-not bar(c,a,c).
            foo(a,c,a):-not bar(a,c,a).
            bar(c,a,b):-not foo(c,a,b).
            bar(c,a,c):-not foo(c,a,c).
            bar(a,c,a):-not foo(a,c,a).

       */

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly.
          "d(a,b)",
          "d(a,c)",
          "d(c,a)"
        )

        SymbolicASPRule(headLiterals = Set("foo(X,Y,Z)"), bodyLiterals = Set("d(X,Y)", "d(Y,Z)", "not bar(X,Y,Z)"),
          domainAtoms = domainAtoms).genGroundInstances ++
          SymbolicASPRule(headLiterals = Set("bar(X,Y,Z)"), bodyLiterals = Set("d(X,Y)", "d(Y,Z)", "not foo(X,Y,Z)"),
            domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
      bar(c,a,c) :- d(c,a),d(a,c),not foo(c,a,c).
      foo(c,a,c) :- d(c,a),d(a,c),not bar(c,a,c).
      foo(a,c,a) :- d(a,c),d(c,a),not bar(a,c,a).
      foo(c,a,b) :- d(c,a),d(a,b),not bar(c,a,b).
      bar(c,a,b) :- d(c,a),d(a,b),not foo(c,a,b).
      bar(a,c,a) :- d(a,c),d(c,a),not foo(a,c,a).
      """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test grounding with probabilistic rules 1"))) { //  --------------------------------------------------------------------

      val domainAtoms = Seq("p(a)", "p(b)")

      val uncertainNongroundRuleGroundings: Seq[GroundSymbolicASPRule] = SymbolicASPRule(
        headLiterals = Set("p(X)"),
        bodyLiterals = Set("not q"),
        domainAtoms = domainAtoms,
        probabilityOpt = Some(0.7d),
        distrPrOverGroundings = false).genGroundInstances

      println("\n------------- Grounding of uncertain rule:\n" + uncertainNongroundRuleGroundings.mkString("\n"))


      val groundRules: Set[GroundSymbolicASPRule] = {
        /*
            #domain p(a), p(b)

            [0.7] p(X) :- not q.
            {p(a)}.
            {p(b)}.
            {q}.
        */


        uncertainNongroundRuleGroundings ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(a)"))).genGroundInstances ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(b)"))).genGroundInstances ++
          Seq(GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("not q"))))

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until loss threshold has been reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-20d), // the desired accuracy (lower = more accurate but slower)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(groundRules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults,
      adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        adHocConjunctionOfSimpleGroundRulesQuery = Seq(("p(a)", Seq("not q")), ("p(b)", Seq("not q"))), // we use
        // adHocConjunctionOfSimpleGroundRulesQuery because distrPrOverGroundings = false in the grounding of the
        // probabilistic rule.
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctionOfSimpleGroundRulesQuery)

      singleTestResult(success = !adHocConjunctionOfSimpleGroundRulesQuery.isEmpty && adHocConjunctionOfSimpleGroundRulesQuery.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._2 == 0.7d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Test grounding with probabilistic rules 2"))) { //  --------------------------------------------------------------------
      // Same as "Test grounding with probabilistic rules 1", but now we attach the probabilistic weight to each
      // ground instance of the nonground rule individually. Since diff-SAT doesn't enforce or use any knowledge about
      // event independence, we sample a larger than necessary number of models and use diversify=true. If
      // we wouldn't do this, we would still get the correct result (0.7 for p(a) :- not q and 0.7 for p(b) :- not q),
      // but we would "accidentially" also get 0.7 for (p(a) :- not q) ^ (p(b) :- not q), i.e., the same result as with
      // distrPrOverGroundings = true, because diff-SAT would see the two events (p(a) :- not q) and (p(b) :- not q)
      // as completely and positively dependent simply because that's simpler for the sampling algorithm,
      // so we couldn't detect the impact of distrPrOverGroundings true vs. false.

      val domainAtoms = Seq("p(a)", "p(b)")

      val uncertainNongroundRuleGroundings: Seq[GroundSymbolicASPRule] = SymbolicASPRule(
        headLiterals = Set("p(X)"),
        bodyLiterals = Set("not q"),
        domainAtoms = domainAtoms,
        probabilityOpt = Some(0.7d),
        distrPrOverGroundings = true).genGroundInstances

      println("\n------------- Grounding of uncertain rule:\n" + uncertainNongroundRuleGroundings.mkString("\n"))


      val groundRules: Set[GroundSymbolicASPRule] = {
        /*
            #domain p(a), p(b)

            [0.7] p(X) :- not q.
            {p(a)}.
            {p(b)}.
            {q}.
        */


        uncertainNongroundRuleGroundings ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(a)"))).genGroundInstances ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(b)"))).genGroundInstances ++
          Seq(GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("not q"))))

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val solverParams = input.SolverParametersOverlay(
        noOfModels = 300 /*see above for why we don't use -1 here*/ , // -1 means sample until loss threshold has been reached
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-20d), // the desired accuracy (lower = more accurate but slower)
        assureMSE = true, // the cost function (which in this example is automatically generated from the probabilistic facts) are of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "true" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(groundRules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults,
      adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        adHocSimpleGroundRuleQueries = Seq(("p(a)", Seq("not q")), ("p(b)", Seq("not q"))), // this gives 0.7 per each ground rule
        adHocConjunctionOfSimpleGroundRulesQuery = Seq(("p(a)", Seq("not q")), ("p(b)", Seq("not q"))), // this should NOT give 0.7 (see explanation above).
        printAdHocQueryResults = false,
        printAnswers = false)

      //println(adHocRuleQueriesResults)

      //println(adHocConjunctionOfSimpleGroundRulesQuery)

      singleTestResult(success = !adHocConjunctionOfSimpleGroundRulesQuery.isEmpty && !adHocRuleQueriesResults.isEmpty &&
        adHocRuleQueriesResults.exists((queryAndFrequency: (String, Double)) => {

          queryAndFrequency._2 == 0.7d

        }) && !adHocConjunctionOfSimpleGroundRulesQuery.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._2 == 0.7d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test with choice rule 1"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        /*

          d(a,b).
          d(a,c).
          d(c,a).

          { d(X,Y); d(Y,Z) } :- q.  % NB: this would not be valid with gringo/clingo (X,Y,Z are unsafe). In contrast
          % to this, the much more basic diff-SAT grounder mechanically instantiates the variables using the domain facts.

       */

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly (e.g., as facts or body literals).
          "d(a,b)",
          "d(a,c)",
          "d(c,a)"
        )

        SymbolicASPRule(choiceHeadOpt = Some(Seq("d(X,Y)", "d(Y,Z)")), bodyLiterals = Set("q"),
          domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
          {d(a,c);d(c,a)} :- q.
          {d(c,a);d(a,c)} :- q.
          {d(c,a);d(a,b)} :- q.
             """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test with choice rule 2"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly (e.g., as facts or body literals).
          "d(a,f(b))",
          "d(f(b),g(a,c))"
        )

        SymbolicASPRule(choiceHeadOpt = Some(Seq("d(X,Y)", "d(Y,Z)")), bodyLiterals = Set("q"),
          domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      //println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
          {d(a,f(b));d(f(b),g(a,c))} :- q.
             """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test with choice rule 3"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly (e.g., as facts or body literals).
          "r(a,f(b),e)",
          "d(e,a,g(a,c))",
          "r(a,f(g,h),e)",
          "d(e,a,g(a,c))"
        )

        SymbolicASPRule(choiceHeadOpt = Some(Seq("r(X,Y,W)", "d(W,X,Z)", "ddd(W,X,Z)")), bodyLiterals = Set("q"),
          domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
          {r(a,f(b),e);d(e,a,g(a,c));ddd(e,a,g(a,c))} :- q.
          {r(a,f(g,h),e);d(e,a,g(a,c));ddd(e,a,g(a,c))} :- q.
             """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "Grounding test with weight body 1"))) { //  --------------------------------------------------------------------

      val groundRules: Set[GroundSymbolicASPRule] = {

        val domainAtoms = Seq( // observe that these are not automatically added to the knowledge base, so you would
          // have to add them as SymbolicASPRules explicitly (e.g., as facts or body literals).
          "r(a,f(b),e)",
          "d(e,a,g(a,c))",
          "r(a,f(g,h),e)",
          "d(e,a,g(a,c))"
        )

        SymbolicASPRule(choiceHeadOpt = Some(Seq("r(X,Y,W)", "d(W,X,Z)")),
          weightBodySymbolicOpt = Some((3 /*lower bound*/ ,
            Seq((3, "b"), (2, "c"), (2, "ddd(W,Y,Z)")))),
          domainAtoms = domainAtoms).genGroundInstances

      }.toSet

      println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val expectedGrounding =
        """
          {r(a,f(b),e);d(e,a,g(a,c))} :- 3<={List(3:b, 2:c, 2:ddd(e,f(b),g(a,c)))}.
          {r(a,f(g,h),e);d(e,a,g(a,c))} :- 3<={List(3:b, 2:c, 2:ddd(e,f(g,h),g(a,c)))}.
             """.split('\n').map(_.trim).filterNot(_.isEmpty).toSet

      val actualGrounding = groundRules.map(_.toString).toSet

      singleTestResult(expectedGrounding.equals(actualGrounding))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "User API usage example 1"))) { //  --------------------------------------------------------------------

       
      val rules: Set[GroundSymbolicASPRule] = Set(
         
            /*
                [0.7] p :- not q.  % rule has probability 0.7
                {q}. % we need this choice rule just to ensure predicate q is defined
                {p}.
             */
           
            GroundSymbolicASPRule(headLiterals = Set("p"), bodyLiterals = Set("not q"),
            probabilityOpt = Some(0.7d))
           , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("p")))
           , GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("q")))
           
           )
       
       
      val solverParams = input.SolverParametersOverlay(
          noOfModels = -1, // -1 means sample until desired accuracy (loss threshold) has been reached. A positive
          // number would specify a minimum sample size (in terms of number of answer sets).
            noOfSecondaryModels = 0,
          offHeapGarbageCollectionModeR = 0,
          thresholdOpt = Some(1e-5d), // the desired accuracy (lower = more accurate but sampling requires more time)
          assureMSE = true, // true = the loss function (which in this example is automatically generated from the probabilistic facts)
          // is assured to be of type MSE
            showauxInSATmode = false,
          advancedSolverArgs = mutable.HashMap[(String, Int), String](
           ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
             , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
             )
           )
       
        // Create the program from the rules and parameters and sample models:
       
      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(rules, backgroundProgramAspifOpt = None).
          solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)
       
        // Print sample and the result of ad hoc query Pr(q AND p):
       
      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults, adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
          satMode = false,
          samplingResult = sampled,
          adHocConjunctiveQueries = Seq(),
          adHocDisjunctiveQueries = Seq(),
          adHocConjunctionOfSimpleGroundRulesQuery = Seq(("p", Seq("not q"))),
          printAdHocQueryResults = false,
          printAnswers = false)

      singleTestResult(success = !adHocConjunctionOfSimpleGroundRulesQuery.isEmpty && adHocConjunctionOfSimpleGroundRulesQuery.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._2 == 0.7d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


    if (testHeader((collective, "User API usage example 2"))) { //  --------------------------------------------------------------------

      val domainAtoms = Seq("p(a)", "p(b)") // For grounding. Observe that these atoms don't automatically become facts or body literals.

      val uncertainNongroundRuleGroundings: Seq[GroundSymbolicASPRule] = SymbolicASPRule(
        headLiterals = Set("p(X)"),
        bodyLiterals = Set("not q"),
        domainAtoms = domainAtoms,
        probabilityOpt = Some(0.7d),
        distrPrOverGroundings = false  // with false, the probability applies to the entire non-ground rule.
        // With true (which might be more useful in practice), it would apply to each ground instance rule individually.
      ).genGroundInstances

      println("\n------------- Ground instances of [0.7] p(X) :- not q :\n" + uncertainNongroundRuleGroundings.mkString("\n"))


      val groundRules: Set[GroundSymbolicASPRule] = { // all ground rules of the program
        /*
              #domain p(a).
              #domain p(b).

              [0.7] p(X) :- not q.
              {p(a)}.
              {p(b)}.
              {q}.
          */

        uncertainNongroundRuleGroundings ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(a)"))).genGroundInstances ++
          SymbolicASPRule(choiceHeadOpt = Some(Seq("p(b)"))).genGroundInstances ++
          Seq(GroundSymbolicASPRule(choiceHeadOpt = Some(Seq("not q"))))


      }.toSet

      //println("\n------------- Grounding:\n" + groundRules.mkString("\n"))

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until desired accuracy (thresholdOpt) has been reached. A positive
        // number would specify a minimum sample size (number of answer sets).
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(1e-20d), // the desired accuracy (lower = more accurate but sampling requires more time)
        assureMSE = true, // true = the loss function (which in this example is automatically generated from the probabilistic facts)
        // is assured to be of type MSE
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
          ("seedRngGlobalR", 0) -> "-1" // uses a random PRNG seed seed for each run. Otherwise, we would get the same set of models at each call.
          , ("diversify", 0) -> "false" // "true" increases the entropy - with false, we might get a highly non-uniform distribution if there are no probabilities specified
        )
      )

      // Create the program from the rules and parameters and sample models:

      val sampled: SamplingResult = ProbabilisticAnswerSetProgram(groundRules, backgroundProgramAspifOpt = None).
        solve(solverParams, paramAtomsAndInnerCostsStrOpt = None)

      // Print sample and the result of ad hoc query Pr[p(a):-not q AND p(b):-not q]:

      val (_, adHocConjunctiveQueriesResults, adHocDisjunctiveQueriesResults, adHocRuleQueriesResults,
      adHocConjunctionOfSimpleGroundRulesQuery) = diffSAT.queryAndPrintSolverResult(showauxInASPmode = false,
        satMode = false,
        samplingResult = sampled,
        adHocConjunctiveQueries = Seq(),
        adHocDisjunctiveQueries = Seq(),
        adHocConjunctionOfSimpleGroundRulesQuery = Seq(("p(a)", Seq("not q")), ("p(b)", Seq("not q"))), // we use
        // adHocConjunctionOfSimpleGroundRulesQuery because distrPrOverGroundings = false in the grounding of the
        // probabilistic rule.
        printAdHocQueryResults = false,
        printAnswers = false)

      singleTestResult(success = !adHocConjunctionOfSimpleGroundRulesQuery.isEmpty && adHocConjunctionOfSimpleGroundRulesQuery.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._2 == 0.7d

      })
      )

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    if (testHeader((collective, "CNF formula with loss function, test 1"))) { //  --------------------------------------------------------------------

      /*
        1 -1 0
        2 -2 0
        -1 -2 0

        pats 1 2

        cost (0.2-f(v1))^2
        cost (0.5-f(v2))^2
        */

      val clause1 = BooleanClause(literals = Set(BooleanLiteral(1), BooleanLiteral(-1)))

      val clause2 = BooleanClause(literals = Set(BooleanLiteral(2), BooleanLiteral(-2)))

      val clause3 = BooleanClause(literals = Set(BooleanLiteral(-1), BooleanLiteral(-2)))

      val booleanFormula: BooleanFormulaWithCosts = BooleanFormulaWithCosts(Set(clause1, clause2, clause3))

      val probabilisticObjectives =  // Parameter atoms are "1" and "2". Atom "1" has probability 0.2, "2" has probability 0.5
        """pats 1 2

           cost (0.2-f(v1))^2
           cost (0.5-f(v2))^2
          """
        // (alternatively, cost terms can be constructed programmatically (see ParseOptimizationTerms to get an idea how to do
        // this, or use the ASP User API)

      val solverParams = input.SolverParametersOverlay(
        noOfModels = -1, // -1 means sample until desired accuracy (thresholdOpt) has been reached. A positive
        // number would specify a minimum sample size (number of answer sets).
        noOfSecondaryModels = 0,
        offHeapGarbageCollectionModeR = 0,
        thresholdOpt = Some(0.001d), // the desired accuracy (lower = more accurate but sampling requires more time)
        assureMSE = true, // true = the loss function is assured to be of type MSE (false works too but true is more efficient)
        showauxInSATmode = false,
        advancedSolverArgs = mutable.HashMap[(String, Int), String](
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
        printAdHocQueryResults = false,
        printAnswers = false)

      println(adHocConjunctiveQueriesResults)

      singleTestResult(success = adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "1" && queryAndFrequency._2 >= 0.15d && queryAndFrequency._2 <= 0.25d

      }) && adHocConjunctiveQueriesResults.exists((queryAndFrequency: (String, Double)) => {

        queryAndFrequency._1 == "2" && queryAndFrequency._2 >= 0.45d && queryAndFrequency._2 <= 0.55d

      }))

    } // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

    // TODO: more tests (e.g., from older unit tests in prasp2)

    // ================================================================================================================

    println("\n*************** API tests ended. ***************\n" +
      "Attempted: " + testAttempted + ", successful: " + testsSuccessful + ", failed: " + (testAttempted - testsSuccessful))

    if (testAttempted - testsSuccessful > 0)
      System.err.println("API tests FAILED")

    println

    sys.exit(0)

  }

}
