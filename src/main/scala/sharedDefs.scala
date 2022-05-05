/**
  * diff-SAT
  *
  * Copyright (c) 2018-2022 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

import java.lang.reflect.Field
import java.util.Random
import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.DifferentialFunction
import input.diffSAT.changeConsoleWidthUnderWin
import input.{UNSAFEhelper, diffSAT}

import scala.collection.mutable


/** Solver and sampler settings (and their default values), and some other global definitions.
  *
  * Generally, solver settings are provided either on the commandline (use --help to see all possible options) or
  * as a compound solver argument of type [[input.SolverParametersOverlay]].
  *
  * Among these, advanced settings (constructor argument advancedSolverArgs in SolverParametersOverlay or using --solverarg on
  * the commandline) correspond to value members of package object [[sharedDefs]].
  * More common settings, such as the sampling accuracy threshold, are set using dedicated constructor arguments in
  * [[input.SolverParametersOverlay]] and correspond to simple commandline parameters such as -n or -t.
  *
  * Those settings which are mutable (`var`) in sharedDefs can be overridden at runtime using the commandline
  * or the User API. '''Every `var` member in `sharedDefs` can be specified as an advanced solver parameter.
  * New `var` members added to this package object become available as settings automatically (using reflection).'''
  * Their default values are simply the initial values assigned in sharedDefs.scala.
  *
  * See [[input.ProbabilisticAnswerSetProgram]] for how to specify [[input.SolverParametersOverlay]] in your own code.
  *
  * ==Advanced settings on the commandline==
  *
  * From the diff-SAT commandline, most of the default values below (if the members are var's) can be changed using
  * --solverarg "paramName" "paramValue"
  *
  * Example: --solverarg maxSolverThreadsR 4
  *
  * Each --solverarg sets only a single parameter. If the param value is a Seq (that is, each solver thread uses
  * one of the seq elements as parameter), list the element values separated by space characters.
  *
  * Example: --solverarg freeEliSearchApproachP "12 3 11 3 3 7"
  *
  * Another example (for testing Stochastic Local Search (e.g., Walksat) in isolation):
  *  --solverarg rephasePhaseMemoP "true" --solverarg useSLSinPhaseMemoRephasingP "true" --solverarg allowEliToClarkReduciblesLookup true --solverarg maxInnerSLSTrials 200000000 --solverarg sasatOuterMaxInSLS 1 --solverarg minNoConflictsBeforeFirstRephasing 0 --solverarg rephasePhaseMemoIntervalInit 0 --solverarg maxSolverThreadsR 1
  *
  * Optionally, use --thread on the commandline to group --solverargs per solver thread (see --help in diffSAT.scala).
  * This is of course only relevant for settings which can differ across threads. Example:
  * --solverarg maxSolverThreadsR 4 ... --thread 3 --solverarg seedP 12345 --thread 4 --solverarg seedP -987654321
  * specifies seed 12345 for solver thread $3 and seed -987654321 for thread $4.
  * Such thread-specific command line arguments are merged into the defaults provided in sharedDefs.scala,
  * e.g., with the above the actual seedP value might become AlternativesForThreads(Map(0 -> -1, 3 -> 12345, 4 -> -987654321))
  *
  * For further commandline options (e.g., -n for specifying the size of the sample and -t to specify the accuracy threshold),
  * run diffSAT --help
  *
  * ==Important (see README.md for details)==
  * For standard (deductive-probabilistic MSE-style) inference problems, it is recommended to run diff-SAT with arguments#
  * -mse --solverarg "partDerivComplete" "false"
  * For non-MSE deduction-style inference where all parameter atoms are measured atoms, omit -mse and use --solverarg "partDerivComplete" "true"
  *
  * Settings annotated with @deprecated will probably be removed or substantially redesigned at some time in the future.
  *
  * ==Idiosyncrasies==
  *
  * Keep in mind that diff-SAT operates (after parsing) with nogoods, not with clauses as most other solvers. The use
  * of nogoods is inspired by clasp/clingo.
  *
  * In many places, the term ''eli'' is used; it denotes a numerical representation of a literal during solving.
  * An ''absEli'' is an eli with its sign removed. E.g., literal "not p" might be represented as eli -5 and its absEli is thus 5 (i.e., the same as eli of atom "p").
  *
  * ==Specifying solver or sampler settings using the User API==
  *
  * Settings available using --solverarg can also be speficied using the User API, using a key->value map in
  * field `advancedSolverArgs` in [[input.SolverParametersOverlay]]. Example:
  * {{{
  *    SolverParametersOverlay(
  *      noOfModels = -1, // a basic setting, corresponding to commandline argument -n
  *      noOfSecondaryModels = 0,
  *      offHeapGarbageCollectionModeR = 0,
  *      thresholdOpt = Some(1e-5d),
  *      assureMSE = true,
  *      showauxInSATmode = false,
  *      advancedSolverArgs = mutable.HashMap[(String, Int), String](
  *      // Advanced settings, corresponding to --solverarg's.
  *      // Any var value member of package object sharedDefs can be specified as first element in
  *      // first tuple (second element in first tuple denotes the solver thread if > 0). Format
  *      // of the string after -> is as explained for --solverarg
  *        ("seedRngGlobalR", 0) -> "-1",
  *        ("diversify", 0) -> "false"
  *      )
  *   )
  * }}}
  *
  * See [[input.ProbabilisticAnswerSetProgram]] and [[userAPItests.APITests]] for further examples.
  *
  * @see [[input.SolverParametersOverlay]], [[input.ProbabilisticAnswerSetProgram]], [[userAPItests.APITests]]
  *
  */
package object sharedDefs {

  val instance = this

  case class AlternativesForThreads[A](alternatives: Map[Int /*<-- Thread no, 0=any*/ , A]) {
    // Alternatives are sequences of values of type A, each element to be used by one solver thread.
    // In more detail:
    // Those of the following settings which use list type "AlternativesPerThread" are for configuring parallel portfolio solving
    // (with number of competing solver threads specified by maxSolverThreadsR) - each solver thread is assigned a combination
    // of values from the respective AlternativesPerThread(...) sequences.
    // With a limited number of solver threads, values earlier in sequences get higher priority to be used by a solver thread.
    // Position within AlternativesPerThread sequence determines priority.
    // Duplicate values allowed in a AlternativesPerThread.
    // Number of values in AlternativesPerThread can be smaller than number of solver threads.
    // If there is just one portfolio solver thread (see below), head of tuple is used.

    // All settings in sharedDefs with type AlternativesForThreads need to be added to class  SolverThreadSpecificSettings.

    def getAllAlternativeValues: Seq[A] =
      alternatives.map(x => x._2).toSeq // (this loses the associated thread)

    def getThreadOrDefaultValue(threadNo: Int): A =
      alternatives.getOrElse(threadNo, alternatives.getOrElse(0, {

        diffSAT.stomp(-10000, "No parameter value for thread " + threadNo + " or default found in AlternativesForThreads")

        alternatives.head._2 // dummy

      }))

    def getFirstOrDefaultValue: A = getThreadOrDefaultValue(1)

  }

  var areAssertionsEnabled = false

  assert({
    areAssertionsEnabled = true;
    true
  }) // sets assertionsEnabled=true if assertions are active (activate in build.sbt)

  @deprecated val extraChecks = false // for debugging only; enables additional checks of invariants or pre-/post-conditions which are
  // less important and/or very costly, slowing down the solver significantly

  val debug2 = false // use with small encodings only (generates a huge number of messages). TODO: messages mittels log() anzeigen; usable only for small problems, due to the very large amount of messages generated

  val debug = (areAssertionsEnabled || debug2) // (also see debugMode in class UNSAFEhelper for debugging off-heap garbage collection)

  var verbose = debug || debug2

  // -------------------------------------------------------------------------------------

  val noOfMinibenchmarkTrials = 1 // (don't use this for serious benchmarking - it just gives a rough estimate).
  // Trials don't include parsing and preparation.
  // > 1 enforces offHeapGarbageCollectionModeR=1, which carries some performance penalty.
  // Three trials will be added at beginning for warm-up.
  // NB (1): Running multiple trials may trigger offline as well as JVM garbage collections, which could make the average
  // trial duration larger than a single program run without benchmarking. Also observe that a difference
  // between multiple trials and computing multiple models is that the former don't allow for data structure reuse.
  //
  // NB (2): noOfMinibenchmarkTrials > 1 or runTimeoutBenchmarks=true disables sanity checks (even with runBatchTests=true)

  // -------------------------------------------------------------------------------------

  // There are several kinds of tests for diff-SAT:
  // 1) Batch tests (directories with .cnf, .aspif or .opt files which can optionally include expectations such as c #sat? false)
  //    activate like this: --batchtests \folder
  // 2) API tests in APITests
  //    activate with --apitests
  // 3) utests in prasp2 (deprecated)
  // 4) Sanity testing which checks models for violated nogoods/clauses. Two locations for this test exist (in solver threads and for end result)
  //    Activate using method performSanityChecks = true

  var runBatchTests = false

  var batchTestDir = "C:\\Users\\Owner\\workspaceScala211\\DelSAT\\batchTesting" // example folder - replace as appropriate
  // in the header of a test formula (e.g., .cnf file) using c #cdlargs are overridden by command line arguments in the diffSAT call.

  var batchTestFileEndings = Seq(".cnf", ".aspif", ".opt")

  var runAPITests = false // activate using --apitests

  var runTimeoutBenchmarks = false  /* activate using --timeoutbench  (not to be confused with noOfMinibenchmarkTrials)
   TODO: doesn't work well (piles up too much waste in memory). Use external script for benchmarking. */

  var timeoutBenchmarkDir = "C:\\Users\\Owner\\workspaceScala211\\DelSAT\\timeOutBenchmarks\\SAT11_application_track"  // example folder - replace as appropriate

  var timeoutBenchmarkTimeoutSec = 5

  var timeoutBenchmarkFileEndings = batchTestFileEndings

  @inline def performSanityChecks: Boolean = (runBatchTests || (debug || areAssertionsEnabled || extraChecks)) &&
    noOfMinibenchmarkTrials == 1 && !runTimeoutBenchmarks // NB: for ASP, any invalid models are first bounced back to
  // the solver before this check could occur (see SolverMulti.scala).
  // NB: enforceSanityChecks currently doesn't check UNSAT results yet.

  // -------------------------------------------------------------------------------------

  val maxAssumedConsoleWidth = if(debug) 1024 else if (diffSAT.osWin && changeConsoleWidthUnderWin) 210 /*with Windows, we programmatically change the
  width to this*/ else /*79*/90 // to ensure single-line progress (status) updates correctly (if buffer width too small, console scrolls). Set to 0 to disable.

  var showProgressStats: Boolean = true // switch off progress statistics using --solverarg showProgressStats false
  // (Also see setting enforceProgressChecksEveryTrialsR)

  // -------------------------------------------------------------------------------------

  val offHeapGarbageReleaseThreshold: Float = 0.7f // free off-heap garbage if estimated remaining free off-heap memory falls below this fraction

  // -------------------------------------------------------------------------------------

  var enforceWriteRuntimeStatsToFileOpt: Option[Boolean] = None

  @inline def writeRuntimeStatsToFile: Boolean = enforceWriteRuntimeStatsToFileOpt.getOrElse(false) //.getOrElse(runBatchTests || debug || debug2 || noOfMinibenchmarkTrials > 1)

  // if true, each run writes configuration information and runtime statistics
  // to a local file in writeToHistoryDirector for debugging and benchmarking purposes. Also see switch --writestatsto <dir>

  val flushRuntimeStatsEverySec = 5 // frequency (in sec) at which runtime stats are flushed to file (if writeRuntimeStatsToFile=true)

  var writeStatsDirectory = "C:/Users/Owner/workspaceScala211/DelSAT/history/" // also see switch --writestatsto <dir>

  // -------------------------------------------------------------------------------------

  assert(!debug2 || debug)

  if (areAssertionsEnabled)
    println("Assertions enabled")

  if (debug)
    println("debug = true")

  if (debug2)
    println("debug2 = true")

  if (extraChecks)
    println("deepChecks = true\n")

  if (performSanityChecks)
    println("performSanityChecks = true\n")

  //@inline def graal: Boolean = System.getProperty("java.vendor.url").toLowerCase.contains("graal") // println("graal = " + graal)  // nope, graal won't set or print that here

  def printAnswers: Boolean = !runTimeoutBenchmarks && !runBatchTests && !suppressAnswers && noOfMinibenchmarkTrials == 1 //&& !enforceSanityChecks // false only for debugging purposes

  @deprecated val showIntermediateTimers = false || debug2

  // Advanced solver/sampler settings =================================================================================================

  /** true allows the reentry of the inner SAT solver loop using the data structures from the previous iteration
    * true requires switchToBestConfigAfterFirstModel=2. Should normally be true.  */
  var reuseSolverData: Boolean = true

  /** if true, multi solver aims at generating diverse models (i.e., models which are largely different from each other).
    * Might slow down solver (but not necessarily). Might override other settings. NB: Doesn't ensure near-uniform sampling! Also, distribution-aware sampling still takes place if parameter atoms are present. */
  var diversify: Boolean = false

  /** Effect is similar but less pronounced effect compared with diversify, faster. Should normally be true. */
  var diversifyLight: Boolean = true

  /** if true (=default since 0.4.1), a discrete form of numerical differentiation is used instead of symbolic or automatic differentiation
    * is used to compute the partial derivatives wrt. parameter atoms.
    * Slower and less accurate (you might need to increase the cost threshold with -t), but necessary if a parameter atom variable is
    * not part of the cost function term (or symbolic/automatic differentiation wrt some parameter atom variable isn't possible for some other reason). */
  var allowNumFiniteDiff: Boolean = true

  /** if true (default), even with allowNumFiniteDiff=true, autom. or symbol. differentiation is
    * used where possible (i.e., for those parameter variables which are measured). With false, a purely numerical differentiation
    * approach is used. True is typically - but not always! - much faster than false. */
  var mixedScenario: Boolean = true

  /** false: variant of ILP'18 approach (less general, use with MSE-style inner cost expressions),
    * true: variant of PLP'18 approach (more general). Some non-MSE-style problems can only be solved with true here.
    */
  var partDerivComplete: Boolean = false

  /** n != 1 for parallel portfolio solving with competing solver instances (specified number of threads not guaranteed)
    * Keep in mind that the machine might decrease maximum core frequencies with more cores being utilized.
    * -x sets number of solver threads in dependency of number of cores, problem size and other factors, with an upper limit of upperLimitAutoSolverThreads.
    * For small problems with number of positive literals (i.e., in case of SAT: #variables) smaller -x (with x < 0), only a single solver thread is launched.
    * NB: diff-SAT also spawns some parallelism from within individual solver threads, so normally no all cores should be occupied by solvers.
    * Commandline: --solverarg maxSolverThreadsR n */
  var maxSolverThreadsR: Int = -1

  /** Upper limit for automatically determined number of solver threads if maxSolverThreadsR < 0 */
  var upperLimitAutoSolverThreads: Int = 999999999

  /** If not empty, only the specified threads will be executed. All other threads will be ignored.
    * E.g., if a total of 6 threads are specified using maxSolverThreadsR and threadSelect = Seq(2,3),
    * only threads $2 and $3 are actually started, whereas $1 and $4 are omitted.
    * First thread has index 1 */
  var threadSelect: Seq[Int] = Seq()

  /** if true, we stop sampling if the total cost doesn't significantly change anymore and
    * at least the requested number of models (switch -n) have been generated. Useful mostly for learning weights. However, in
    * deductive-probabilistic and mixed scenarios, cost stagnation before reaching the threshold can
    * also indicate that the input is inconsistent (no solution exists)). */
  var stopSamplingOnStagnation: Boolean = false

  /** if multiple cost terms are specified, this function is used to combine (reduce) them
    * to a single total cost, after also dividing by the number of inner cost functions.
    * Try, e.g., Product instead of Sum if the inner costs are terms referring only to example facts which are mutually probabilistically independent. */
  var innerCostReductFun = (r: DifferentialFunction[DoubleReal], x: DifferentialFunction[DoubleReal]) =>
    new com.accelad.math.nilgiri.autodiff.Sum[DoubleReal](r, x)

  // NB: In the following AlternativesForThread typed values, e.g., Map(0 -> x, 1 -> y)  means that the first thread
  // gets by default value y and all other threads get by default value x. So thread indices start with 1, not 0.
  // Override on the commandline with, e.g., --thread 1 --solverarg ... z

  /** Seed for the global PRNG. -1L: use a pseudo-random seed
    * In the current diff-SAT version, the number below is used as default (may change in newer versions!).
    * Use -1L for a pseudo-randomly choosen global PRNG seed.
    * NB: it's useful to fix a certain seed (for reproducibility and in particular for debugging and development) but keep in
    * mind that any additional or omitted consumption of a random number before obtaining the thread-local PRNG seeds from
    * the global PRNG leads to a different runtime performance. See threadPRNGSeedPool to mitigate this issue.
    * Still, even with a fixed seed, there may be sources of run time unpredictability, such as thread synchronization.
    * Also see parameters maxSolverThreadsR and threadSelect */
  var seedRngGlobalR: Long = 0L //42L //-1L

  /** Seed for thread-local pseudo-random number generator (PRNG)
    * in an individual solver thread. -1l: use a random seed generated by the global PRNG, i.e., determined by seedRngGlobalR.
    * Values != -1 cannot be used with diversify (see below). Also observe that a seed != -1l doesn't guarantee
    * deterministic results if multithreading is active (because of the unpredicability of thread scheduling which influences
    * access to data which is shared among threads, such as bestPhase, or sharing of learned nogoods).
    * Also see newSeedOnRestart. */
  var seedP: AlternativesForThreads[Long] = AlternativesForThreads[Long](Map(0 -> -1l))

  /** See source code - On the commandline, specify like this (no sequences allowed then): --solverarg "restartTriggerConfP" "3 4 256"
    * Remarks:
    * - for detecting UNSAT (not diff-SAT's focus), a higher frequency of restarts is often desirable
    * - another way to trigger (additional) restarts is using parameter slowThreadAction (see further below).
    * - reusedTrailRestartsR = false increases number of restarts. */
  var restartTriggerConfP: (AlternativesForThreads[Int], Seq[Int], Seq[Double]) = (AlternativesForThreads[Int](Map(0->3, 2->2)) /*
    0=no restarts, 1=fixed interval, 2=geometric (regular or inner-outer scheme, see outerGeom), 3=Luby. Try with 3 first if unsure.
    Each of these possibly combined with Glucose-style schedule or adapting factor (see
    restartsFactModifierP below; changes the multiplier and restart condition), e.g., fixed interval with restartsFactModifierP = on
    effectively means a Glucose-style restart policy*/ ,
    Seq(0, /*for approach 1 (fixed):*/ 50, /*for approach 2 (geom):*/ 100 /*<- MiniSAT 2: 100*/ ,
      /*for approach 3 (Luby) this param is meaningless:*/ -1) /*per approach in ._1: initial # of conflicts
    before the first restart (without considering multipliers), or fixed restart interval in case of restartPolicy=1.
    Recommendation: try first ca. 8 with geometric or ca. 50 with fixed interval*/ ,
    Seq(0d, /*for approach 1 (fixed):*/ 1d, /*for approach 2 (geom):*/ 2d/*1.02d*/
      /*<- MiniSAT 2: 2, but observe
          reusedTrailRestartsR. Also might need to be adapted if parameter outerGeom is used*/ ,
      /* "luby unit factor" for approach 3:*/ 256d /*256d*/) /* per approach
    in ._1: multipliers, multiplied also(!) with restartsFactModifier (see below).
    Suggestion: try for ._3 first with about 2 or 4 for geom, and a value between 64 and 512 with Luby */ )

  /** See source code - Global restart frequency scaling. Higher absolute value = fewer restarts.
    * If x<0f, a variant of Glucose 4-EMA style restarts is used (Biere et al, POS 2015).
    * Since the Glucose-style-criterion adds to the regular restart decision criteria, you should normally choose
    * an absolute value lower than 1 in that case, such as -0.98f.
    * More precisely, if x<0, Glucose-style-conditions for restarts are considered after the |x| * restart-triggering number of conflicts according restartTriggerConfP have been encountered.
    * In any case, value ._3 is actually use multiplied with |x|. E.g., if x = 0.7 and if geometric restarts are active and in restartTriggerConf
    * value _3 for geometric restarts is 2.5d, the actual multiplier is 2.5*0.7.
    * !! This or alternatively restartTriggerConf might have to be adapted depending on localRestarts=true/false. */
  var restartFrequencyModifierFactorP: AlternativesForThreads[Float] = AlternativesForThreads[Float](Map(0-> -0.5f, 1 -> 0.1f, 5 -> 1f, 8 -> -0.98f/*0 -> -0.5f, 2 -> 1f, 5 -> 1f, 8 -> -0.98f*/
    /*-0.98f*/))

  /** The initial "outer" value for the inner-outer restart scheme. Only used if geometric restarts are
    * active (see restartTriggerConf). Use Double.MaxValue to deactivate (simple geometric sequence). */
  var outerGeom = 64d //Double.MaxValue // 128d

  /** lower bound to avoid that the number of restarts grows too fast. */
  val lowerBoundForNoOfConflictsBeforeRestart = 12

  /** True has an effect with freeEliSearchConfig=11/14/15 only, otherwise true is ignored.
    * Might somewhat negatively influence learned nogood deletion performance. */
  var reusedTrailRestartsR = true

  /** TODO: Needs to be true (does it? If yes why?).  :::
    * Older: Cannot be combined with removeLearnedNogoodAtRegularRestarts=true. Remark: If localRestarts = true, the trigger value for restarts might
    * have to be changed with restartTriggerConfP or restartsGlucoseAndFactorModifierP or localRestartsTriggerThreshFactor. */
  var localRestartsP: AlternativesForThreads[Boolean] = AlternativesForThreads[Boolean](Map(0 -> true))

  /** if localRestarts=true, this specifies the threshold with which the current number of
    * conflicts before a restart according to restartTriggerConfP is multiplied. Must be >= 1.
    * Same effect can be achieved by changing restartsGlucoseAndFactorModifierP or restartTriggerConfP, but
    * all three settings are applied independently. */
  val localRestartsTriggerThreshFactor = 10 // TODO: check code

  /** 1: set a new random seed for the thread-local pseudo-random number
    * (generated using the global PRNG) at each restart,
    * 2: resets PRNG using the original thread-local seed,
    * 0: don't reset PRNG at restarts
    */
  val resetLocalPRNGonRestart: Int = 0

  /** Data structure for (non-probabilistic) branching heuristics ("free eli search"), for conventional branching (i.e., where
    * choice isn't for parameter atoms for which it is determined by the differentiable cost function).
    * On the commandline, specify like this: --solverarg "freeEliSearchApproachP" "15 11 7 13 12 7" with a >=6-core machine (NB: this *doesn't* specify the
    * number of solver threads which has to be set using maxSolverThreadsR)
    * Available approaches:
    *
    * 7: Linear search without(!) regard to absEli scores. Search direction: see initAbsElisArrangementP
    * 8: Linear search but using absEli scores. Search direction: see initAbsElisArrangementP
    * 7 and 8 are deprecated
    * 9: Sorted tree set, with order defined by absEli scoring
    * 11: Priority queue, with backing heap order defined by absEli scoring (like MiniSat and most SOTA SAT solvers)
    * 12: Tiered (decision level-wise) linear search without(!) absEli score consideration. Outcome depends on whether the search order profits from initAbsElisArrangementP
    * 13: As 12 but with absEli score consideration
    * 14: A heap based on an dual-indexed set. absEli scores are considered.
    * 15: Uses a kind of radix sort where the absEli scores are getting clustered (rounded) into bins. Search is linear over ordered bins.
    *
    * The search approaches are influenced by initAbsElisArrangementP and initialPhaseMemo, and of course
    * the order of the clauses in the input formula (the clauses and literals are sometimes in a "lucky" order).
    * Approaches 11 also uses initAbsElisArrangementP to initialize the scores.
    *
    * If unsure, try with 15 and 12 first, then 12 and 11 */
  var freeEliSearchApproachP: AlternativesForThreads[Int] = AlternativesForThreads[Int](
    Map(0 -> 15, 3 -> 12, 7 -> 12))

  /** For freeEliSearchApproach 15. Should normally be between (about) 12 and 100. See getBinFromScoreForFreeEliSearchApproach15() for
  the mapping from absEli scores to bin indices. */
  var absEliScoringApproach15NoOfBinsP: AlternativesForThreads[Int] = AlternativesForThreads(Map(0 -> 64, 5 -> 12, 6 -> 20))

  /** Literal scoring approach for regular (non-parameter atom) branching heuristics (such as LRB) - see source code for details */
  var absEliScoringApproachP: AlternativesForThreads[Int] = AlternativesForThreads(Map(0 -> 2, 6 -> 0))
  // 0: EVSIDS (Minisat) or adaptVSIDS (Liang et al) -like approach but using nogoods instead of clauses and with some minor modfifications. adaptVSIDS is itself
  // based on EVSIDS (as in MiniSAT, PicoSAT and others)).
  // 1: variant of CHB (Liang et al)
  // 2: a variant of LRB (a form of learning rate maximization using MABs) (Liang et al: "Learning Rate Based Branching Heuristic for SAT Solvers")

  /** Only relevant if absEliScoringApproach=0, otherwise ignored; see source code for details.
    * If true and absEliScoringApproach=0: use approach like EVSIDS (like in Minisat and others) instead of adaptVSIDS */
  val evsids = false  // TODO: make this absEliScoringApproach 3

  val alphaInit = 0.3f // 0.4f  // for absEliScoringApproach 1 and 2

  val alphaTh = 0.08f //0.06f  // for absEliScoringApproach 1 and 2

  val alphaStep = 1e-6f //1e-6f // for absEliScoringApproach 1 and 2

  val updSc = 0.8f //0.95f  // for absEliScoringApproach 1 and 2

  /** if true: use RSR extension of LRB (for absEliScoringApproach==2) */
  val includeReasonedCountsInAbsEliScoringApproach2 = false

  /** if true, use locality extension (Liang et al) with absEliScoringApproach = 1,2 and freeEliSearchApproach 11,14,15 */
  val localityExt = true

  /** Must be a power of 2. For localityExt = true. Determines the downscaling frequency for absEli scores
      (higher = scale down less often but with larger scaling amount at each scaling event).
      Resacling is very costly, in particular with freeEliSearchApproach == 14 and freeEliSearchApproach == 15.
      In particular high impact on absEli score scaling in jumpBack() with localityExt=true.
    */
  var reduceScoreOfPassiveAbsElisWithLocalityExtEvery = 128 //128 //8

  @deprecated val binRangeMax = 1e20f //10000f  // currently not used

  val absEliScoreScaleBaseHigh = 0.99f //0.99f // for absEliScoringApproach = 0

  val absEliScoreScaleBaseLow = 0.75f //0.75f // for absEliScoringApproach = 0

  /** must be 1 or a power of 2 */
  val updateHeapInFreeElisPriorityQueueEvery = 2 //1  // for freeEliSearchConfigs == 11 and absEliScoringApproach != 0

  //  /** Rescale all absEli scores every x conflicts even if there was no overflow. Int.MaxValue = off */
  //val enforceRescalingOfAbsEliScoresEvery: Int = Int.MaxValue

  /** if true, elis with high decision levels are preferred as watched elis in learned nogoods */
  val moveElisWithHighDecisionLevelToFront = false

  val maxBCPPushInit = 65536 * 64 // internal use only; Initial max number of further literals (except parameter lits) assigned by a single BCP call following the assignment of a literal. Also see rndmIgnLearnedNogoodThresholdP

  /** If true, learned nogoods will be removed (only!) at every nth non-local restart, n being defined as reduceLearnedNogoodEveryNthRestart.
    * In other words, with true the nogood removal policy is identical with the restart policy (e.g., geometric, Luby...).
    * True might require change of other settings to work well (such as the restart frequency).
    * Cannot be combined with localRestarts. */
  val removeLearnedNogoodAtRegularRestarts: Boolean = false

  val checkLearnedNogoodRemovalEveryNconflicts: Int = 100

  /** Only used if removeLearnedNogoodAtRegularRestarts=true */
  val removeLearnedNogoodEveryNthRestart = 1

  val nogoodRemovalUsingRecyclingFromTotalHistoryEvery = 0
  /** if n > 0 (experimental), every n-th learned nogood
    * removal event, instead of removing a percentage x of the current set of learned nogoods, we make the (1-x) percent highest scored learned nogoods
    * from all times(*) the current set. Can be useful where the scoringForRemovalOfLearnedNogoods approach
    * allows for old learned nogoods to improve their scores over time.
    * (*) requires that freeOrReassignDeletedNogoodMemory=false, otherwise we might just recycle "old" nogoods
    * which in fact have been already replaced with newer nogoods.
    * 0 = deactivated. */

  /** Approximate percentage of learned nogoods which are removed at
    * each nogood reduction event. Upper bound since some nogoods cannot be remove.
    * Doesn't account for nogoods fetched from parallel solver threads.
    * 0 <= n < 1, attemps (without guarantee) to remove n% learned nogoods (scored according scoringForRemovalOfLearnedNogoodsR), but in any case
    * maximally all removable (i.e., not used as a reason for unit propagation) learned nogoods whose score is below the average score.
    * (minimum 1 and upper bound number of learned nogoods) if #learned nogoods > nogoodRemovalThresh.
    * 0: no removal of learned nogoods.
    * NB: removeLearnedNogoods doesn't include removal forced by inprocessing (e.g., by subsumption) unless emoveLearnedNogoods = 0. */
  var maxPercentToRemoveOfLearnedNogoods = 0.5d //0.5d

  /** If the number of learned nogoods grows above a threshold (see code) initialized with this value.
    * >>> No effect if removeLearnedNogoodAtRegularRestarts=true <<<
    * Observe that various other parameters also have an influence on the current number of learned nogoods,
    * such as freeEliSearchConfigs or restartTriggerConf.
    * The initial threshold changes according nogoodRemovalThreshRatioP.
    * If x > 0, x is directly the initial number of learned nogoods aimed for keeping. After x is reached,
    * an amount defined by maxPercentToRemoveOfLearnedNogoods is removed.
    * With x = 0, a Glucose-style nogood removal policy is use (behavior influenced by parameters baseGlucoseStyleNogoodRemovalStrategy and
    * factorGlucoseStyleNogoodRemovalStrategy).
    * If x < 0, a heuristic based on initial nogoods/variables weighted by -x is used (similar but different from Minisat, see code for details).
    * If x < 0, larger -x means fewer nogoods are removed.
    * This (and also nogoodRemovalThreshRatioP) is a pretty influencial parameter but no way to determine a good value automatically from the problem is known.
    */
  var nogoodRemovalThreshInitP: AlternativesForThreads[Int] = AlternativesForThreads(Map(0 -> -300, 3 -> 0, 5 -> 1024 * 12, 6 -> -600)) //-300 //1024*16  /** approach to determine removal of some amount of learned nogoods (see removeLearnedNogoods)

  /** base parameter for nogood deletion strategy nogoodRemovalThreshInit=0.
    * Lower value = nogood removal procedure called more frequently. No effect if removeLearnedNogoodAtRegularRestarts=true */
  var baseGlucoseStyleNogoodRemovalStrategy = 50000 //40000 //20000

  /** factor parameter for nogood deletion strategy nogoodRemovalThreshInit=0
    * for nogoodRemovalThreshInit=0. Lower value = nogood removal procedure called more frequently. No effect if removeLearnedNogoodAtRegularRestarts=true */
  var factorGlucoseStyleNogoodRemovalStrategy = 1000 //2850 //500

  /** Higher values >= 1 mean fewer learned nogoods will be removed.
    * Semantics: factor for geometric growth of learned nogood removal trigger threshold (1d = no changes).
    * No effect if nogoodRemovalThreshInit=0. No effect if removeLearnedNogoodAtRegularRestarts=true or nogoodRemovalThreshInit=0. */
  var nogoodRemovalThreshRatioP: AlternativesForThreads[Double] = AlternativesForThreads(Map(0 -> 1.05d, 6 -> 1.2d))

  /** starting value for number of conflicts after which adaption of nogoodRemovalThreshInit takes place (scheme as in MiniSAT)
    * Not for nogoodRemovalThreshInit=0. No effect if removeLearnedNogoodAtRegularRestarts=true. */
  var nogoodRemovalAdjustStartNoOfConflicts: Float = 100f

  /** Increment for number of conflicts after which adaption of nogoodRemovalThreshInit takes place (scheme as in MiniSAT)
    * Not for nogoodRemovalThreshInit=0.
    * Higher values <=> more learned nogoods will be removed.
    * No effect if removeLearnedNogoodAtRegularRestarts=true. */
  var nogoodRemovalAdjustInc: Float = 1.5f //1.5f

  // @deprecated val threshForPreFilterLearnedNogoods = 0d // 0.03d //Conflict nogoods below that nogood score are not added at all to the list of
  // learned nogoods (i.e., they are never used).

  /** Scoring approach of nogoods for learned nogood removal sweeps.
    *
    * Available approaches:
    *
    * 0: inverse LBD (Literals Blocks Distance, Audemard & Simon 2009) (also see setting keepGlue)
    * 1: nogood activity score
    * 2: inverse absEliScore (doesn't make much sense, just for debugging)
    * 3: absEliScore
    * 4: don't score nogoods (i.e., each nogood gets the same constant score)
    * 5: n/a
    * 6: n/a
    * 7: inverse nogood size (i.e., preferably shorted nogoods are kept, irrespective of LBD and activities)
    * 8: absEliScore weighted with inverse LBD
    * 9: inverse nogood size weighted with absEliScore
    * 10: n/a
    * 11: nogood activity weighted with inverse LBD
    *
    * For settings involving LBD also see parameter keepGlue.
    *
    * Suggestion: try with 11, 8, or 1 first
    */
  var scoringForRemovalOfLearnedNogoodsP = AlternativesForThreads(Map(/*0 -> 11, 6 -> 4, 12 -> 4*/0 -> 11))

  val maxLBD = 20

  val highestScoreForLearnedNogoodUpToSize = 2 // we always assign maximum (best) score to learned nogoods with a size up to x

  /** If scoringForRemovalOfLearnedNogoodsR = 0, and x>=0, we
    * try to keep all nogoods with LBD <= x (corresponding to so-called "glue clauses") and rank the others by
    * inverse LBD score (i.e., higher LBD means more likely to be ignored or removed).
    * If scoringForRemovalOfLearnedNogoodsR=0 and x<0, we try to keep
    * all nogoods with LBD <= -x and return for all others 0 as pseudo-LBD (but scoringForRemovalOfLearnedNogoods might rank
    * these "unranked" nogoods using some other metrics, see above).
    * Setting not used if scoringForIgnNogoodsR respectively scoringForRemovalOfLearnedNogoodsR != 0, 8 or 11.
    * With scoringForRemovalOfLearnedNogoodsR = 8 or 11, the glue is just a factor among others, otherwise the above applies too. */
  val keepGlue = 3

  var nogoodActivityBump: Float = 1e-37f // only for scoringForRemovalOfLearnedNogoodsR = 1 and others which use nogood activity

  /** learned nogood activity decay (additive) (remark: Minisat 2 uses geometric decay with
    * factor 1/0.999), for scoringForRemovalOfLearnedNogoods=1 etc */
  var nogoodActivityDecay: Float = 1e-20f

  /** If x > 0, the probability of picking a branching literal randomly if no unassigned parameter literal could be found.
    * If x < 0 (e.g., -5000f), a heuristically determined value is used (see code).
    * 0 is typically the best choice: even with 0, there are other means of randomization, e.g.,
    * parameters noisePhaseMemo, diversify and diversifyLight.
    * *
    * Important: a high degree of randomization (also by, e.g., overly frequent restarts) within the SAT solving loop can
    * reduce the number of unassigned literals quickly ("Unassigned peak min" in status line), but that "success" might(!) be deceptive,
    * as the solver might spend a lot of time examining uninteresting parts of the search space. Whereas too little
    * randomization can also lead to stagnation (e.g., getting stuck in a local minimum).
    *
    * Also see noisePhaseMemo */
  val rndmBranchProbR = 1e-6f //1e-6f //1e-6f  // -5000f

  @deprecated var traverseReduciblesUpwardsInUnitPropP: AlternativesForThreads[Boolean] = AlternativesForThreads[Boolean](Map(0 -> true))
  //^ for some extReducibles approaches (see code) only. TODO: remove or say for which ones (e.g., impossible for extReducibles=1)

  /** If > 0 and active multithreading (see maxSolverThreadsR), the portfolio approach which has been
    * fastest in the second sampling round is used exclusively (if 2, single threaded then, if 1, still competing using multiple threads if maxCompetingSolverThreads > 1) for
    * all further model solving. NB: it's not guaranteed that the configuration identified as the fastest will also be the fastest in subsequent rounds. */
  var switchToBestConfigAfterFirstModel: Int = 2

  /** true ignores cost function and parameter/measured atoms. Cost is always assumed to be
    * negative infinity. Not required as such for non-probabilistic problems (you could simply set threshold = Double.MaxValue
    * and use -1 as number of models), but useful for debugging. */
  var ignoreParamVariablesR: Boolean = false

  /** For translating away disjunctions in ASP rule heads (an extension over normal ASP), increase the number of unfold operations
    * if necessary. If diff-SAT find an answer set but spends a lot of time doing unfolds and shifts, consider trying with a
    * smaller value (but this may not discover any existing answer sets). */
  var maxNoOfUnfolds: Int = Int.MaxValue

  /** With 1, integrity rules for classic negation (i.e., :- a, -a) are only
    * added for rules specified via the API but not for those in ASPIF files where it is instead assumed that they have already been added by the grounder.
    * With value 0, integrity constraints will never be generated. Value 2 (adding integrity constraints also for ASPIF)
    * isn't currently supported and wouldn't make much sense since all contemporary grounders add those constraints anyway. */
  val generateIntegrityRulesForAPIdefinedClassicNegation = 1

  var maxSamplingIterationsR = 1000000
  /** stop after max(this,n*1000) many multimodel sampling iterations even if
    * accuracy threshold (total cost target) has not been reached reached (not to be confused with trials
    * of the inner (i.e., SAT solver) loop). n is the value specified with -n on the command line. */
  // TODO: split into max iterations for multimodel sampling and max iterations per single model solving.

  /** Default timeout (approximate) for both the inner solver and multimodel sampling (whatever
    * reaches this time limit first). Affects only the pure sampling and solving time, doesn't account
    * for parsing, etc (so it can't be used for standard timeout benchmarks).
    * NB: Timeout doesn't work well with very low limits (e.g., <10sec), because of the
    * intervals the solver does progress checks. */
  var timeoutMs: Long = 6 /*hours*/ * 60 /*minutes*/ * 60 /*seconds*/ * 1000 /*milliseconds*/

  @deprecated var localSolverParallelThresh: Int = 150 // = localSolverParallelThreshMax: off.
  // Used (with various factors and conditions, see code) as #items threshold for loop parallelization in various places

  /** If true, inner costs which contain undefined measured atoms are replaced with
    *0. However, an undefined measured atoms is likely undefined by mistake, so adding a spanning rule for it is normally better. */
  var ignoreCostsWithUndefMeasuredAtoms: Boolean = false

  /** If true, show the approximate probabilities of all non-auxiliary symbols after sampling (useful for debugging) */
  var showProbsOfSymbols: Boolean = false

  /** If true, show progress at a fixed position in the console (doesn't work with all consoles) */
  var singleLineProgress: Boolean = true

  // ------ Experimental solver settings (most of these can also be set with --solverarg, if they are var's).
  // Use with care, may not work yet as expected:

  /** Maximum % of learned nogoods in the current nogood sharing pool (NOT: all learned nogoods) which are considered
    * for being copied from other threads (NOT the total percentage of learned nogoods being shared).
    * 0 = no nogood sharing.
    * Sharing requires that maxPercentToRemoveOfLearnedNogoods != 0 (which normally is the case).
    * Another (orthogonal) way to regulate the number of shared nogoods is nogoodShareTopKPutIntoSharingPool.
    * NB: nogood sharing may lead to nondeterministic behavior (varying performance and sampling results for same PRNG seed) due
    * to thread interaction. */
  var nogoodShareNumberMax: Float = 1f // 1f // 0.01f

  /** Each time some learned nogoods have been deleted, the top-k (using nogood scoring) remaining learned
    * nogoods (with size <= nogoodShareSizeLimit) are added to
    * the nogood sharing pool where they can be fetched by other solver threads (see nogoodShareNumberMax).
    * Requires nogoodShareNumberMax > 0 */
  var nogoodShareTopKPutIntoSharingPool: Int = 10 //100

  /** Limit nogood sharing to nogoods with size <= x. 8 is the value used by ManySAT, but observe that
    * in contrast to ManySAT, diff-SAT fetches nogoods from other threads exactly directly
    * after some learned nogoods in that thread have been removed (see nogoodRemovalThreshInit, etc). */
  var nogoodShareSizeLimit: Int = 16 //8

  /** Should normally be true, except for small single-model tasks where false might be beneficial due to lower
    * memory management overhead.
    * false can lead to off-heap memory overflow (=crash) for large problems or when sampling multiple interpretations.
    * True only allowed with extReducibles = 1 and 2.
    * Which (and which of freeDeletedNogoodMemoryApproach) is fastest is hard to predict, since
    * memory management can be slower than using just unsafe but might increase locality of nogoods in memory.
    * >>> For sampling (probabilistic problems), value must be true (and freeDeletedNogoodMemoryApproach = 2).
    * If false, "deleted" learned nogoods are removed from reducibles lists but the occupied memory isn't freed or reallocated until diff-SAT ends.
    *
    * Not to be confused with offHeapGarbageCollectionModeR
    */
  val freeOrReassignDeletedNogoodMemory = true

  /** See source code; internal use only.
    * Not to be confused with offHeapGarbageCollectionModeR */
  val freeDeletedNogoodMemoryApproach: Int = 2 // Leave at 2! (the other approaches are experimental). Relevant only
  // with freeOrReassignDeletedNogoodMemory=true and if there are learned nogoods removed (see settings nogoodRemovalThreshInitP etc).
  // With 0 and freeOrReassignDeletedNogoodMemory = true, space assigned for deleted learned nogoods is
  //     reassigned by diff-SAT itself using a thread-local(!) sorted tree for managing off-heap memory, if possible.
  // With 1 and freeOrReassignDeletedNogoodMemory = true, allocated off-heap memory is freed by unsafe.
  // With 2 and freeOrReassignDeletedNogoodMemory = true, a simple thread-local unsorted list is used for memory management.
  // With 3 and freeOrReassignDeletedNogoodMemory = true, a global unsorted list for keeping track of and freeing allocated off-heap memory is used.
  // >>> In any case, this setting has an effect only if freeOrReassignDeletedNogoodMemory = true <<
  // >>> For sampling (probabilistic problems), value must be 2 (and freeOrReassignDeletedNogoodMemory = true).

  /** This value is influential, largely because of the slow memory allocate method of the SDK's unsafe. -1 = auto. */
  var defaultNogoodAllocationSize = -1 //96-8

  /** Remove some redundancies from conflict (i.e., learned) nogoods during solving (similar to MiniSAT >=1.5). Not to be confused with self-subsumption check during preprocessing */
  var conflictNogoodSelfSubsumption = false

  /** Perform nogood simplification at solver runtime (after preprocessing) */
  var inProcessingSubsumption: Boolean = true && maxPercentToRemoveOfLearnedNogoods > 0d

  /** If inProcessingSubsumption=true, perform inProcessingSubsumption only every x-th restart */
  var inProcessingSubsumptionEvery: Int = 1

  /** Preprocessing (variable and nogood removal) - See source code for details - On the commandline, use like this: --solverarg "preProcesssVariableElimConfig" "true 0.5 0.5 1.5 true"
    * Observe that this setting may reduce the entropy of sampled models. */
  var preProcesssVariableElimConfigR: (Boolean, Double, Double, Float, Boolean) = /*Pre-processing of initial sets of variables
  and nogoods. Tries to remove variables and nogoods with these variables before actual solving starts.*/ (false /*on/off*/ ,
    /*currently not used: */ 0d,
    /*currently not used: */ 0d,
    1f /*10f*/ /*0.1f*/ /*maximum product of literals with positive or negative occurrence of variable candidate for removal, in % of sqrt(all literals)*/ ,
    true /*true: materially remove variables instead of just ignoring them. True currently available in SAT mode only*/ )

  /** If true, we check for existence of other nogood subsuming a nogood during preprocessing (not related to self-subsumption check) */
  var foreignNogoodSubsumptionCheck = false

  var strengthenNogoodsDuringPreproc = true  // using self-subsumption check during preprocessing

  /** See source code */
  var abandonOrSwitchSlowThreads: Double = 0d // suggestion: try with 0d (off) first, then (using debug=true) find some value which abandons some threads after a few seconds (e.g., 2d or 10d).
  // If > 0, solver threads which seemingly (might not be true!) fell behind competing solver threads by a certain amount
  // are aborted, changed in their priority or switched to a different branching approach. See slowThreadAction for the concrete action.
  // Lower values mean earlier change/removal of seemingly worse performing competing solver threads (portfolios).
  // The "slowness" criterion is purely heuristical and cannot guarantee that the abandonded/switched "slow" solver threads are actually the least suitable
  // for the problem at hand (but see slowThreadAction = 2 below).
  // The frequency of "slowness" checks also depends on setting progressCheckEveryTrialsR (lower value = more frequent checks).

  /** See source code */
  var slowThreadAction: Int = 4 // determines the action on seemingly slow threads if setting abandonOrSwitchSlowThreads is active.
  // If 0, kill the seemingly "slow" thread (giving remaining threads more CPU time/higher core frequency), or change thread priorities if killing thread wouldn't be sensible (identical configurations).
  // If 1, reduce thread priority (if supported by JVM and OS). Since priorities are reduced in relation to other threads' priorities,
  // this approach also allows for indirect increase of priority if the "slower" thread catches up speed at a later point.
  // If 2: as with 1 but reverse action: priorities of "seemingly slow" threads are increased.
  // TODO: 3 (currently not available): If 3 and there are different free eli search approaches in current threads, "slow" solver threads are
  // switched to the next approach in the sequence freeEliSearchApproachP. slowThreadAction = 1 is enforced if slowThreadAction = 0 and there is only one solver thread left.
  // If 4, just perform a restart of the respective "slow" solver performed.

  /** See source code */
  var maxApproachSwitchesPerSolverThread: Int = Int.MaxValue // maximum number of switches per solver thread if slowThreadAction = 3

  /** Report regular solving progress at least every x solver trials. Must be a power of 2. */
  var enforceProgressChecksEveryTrialsR: Int = if (abandonOrSwitchSlowThreads != 0d) 65536 else (if (debug) 65536 * 6 else 65536 * 6)

  /** Minimum number of trials between two subsequent progress checks. Useful for problems which create an
    * extremely large number of conflicts in short time. Observe that this and other progress check settings also influence the number of best phase queings and rephasings (if active). */
  var minNoTrialsBetweenTwoProgressChecks = 2096 //1024

  //val progressReportImprovThresh = if (diffSAT.debug) 100 else 100 // report progress also if reduction of unassigned literals is at least this threshold

  /** If true, after solving, propositional clauses corresponding to "clark nogoods" and any loop
    * nogoods are printed. ! Observe that this doesn't emit an equivalent theory in case the ASP program isn't tight since the set of loop nogoods isn't complete. However,
    * if the emitted clauses are used with a SAT solver and the resulting model is an answer set (checkable in P time), it is an answer
    * set of the original answer set program. */
  var emitClauses: Boolean = false

  /** If true, we stop sampling after the (using -n) specified number of models have been reached even if
    * the accuracy threshold or cost stagnation has not been reached yet. */
  val stopAfterNModels: Boolean = false

  /** Threshold used to determine whether there is cost stagnation is calculated as accuracy threshold / stagnationTolDiv */
  var stagnationTolDiv: Double = 100d

  /** With true and -n <n> with n > 0, sampling stops when the specified number of models has
    * been reached even if the cost minimum has not been reached up to the given threshold. */
  var enforceStopWhenSampleSizeReached: Boolean = false

  @volatile var emittedClauses: Boolean = false

  val initCleanUpArrangeClarkNogoods: Boolean = true // must leave at true!

  val clusterAbsElis = false && freeEliSearchApproachP.alternatives.values.toSeq.contains(7) // TODO: keep? Clustering elis seems mostly (?) not helpful if the
  // number of common nogoods/clauses is used as cluster distance metrics, simply because nogoods typically don't share enough elis.

  val clusterAbsElisIfVarsMax = 20000

  val clusterNogoods = false // might be useful some time but currently way too slow

  val removeDuplicateLiteralsFromClarkNogoods = false

  /** shuffle nogoods during preparation phase if #clauses <= x. 0 = no shuffling.
    * observe that shuffling makes the task nondeterministic even with fixed seed of the PRNG (see above in code) */
  var shuffleNogoods: Int = 0 //if(clusterNogoods || sortInitialNogoods) 0 else 0 //20000

  /** Sort "Clark" nogoods by number of literals, from small to large.
    * See initAbsElisArrangementP for how to utilize this in branching decisions. */
  var sortInitialNogoods = shuffleNogoods == 0 && !clusterNogoods

  /** See code. -1: auto */
  var nogoodBCPtraversalDirectionP = AlternativesForThreads[Int](Map(0 -> -1/*0->0, 1->1, 3->1, 5->1, 7->1, 9->1, 11->1*/))

  @deprecated val padSymbolsToPow2 = false // TODO: remove

  // ------ Internal solver settings. They should normally be left unchanged, although some of them can be set with --solverarg (if they are var's).

  /** See source code */
  val extReducibles: Int = 2 // Should be 2 (the other approaches are experimental, not well tested and might be removed in the future).
  // Determines how reducibles are internally represented and how BCP uses reducibles lists:
  // 1: Reducible lists with bulk clear and restauration lists,
  // 2: Minisat-style watch lists (see code for details),
  // 5: Uses nogood's unset length and bitset or product (works only for small problems).
  // 2 is typically the best choice. Options 0,3,4 currently not available.

  /** See source code */
  var delayStartUntilCPULoadTo: Double = -1d //if(diffSAT.noOfMinibenchmarkTrials >= 2) 0.01d else 0.1d //-1d  // if >= 0d, this blocks the start of the actual solver (and timer start) until system CPU load falls under this value.
  // Useful for preliminary benchmarking tasks.

  val keepNogoodsWeaklySorted: Boolean = false // experimental

  /** Initial literal assignment value in phase memory
    * 0 = 0x00,
    * 1 = 0x01,
    * 2 = pos/neg ratio of approximate number of occurrences in nogoods (see code for details),
    * 3 = as 2 but using the inverse ratio,
    * 4 = approximated Jeroslow-Wang (very time and memory consuming during preprocessing!),
    * 5 = random per each absEli,
    * 6 = randomly true (false) per all absElis,
    * Also see initAbsElisArrangementP. */
  var initialPhaseMemo: Int = 1   // TODO: AlternativesForThreads

  /** True: as in RSAT but optionally with some noise (randomization at restarts).
    * false is for debugging purposes. NB: noisePhaseMemoR < 0 or =1 effectively deactivates phase memo. */
  var updatePhaseMemo: Boolean = true

  /** If > 0, add noise to use of phase memo when using the phase of a branching eli.
    * If x <= 0, no phase memo is used: positive polarity with probabiliy -x, negative polarity otherwise.
    * Observe that with adaptNoisePhaseMemo, it can make sense to provide a value >= 1 here.
    *
    * Also see rndmBranchProbR */
  var noisePhaseMemoP = AlternativesForThreads[Float](Map(0 -> 1e-5f, 4 -> 0.001f))

  /** If != 0, phase memo noise (see noisePhaseMemoR) change over time (adapted at each restart)
    * using a heuristics. Try with 2 first if unsure.
    * 0: no change,
    * 1: decrease with number of conflicts (logarithmically),
    * 2: fluctuating noise with amplitude decreasing with number of conflicts (also see adaptNoisePhaseMemo2Frequency and adaptNoisePhaseMemo2Amplitude),
    * 3: like 2, but using the number of restarts instead of number of conflicts,
    * 4: like 1, but using a different function (slower decline) */
  var adaptNoisePhaseMemo: Int = 2 // TODO: make AlternativesForThreads

  /** >= 0. For adaptNoisePhaseMemo=2 */
  var adaptNoisePhaseMemo2Frequency = 10d  // TODO: make AlternativesForThreads

  /** >= 1. For adaptNoisePhaseMemo=2 */
  var adaptNoisePhaseMemo2Amplitude = 1d  // TODO: make AlternativesForThreads

  /** Every x restarts perform a reset to a (global or thread-local, see globalBestPhaseMemo)
    * "best phase" with some noise added. 0 = off. Also see bestPhasesQueueSize, bestPhaseCriterion and other bestPhase settings.
    * Simple kind of rephasing during restarts. Unrelated to setting rephasePhaseMemoP, except that it also uses bestPhases. */
  var weakRephasingAtRestartEveryP = AlternativesForThreads[Int](Map(0 -> 0/*, 1 -> 5, 8 -> 2*/))

  var weakRephasingThreshForBestPhase = 0.1f //0.1f

  var weakRephasingThreshForRandomPhase = weakRephasingThreshForBestPhase - 0.005f

  /** With true, the phase memory is from time to time (at some restarts, see below) updated to one of
    * the following:
    * best phase so far, random phase, original phases, run of SLS (if useSLSinPhaseMemoRephasing=true - e.g., WalkSAT, SASAT), and
    * other heuristics (see code).
    * Similar to but different approach than weakRephasingAtRestartEveryP */
  var rephasePhaseMemoP = AlternativesForThreads[Boolean](Map(0 -> true/*, 1 -> true, 4 -> true, 7 -> true*/))

  var rephasePhaseMemoIntervalInit: Int = 10000 //200000 //10 //2000 //10000

  /** Lower=more frequent rephasings. Also see rephasingPhaseMemoIntervalDiv. */
  var minNoConflictsBeforeFirstRephasing: Int = 5 // 5000  //5000

  /** The higher the more often rephasing takes place (details see code;
    * also see rephasePhaseMemoIntervalInit). Ignored if rephasePhaseMemoP is false */
  var rephasingPhaseMemoIntervalDiv: Int = 1000 //100000 //1000 //10   // TODO: AlternativesForThreads

  /** Size of best phases queue (where previously encountered assignment phases are stored for use
    * in rephasing). At rephasing, on of the entries in this queue is picked randomly. */
  var bestPhasesQueueSize: Int = 10 // 10

  /** Criterion for what counts as a new "best phase".
    * 0: based on exponential moving averages of the learnt clause LBDs ("glue")
    * 1: based on number of assigned variables
    * 2: based on conflicts triggered during recent BCP(!) (experimental, might create large time overhead) */
  var bestPhaseCriterion: Int = 0

  /** If true, each time a progress check occurs a new "best phase" assignment is added to the best phases queue,
    * even if it's not a greedy improvement (i.e., if it didn't reduce the number of violated nogoods).
    * Use true for debugging purposes.*/
  var enforceBestPhaseQueueEntry: Boolean = false

  // @deprecated var globalPhaseMemo: Boolean = false && !rephasePhaseMemo // /* && !reusedTrailRestartsR ??*/ // more tests are required to confirm which value is best here
  // Remark: we shouldn't use true if rephasePhaseMemoP is also true, as otherwise the code wouldn't be threadsafe without massive speed decrease
  // TODO: bug with true (see val absElisSeqArranged ...)

  @deprecated val globalBestPhaseMemo: Boolean = false  // TODO: true not properly working anymore (occasional race condition?). Remark: if true, this provides another way for solver threads to exchange information. Also adds further nondeterminism

  // Rephase-by-SLS (Stochastic Local Search) settings:

  /** SLS here means occasionally running WalkSAT (or variants, see below) or SASAT over the phase memo assignment during rephasing.
    * true is often faster, but requires more memory.
    * >>>> Only relevant if rephasePhaseMemoP is true. Also requires allowEliToClarkReduciblesLookup=true <<<<
    * Some problems can profit massively from rephase-by-SLS (e.g., g125.17, ii32d3, f400, f800, etc, random 3-SAT) whereas
    * others are just slowed down by activating SLS-rephasing (e.g., hanoi). Observe that SLS requires more
    * memory because it requires maintainEliToFullReducibles=true. Observe threshNoOfAbsElisForSLSrephasing. */
  var useSLSinPhaseMemoRephasingP = AlternativesForThreads[Boolean](Map(0 -> false/*, 2 -> true, 4 -> true, 8 -> true*/))  // Remark: with the current maxInnerSLSTrials settings, thread $8  runs with SLS only over the entire time (doesn't change back to any other rephasing approach)

  /** If number of variables outside this interval never use SLS */
  var boundsOnNoOfAbsElisForSLSinRephasing = (1, Long.MaxValue/*400000L*/)

  /** If false, (a variant of) WalkSAT is used.
    * If true, SLS using Simulated Annealing (SA) is used.
    * Our SASAT implementation is a variant of SASAT-with-random-walk, based on W. M. Spears: Simulated Annealing for Hard Satisfiability Problems, but of course using nogoods instead of clauses
    */
  var useSASATinSLS = false

  var walkSATnoiseR: Float = 0.3f //0.567f // remark: optimal value for random 3SAT might be 0.567 acc. literature (TODO: make var. Add "auto" and recognize 3SAT)

  var randomWalkProbInSASAT: Float = 0.1f // use 0 to deactivate. Observe that the semantics is different from the algo in Sect. 5 in [Spears]

  var SASATwithWalkSATsteps: Boolean = false // relevant if useSASATinSLS=true and(!) randomWalkProbInSASAT > 0

  var walkSATwithTempDecl: Boolean = false // relevant if useSASATinSLS=false. Also see maxTempInSLS, minTempInSLS and decayRateSLS

  var fixedTemperatureWithPlainWalkSAT: Double = 0.1d

  /** If > 0f, we consult and update with probability x variable and nogood scores when making nondeterministic selctions
    * of literals and nogoods in WalkSAT (see source code for details) */
  var useScoresInSLS: Float = 0f // \\\

  var shareScoresFromSLSWithOtherThreads: Boolean = false  // \\\ experimental (TODO: check, fix)

  var shareNogoodsFromSLSWithOtherThreads: Boolean = false // \\\ experimental (TODO: check, fix)

  var copyPhasesFromBestPhasesInSLS: Boolean = true // true cannot be combined with copyPhasesFromAssignmentInSLS = true

  var copyPhasesFromAssignmentInSLS: Boolean = false // true cannot be combined with copyPhasesFromBestPhasesInSLS = true

  var copySLSPhasesToBestPhasesInSLS: Boolean = true //true

  /** If false, the current memorized phases from CDNL are used for the first outer SLS iteration */
  var alwaysStartFromRandomPhasesInSLS: Boolean = false

  /** If true, we reset SLS (see resetInnerSLSAfterPercentMaxInnerTrials) to state so far with lowest number of violated nogoods (instead of random assignments) */
  var resetSLStoStoredBestState: Boolean = false

  var semiLocalSearchInSLS: Boolean = false // experimental. TODO: remove?

  var showSLSprogress: Boolean = true && singleLineProgress

  /** If a small value is used here, rephasingDiv (in sharedDefs) might need to be increased (so
    * that using frequent SLS-rephasings, the CDNL assignment loop "emulates" the sasat outer loop) */
  var sasatOuterMaxInSLS: Int = 1 // 1000000

  /** Observe that in SASAT, each of these iterations takes noOfAbsElis x more steps than in WalkSAT.
    * !!! Remark: the other stop criterion for the inner loop is when the temperature reaches MIN_TEMP (see decayRateSLS...). */
  var maxInnerSLSTrials: Long = (if (useSASATinSLS) 7000000L else if (walkSATwithTempDecl) Long.MaxValue else 100000000L /*Long.MaxValue*/)

  /** Resets SLS state every x * maxInnerSLSTrials trial. Resets to random or "best" state so far (see resetSLStoStoredBestState) */
  var resetInnerSLSAfterPercentMaxInnerTrials = 0.1f

  var maxTempInSLS: Double = 0.4d // 0.3d  // for WalkSAT this is only relevant if walkSATwithTempDecl is true

  var minTempInSLS: Double = 0.001d //0.1d  // for WalkSAT this is only relevant if walkSATwithTempDecl is true

  /** < 0f: auto rate divided by -x.
    * Remark: the other stop criterion for the inner loop is maxInnerSLSTrials
    *E.g., for long SLS runs with little temp decrease, use large negative number, e.g., -10000f */
  var decayRateSLS: Float = -10f //also try -10f -100f -1000f -1f 1e-7f

  /** true disallows rephasing (including SLS) to run in parallel with other SLS phases.
    * This switch only has an effect if globalPhaseMemo is false, otherwise rephasings are always blocking for single thread use. */
  var runRephasingExclusively: Boolean = false

  // End of SLS settings ------------------------

  /** Traversal order in some of the places where variables are searched or ordered. Can make a significant difference but the optimal order is unfortunately
    * unpredictable (for us). What might work (if there is no "lucky" arrangement) is to choose an arrangement where
    * the branching eli is selected in a way which allocates truth values to literals in short nogoods (requires sorting
    * of nogoods), or variables which occur in many nogoods. The branching eli needs to be picked by an appropriate
    * approach set with freeEliSearchApproachP (linear search uses the initAbsElisArrangementP).
    * 0 = arrange literals (seen as integer numbers) upwards, 1 = downwards, 2 = random,
    * 3 = order of first appearance in nogoods,
    * 4 = reverse order of first appearance
    * (also see sortInitialNogoods),
    * 5 = sorted by ratio number of pos/neg occurrences in nogoods, 6 = as 5 but inverse ratio,
    * 5 or 6 works only with allowEliToClarkReduciblesLookup = true (see below), otherwise 4 is used.
    * 7 = by initial phase memo (see initialPhaseMemo). 8 = as 7 but reverse order.
    * 9 = by number of occurrences as pos or neg eli. 10 = as 9 but reverse order. Remark: 9 and 10 may increase significantly the amount of memory required during initialization
    * If unsure, try with 0 or 7 first.
    * Also see initialPhaseMemo.
    * !! initAbsElisArrangement also determines the initial absEli scores (priority of free (unimplied) absElis in decision making)
    * from this order, see absEliScoringApproachP. Also see absElisScoringPreservationFactorFromInit.
    */
  var initAbsElisArrangementP: AlternativesForThreads[Int] = AlternativesForThreads[Int](Map(0 -> 7/*7*/, 7 -> 9/*<- presumes $7 uses approach 12 for free eli search*/))

  /** Higher values = the initial arrangement of absElis (see initAbsElisArrangementP) are
    * influencial for a longer time on the branching eli decision making. If 0, all absEli scores are initialized to 0 regardless of
    * initAbsElisArrangementP (but initAbsElisArrangementP still determines the absElis traversal order elsewhere,
    *e.g., in linear search approaches to finding the next branching eli).
    * Very high values together with neverRescaleAbsEliScores=true effectively make absEliScoringApproachP meaningless. TODO: AlternativesForThreads
    * Negative values reverse the absEli score impact of the order defined by initAbsElisArrangement.
    * Zero would mean that all absElis scores are initialized to 0.
    * Can be larger than 1. */
  var absElisScoringPreservationFactorFromInit: Float = 0.1f //Float.MaxValue  // TODO: AlternativesForThreads

  val neverRescaleAbsEliScores = false // true for debugging purposes only

  @deprecated var ensureParamAtomsAreMeasured: Boolean = false // Deprecated; if true, every parameter atom which isn't already a measured atom will
  // be made a measured atom. That's only useful if the weight of the parameter atom needs to be _directly_ controlled during sampling.
  // Normally, autoGenerateCostLinesForHypotheses should be set to true in that case too.

  @deprecated var autoGenerateCostLinesForHypotheses: Boolean = false // Deprecated; generates an inner MSE cost function for each parameter atom which isn't
  // part of any cost, that is, for hypothesis parameter atoms. The generated inner costs are required because for hypotheses and
  // the older numerical diff approach, we needed a (changing, "moving") target probability (computed using an "outer" gradient descent).
  // true requires that ensureParamAtomsAreMeasured is also true.

  /** If true, parameter atoms which aren't also measured atoms are ignored. Works
    * only if allowNumFiniteDiff=true. */
  var ignoreParamIfNotMeasured: Boolean = false

  /** For allowNumFiniteDiff; if > 0, bag of samples models is cleared if
    * there are no significant cost improvements although the threshold has not been reached yet, in order to escape a local minimum.
    * Decremented after each reset. */
  var resetsNumericalOuterLoopOnStagnation: Int = 10

  /** Used with allowNumFiniteDiff to avoid getting stuck in a local minimum. But
    * if this value is too large, nontermination (because of non-convergence to _any_ minimum) can occur. */
  var numFinDiffShuffleProb: Double = 0.0005d

  var shuffleRandomVariables: Boolean = true

  @deprecated val omitSingletonBlits: Boolean = true // must be true!

  /** Default cost function threshold (target cost). Lower value = more accurate results. Change as appropriate for problem and cost function(s)
    * To set the threshold, it is advised to use console argument -t or the User API instead of changing this default. */
  var defaultThreshold: Double = 0.01d

  var allowEliToClarkReduciblesLookup: Boolean = initialPhaseMemo == 2 || initialPhaseMemo == 3 || /* initialPhaseMemo == 4 ||*/ useSLSinPhaseMemoRephasingP.getAllAlternativeValues.contains(true) // should normally
  // be false, but true is a requirement for Stochastic Local Search (see useSLS) and certain initialPhaseMemo approaches.

  /** Default size of a watch list. Changes here can have
    * a significant effect on performance, but optimal value is hard to predict */
  var defaultEliToReducibleListCapacity: Int = 1024 * 1 // 1024*2

  /** In number of Ints (including metadata). Dynamically adapted during runtime. Initial size should rather pessimistic (high). */
  var initialNewNogoodReducibleSlotSize: Int = 160

  /** With true, a pseudo random number generator is used within solver threads which
    * is somewhat slower than the default one but provides better randomness.
    * Observe that none of the random number generators used in this software is suitable for encryption or security-related tasks. */
  var altRandomNumGen: Boolean = false

  @deprecated val ignoreLearnedNogoods: Boolean = false // TODO: remove. true marks all learned nogoods for deletion. For debugging purposes only.

  /** Writes the positive dependency graph of the answer set program to DOT file dependencyGraphPos.dot, then exits.
    * DOT files can be rendered with various tools, e.g., GraphViz or Mathematica. In Mathematica use Import["C:\\Users\\Owner\\workspaceScala211\\DelSAT\\depGraphPosNeg.dot", ImagePadding -> 10]
    */
  var emitASPpositiveDependencyGraph = false

  // End of advanced solver settings ===============================================================================================

  var probabilisticFactPrefix: String = "_pr_"

  var patFactPrefix: String = "_pat_"

  var costFactPrefix: String = "_cost_"

  var evalFactPrefix: String = "_eval_"

  var probabilisticFactProbDivider: Int = 10000 // since our solver (like most ASP solvers) doesn't support floating point numbers, we divide integers

  // ===============================================================================================================================

  var suppressAnswers: Boolean = false // if true, the resulting models aren't printed (useful if number of sampled models is large)

  val adHocConjunctiveQueries: Seq[Seq[String]] = Seq() // note that this works only for symbols defined in rules - if x is an undefined predicate (or _eval_),
  // addHocQueries cannot be used to deduce Pr(x) = 0.
  /* Example: Seq( // conjunctions c of atoms whose marginal probabilities Pr(c) should be printed after sampling
    Seq("flip(1)", "head(1)"),
    Seq("flip(2)", "head(2)"),
    Seq("flip(3)", "head(3)")
    )
    */

  val adHocDisjunctiveQueries: Seq[Seq[String]] = Seq() // analogous to adHocConjunctiveQueries, but each element is a clause (disjunction of literals)
  /*Example (SAT mode): Seq(
  Seq("1", "-2", "3"),
  Seq("-1", "3")
  ) */

  val adHocSimpleGroundRuleQueries: Seq[(String /*head atom (exactly one positive literal)*/ , Seq[String] /*body literals*/ )] = Seq() // analogous to adHocConjunctiveQueries, but each element is a ground normal rule

  val adHocCollectionOfSimpleGroundRuleQuery: Seq[(String /*head atom (exactly one positive literal)*/ , Seq[String] /*body literals*/ )] = Seq() // analogous to
  // adHocSimpleGroundRuleQueries, but here a single query consisting of a conjunction of the rules is specified.

  // ================== ================== ================== ================== ================== ================== ================== ==================

  val unsafe = UNSAFEhelper.UNSAFE

  val intArrayOffs = unsafe.arrayBaseOffset(classOf[Array[Int]]) // we put this here to ensure that scalac makes this a static field

  //var offHeapAllocatedEstimate = 0l  // measured only some(!) of the non-heap memory allocated by diff-SAT, but not all and also not any other off-heap data (like DirectByteBuffers)
  // ^ TODO: not precise (bug, estimate too high). Currently commented out.

  var omitSysExit0 = false // If this .jar is dynamically included in prasp2 using classloader, we must not sys.exit in case of successful termination (except -v/-hashOfPass), as this
  // would quit the overall program. We could prevent this issue using some additional wrapper method, but we want to keep prasp2 compatible with Java tools other than this.
  // If on the other hand the tool is invoked as an external process, sys.exit(0) is required.

  @volatile var stopSolverThreads = false

  def getSharedFieldsUsingReflection(omitRefType: Boolean = true,
                                     omitScalaGen: Boolean = true,
                                     omitFinal: Boolean = true): Array[(String, AnyRef)] = {

    // TODO: dangerous method; currently only used for test batch processing of formulas but still should find a better way

    val paramFields = sharedDefs.instance.getClass.getDeclaredFields

    paramFields.flatMap(fieldInSharedDefs => {

      val fStr = fieldInSharedDefs.getName

      //if(fStr == "debug" || fStr == "shuffleRandomVariables")
      // println(java.lang.reflect.Modifier.toString(fieldInSharedDefs.getModifiers))

      try {

        val valueOfField = fieldInSharedDefs.get(sharedDefs.instance)

        if (omitFinal && java.lang.reflect.Modifier.isFinal(fieldInSharedDefs.getModifiers) || omitRefType && valueOfField.toString.contains("@") || omitScalaGen && (fStr.contains("$") || valueOfField.toString.contains("$")))
          None
        else
          Some((fStr, valueOfField))

      } catch {

        case e: Exception => {

          System.err.println(e)

          Some((fStr, "(could not retrieve value of " + fStr + ")"))

        }

      }

    })

  }

  def setSharedFieldsUsingReflection(fieldNamesValue: Array[(String, AnyRef)]): Unit = {

    fieldNamesValue.foreach((fieldnameValue: (String, AnyRef)) => {

      val field = sharedDefs.instance.getClass.getDeclaredField(fieldnameValue._1)

      field.setAccessible(true)

      field.set(sharedDefs.instance, fieldnameValue._2)

    })

  }

  def overrideAdvancedSolverArgs(additionalSolverArgsR: mutable.HashMap[(String, Int /*<-thread to associate value with*/ ), String],
                                 baseSettingsOpt: Option[Array[(String, AnyRef)]] = None): Unit = {

    if (debug) println("additionalSolverArgsR = " + additionalSolverArgsR)

    baseSettingsOpt.foreach(setSharedFieldsUsingReflection(_)) // to restore defaults before overriding them (only required for batch testing)

    val additionalSolverArgs = additionalSolverArgsR.map((tuple: ((String, Int), String)) => ((tuple._1._1.replaceAllLiterally("\"", "").trim, tuple._1._2), tuple._2.replaceAllLiterally("\"", "").trim))

    // (Remark: we could probably do the type matching automatically using scala.reflect which we want to avoid)

    // Important: for graal native image, during image generation, graal must use the (otherwise unreferenced)
    // class RuntimeReflectionRegistrationFeature
    // to register all fields in sharedDefs. See RuntimeReflectionRegistrationFeature.java for details.

    additionalSolverArgs.foreach { case ((paramName, thread), paramValueStr) => { // see above for meaning of these parameters

      //sharedDefs.instance.getClass.getDeclaredFields.foreach(f => println(f/*.getName*/))

      val field = sharedDefs.instance.getClass.getDeclaredField(paramName)

      field.setAccessible(true)

      def defaultHeadOfAlternatives: Any = field.get(sharedDefs.instance).asInstanceOf[AlternativesForThreads[_]].alternatives.head._2

      def updateAlternatives(field: Field, nvs: Map[Int, _]): Unit = {

        val s = AlternativesForThreads(alternatives = field.get(sharedDefs.instance).asInstanceOf[AlternativesForThreads[_]].alternatives ++ nvs)

        field.set(sharedDefs.instance, s)

      }

      if (debug) println("--solverarg in group of solver thread " + thread + ", parameter name " + field.getName + " with type '" + field.getType + "' with old value " + field.get(sharedDefs.instance))

      field.getType match {

        case f if f == classOf[Int] => {

          field.set(sharedDefs.instance, paramValueStr.toInt)

        }

        case f if f == classOf[Long] => {

          field.set(sharedDefs.instance, paramValueStr.toLong)

        }

        case f if f == classOf[Float] => {

          field.set(sharedDefs.instance, paramValueStr.toFloat)

        }

        case f if f == classOf[Double] => {

          field.set(sharedDefs.instance, paramValueStr.toDouble)

        }

        case f if f == classOf[Boolean] => {

          field.set(sharedDefs.instance, paramValueStr.toBoolean)

        }

        case f if f == classOf[AlternativesForThreads[_]] && defaultHeadOfAlternatives.isInstanceOf[Float] => {
          // (we could avoid isInstanceOf (which we need due to type erasure) using type tags, but we'd better avoid Scala reflection)

          val nvs = paramValueStr.split("\\s+").map(v => (thread, v.toFloat)).toMap

          updateAlternatives(field, nvs)

        }

        case f if f == classOf[AlternativesForThreads[_]] && defaultHeadOfAlternatives.isInstanceOf[Int] => {
          // (we could avoid isInstanceOf (which we need due to type erasure) using type tags, but we'd better avoid Scala reflection)

          val nvs = paramValueStr.split("\\s+").map(v => (thread, v.toInt)).toMap

          updateAlternatives(field, nvs)

        }

        case f if f == classOf[AlternativesForThreads[_]] && defaultHeadOfAlternatives.isInstanceOf[Long] => {
          // (we could avoid isInstanceOf (which we need due to type erasure) using type tags, but we'd better avoid Scala reflection)

          val nvs = paramValueStr.split("\\s+").map(v => (thread, v.toLong)).toMap

          updateAlternatives(field, nvs)


        }

        case f if f == classOf[AlternativesForThreads[_]] && defaultHeadOfAlternatives.isInstanceOf[Double] => {
          // (we could avoid isInstanceOf (which we need due to type erasure) using type tags, but we'd better avoid Scala reflection)

          val nvs = paramValueStr.split("\\s+").map(v => (thread, v.toDouble)).toMap

          updateAlternatives(field, nvs)


        }

        case f if f == classOf[AlternativesForThreads[_]] && defaultHeadOfAlternatives.isInstanceOf[Boolean] => {
          // (we could avoid isInstanceOf (which we need due to type erasure) using type tags, but we'd better avoid Scala reflection)

          val nvs = paramValueStr.split("\\s+").map(v => (thread, v.toBoolean)).toMap

          updateAlternatives(field, nvs)


        }

        case f if f == classOf[(Seq[Int], Seq[Int], Seq[Double])] => { // for restartTriggerConfP. Observe that using --solverarg only
          // the heads of each of the inner seqs (alternatives) can be set.
          // NB: this simple form of pattern matching couldn't distinguish this case from, e.g., Seq[Int], Seq[Long], Seq[Float]

          //println("--solverarg parameter field " + field.getName + " with type (Seq[Int], Seq[Int], Seq[Double]) with old value " + field.get(sharedDefs.instance))

          val s = paramValueStr.split("\\s+").zipWithIndex.map({

            case (headItemStr: String, 0 /*pos: Int*/ ) /*? there doesn't see to be a way to get the nested classes e.g. from f.getClasses()(pos)*/ => Seq(headItemStr.toInt)

            case (headItemStr: String, 1 /*pos: Int*/ ) => Seq(headItemStr.toInt)

            case (headItemStr: String, 2 /*pos: Int*/ ) => Seq(headItemStr.toDouble)

            case (_, _) => diffSAT.stomp(-5009)

          }).toSeq

          field.set(sharedDefs.instance, (s(0), s(1), s(2)))

        }

        case f if f == classOf[(Boolean, Double, Double, Float, Boolean)] => {

          //println("--solverarg parameter field " + field.getName + " with type (Boolean, Double, Double, Float, Boolean) with old value " + field.get(sharedDefs.instance))

          val s = paramValueStr.split("\\s+").zipWithIndex.map({

            case (headItemStr: String, 0 /*pos: Int*/ ) => headItemStr.toBoolean

            case (headItemStr: String, 1 /*pos: Int*/ ) => headItemStr.toDouble

            case (headItemStr: String, 2 /*pos: Int*/ ) => headItemStr.toDouble

            case (headItemStr: String, 3 /*pos: Int*/ ) => headItemStr.toFloat

            case (headItemStr: String, 4 /*pos: Int*/ ) => headItemStr.toBoolean

            case (_, _) => diffSAT.stomp(-5009)

          }).toSeq

          field.set(sharedDefs.instance, (s(0), s(1), s(2), s(3), s(4)))

        }

      }

      if (debug) println("    New value: " + field.get(sharedDefs.instance))

    }

    }

  }

  // ================== ================== ================== ================== ================== ================== ================== ================== ==================

  type Eli = Int

  type Nogi = Int

  final case class Rule(headAtomsElis: Array[Eli],
                        bodyPosAtomsElis: Array[Eli],
                        bodyNegAtomsElis: Array[Eli],
                        blit: Eli /*note: if omitSingletonBlits, this is an ordinary (non body) eli if there's just one body literal*/ ,
                        elisFromDoubleNegationsInBodyPosAtomsElis: Array[Int] = Array[Int]() /* <-- only used when creating rules (with double negation) via API, not via aspif file*/) {

    def toString(symbols: Array[String]): String = {

      assert(headAtomsElis.length == 1) // diff-SAT supports disjunctive rules, but by this point they are transformed (normalized) already (also any :- constraints)

      if (bodyNegAtomsElis.isEmpty && bodyPosAtomsElis.isEmpty)
        symbols(headAtomsElis.head - 1) + "."
      else {

        symbols(headAtomsElis.head - 1) + " :- " + bodyPosAtomsElis.zipWithIndex.map(eliAndIndex => {

          (if (elisFromDoubleNegationsInBodyPosAtomsElis.contains(eliAndIndex._1 /*_2*/))
            "not not " else "") +
            symbols(eliAndIndex._1 - 1)

        }).mkString(", ") +
          ((if (bodyNegAtomsElis.isEmpty || bodyPosAtomsElis.isEmpty) "" else ", ") +
            bodyNegAtomsElis.map(nEli => "not " + symbols(/*negateNegEli*/ -(nEli) - 1)).mkString(", ")) + "."

      }

    }

  }

  type NogoodReducible = Long // an unsafe address. For layout in memory see offsetOfNogoodInReducible

  val newAspifEliOffsets: Int = 5000000

  val newAspifEliBoundary = Int.MaxValue - newAspifEliOffsets * 3

  val aspifExtraShowEliBoundary = newAspifEliBoundary

  val extraShowAspifElitCount = new java.util.concurrent.atomic.AtomicInteger(0)

  val aspiEliForAuxSymbolForOtherPurposesBoundary = aspifExtraShowEliBoundary + newAspifEliOffsets

  val newFalseAspifElisBoundary = aspiEliForAuxSymbolForOtherPurposesBoundary + newAspifEliOffsets // this must be the highest offset for auxiliary literals

  val newFalsePredsCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  val newAuxForOtherPurposesPredsCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  @inline def isNewFalsePosAspifEli(aspifEli: Int) = aspifEli >= newFalseAspifElisBoundary

  var commandLineTakeNote: String = ""

  type RandomGenSuperclass = java.util.Random // java.util.SplittableRandom

  val seedRngGlobal = if (seedRngGlobalR == -1l) new Random().nextLong() else seedRngGlobalR

  if (debug) println("\nGlobal PRNG seed = " + seedRngGlobal + "\n")

  val rngGlobal: RandomGenSuperclass = new RandomGenSuperclass(seedRngGlobal)

  val threadPRNGSeedPool = (1 to 256).map(_ => rngGlobal.nextLong()) // we obtain possible thread-local PRNG seeds immediately
  // to avoid distortions from changing the consumption of global random numbers during development.
  // (If the actual number of solver threads is larger than 256, simply new nextLong calls are employed.)

}