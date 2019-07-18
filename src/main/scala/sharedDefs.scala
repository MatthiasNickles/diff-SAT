/**
  * delSAT
  *
  * Copyright (c) 2018,2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

import com.accelad.math.nilgiri.DoubleReal
import com.accelad.math.nilgiri.autodiff.DifferentialFunction
import commandlineDelSAT.delSAT
import solving.Preparation
import sun.misc.Unsafe
import utils.{IntArrayUnsafeS, XORShift32}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ArrayBuilder}
import scala.reflect.ClassTag

package object sharedDefs {

  /* ================== Solver settings ==================

   From the delSAT commandline, most of the default settings below can be changed using
   --solverarg "paramName" "paramValue"

   Example: --solverarg maxSolverThreadsR 2

   Each --solverarg sets only a single parameter. If the param value is a Seq (that is, each solver thread uses
   one of the seq elements as parameter), list the element values separated by space characters.

   Example: --solverarg freeEliSearchConfigsP "5 3 0 3 3 7"

  For further commandline options (e.g., -n for specifying the size of the sample and -t to specify the accuracy threshold),
  see delSAT --help

  Remark (see user documentation for details):
    For standard (deductive-probabilistic MSE-style) inference problems, it is recommended to run delSAT with arguments
    -mse --solverarg "partDerivComplete" "false"
    For non-MSE deduction-style inference where all parameter atoms are measured atoms, omit -mse and use --solverarg "partDerivComplete" "true"
  */

  var showProgressStats: Boolean = true // switch off progress statistics using --solverarg showProgressStats false

  var diversify: Boolean = false // if true, multi solver aims at generating diverse models (i.e., models which are largely different from each other).
  // Might slow down solver. Might override other settings. NB: Doesn't ensure near-uniform sampling! Also, distribution-aware sampling still takes place if parameter atoms are present.

  var diversifyLight: Boolean = true // similar but less pronounced effect compared with diversify, faster.

  var allowNumFiniteDiff: Boolean = true // if true (=default since 0.4.1), a discrete form of numerical differentiation is used instead of symbolic or automatic differentiation
  // is used to compute the partial derivatives wrt. parameter atoms.
  // Slower and less accurate (you might need to increase the cost threshold with -t), but necessary if a parameter atom variable is
  // not part of the cost function term (or symbolic/automatic differentiation wrt some parameter atom variable isn't possible for some other reason).

  var mixedScenario: Boolean = true // if true, even with allowNumFiniteDiff=true, autom. or symbol. differentiation is
  // used where possible (i.e., for those parameter variables which are measured). With false, a purely numerical differentiation
  // approach is used. True is typically - but not always! - much faster than false.

  var partDerivComplete: Boolean = false // false: variant of ILP'18 approach (less general, use with MSE-style inner cost expressions),
  // true: variant of PLP'18 approach (more general). Some non-MSE-style problems can only be solved with true here.

  // Those of the following settings which end with "...P" are for parallel portfolio solving (see maxSolverThreadsR) - each
  // solver thread is assigned a combination of values from the respective Seq(...) sequences.
  // With a limited number of solver threads, values earlier in sequences get higher priority to be used by a solver thread.
  // Duplicate values allowed in Seqs. Number of values in Seq can be smaller than number of solver threads.

  var maxSolverThreadsR: Int = -1 // for parallel portfolio solving with competing solver instances (number of threads not guaranteed)
  // Keep in mind that the machine might decrease maximum core frequencies with more cores being utilized.
  // -x sets number of solver threads in dependency of number of cores, problem size and other factors. For small
  // problems with number of positive literals (ri.e., in case of SAT: #variables) smaller -x (with x < 0), only a single solver thread is launched.
  // NB: delSAT also spawns some parallelism from within individual solver threads, so normally no all cores should be occupied by solvers.
  // Commandline: --solverarg maxSolverThreadsR n

  var stopSamplingOnStagnation: Boolean = false // if true, we stop sampling if the total cost doesn't significantly change anymore and
  // at least the requested number of models (switch -n) have been generated. Useful mostly for learning weights. However, in
  // deductive-probabilistic and mixed scenarios, cost stagnation before reaching the threshold can
  // also indicate that the input is inconsistent (no solution exists)).

  var innerCostReductFun = (r: DifferentialFunction[DoubleReal], x: DifferentialFunction[DoubleReal]) =>
    new com.accelad.math.nilgiri.autodiff.Sum[DoubleReal](r, x) // if multiple cost terms are specified, this function is used to combine (reduce) them
  // to a single total cost, after also dividing by the number of inner cost functions.
  // Try, e.g., Product instead of Sum if the inner costs are terms referring only to example facts which are mutually probabilistically independent.

  var restartTriggerConfP: (Int, Seq[Int], Seq[Double]) = (2 /*0=no restarts, 1=fixed interval, 2=geometric, 3=Luby sequence*/ ,
    Seq(/*8,32*/ 16) /*initial no of conflicts before restarts*/ ,
    Seq(2d /*32d*/) /*multiplier for geom and luby. Suggestion: try first with 2 for geom or 32 for luby */ )
  // ^ On the commandline, specify like this (no sequences allowed then): --solverarg "restartTriggerConf" "3 32 32"

  var freeEliSearchConfigsP: Seq[Int] = Seq(8, 3) // 0<= item <=11; parallel free eli search (branching) parameter configurations if
  // maxSolverThreadsR != 0.
  // Sequence order determines priority. If there is just one portfolio solver thread (see below), head of tuple is used.
  // Duplicates allowed.
  // On the commandline, use like this: --solverarg "freeEliSearchConfigsP" "5 3 0 3 3 7" (observe that this doesn't specify the
  // number of solver threads which has to be set using maxSolverThreadsR)

  var seedP: Seq[Long] = Seq(-1l) // seed for random number generator in respective solver thread. Values != -1 cannot be used with diversify (see below).

  var rndmIgnLearnedNogoodThresholdP: Seq[Float] = Seq(-0.2f /*0f, -0.1f*/) // Threshold for (x>0: random %, x<0: -%) ignorance of nogoods during BCP

  var arrangeEliPoolP: Seq[Int] = Seq(0, 1) // per solver thread; 0=off, 1=upwards, 2=downwards, 3=shuffle, 4=reshuffle at each restart, 5=(0,1,2,3 or 4 picked at random).
  // Arranges branching eli pool (for free eli search) by number of nogoods containing the eli (relevant where the freeEliSearchApproach chooses from a sequence of elis)

  var rndmBranchP: Seq[Double] = Seq(1e-6d) //Seq(1e-6f) // per solver thread. Very sensitive parameter! Lower(!) positive x <=> higher frequency (as a
  // heuristical weight, not a probability) of selecting the next branching posEli randomly. Higher amount of random branching decisions
  // means higher models entropy (useful for, e.g., weight learning) but slower solving (computing individual models takes more time).
  // Also see parameter "diversify" (which has the same effect as rndmBranch = Double.MinPositiveValue).

  var noHeapP: Seq[Int] = Seq(1, 0) // per solver thread; 0/1 off/on. "On" omits the intermediate heap data structure for
  // BCP (unit propagations) and makes assignments directly and recursively. "Off" uses heap-based Boolean Constraint Propagation (BCP).
  // With "On" (1) you might have to increase the stack size, e.g., -Xss10m.

  var switchToBestConfigAfterFirstModel: Int = 2 // if >0, the portfolio approach which was fastest in the second sampling round is used
  // exclusively (if 2, single threaded then, if 1, still competing using multiple threads if maxCompetingSolverThreads > 1) for
  // all further model solving. NB: it's not guaranteed that the configuration identified as the fastest would also be the fastest in further rounds.

  var ignoreParamVariablesR: Boolean = false // true ignores cost function and parameter/measured atoms. Cost is always assumed to be
  // negative infinity. Not required as such for non-probabilistic problems (you could simply set threshold = Double.MaxValue
  // and use -1 as number of models), but useful for debugging.

  var noOfUnfolds: Int = 0 // for translating away disjunctions in ASP rule heads (an extension over normal ASP), increase the number of unfold operations
  // if necessary (try with 0 first, unless you need the full set of answer sets)

  var maxSamplingIterations = 100000 // stop after this many generated models even if accuracy threshold not reached (not to be confused with trials
  // of the inner (i.e., deduction) loop)

  var localSolverParallelThreshMax: Int = 99999999 // don't use MaxValue here. We use this value just so to be able to multiply by small ints without overflow.

  var localSolverParallelThresh: Int = 150 // = localSolverParallelThreshMax: off.
  // Used (with various factors and conditions, see code) as #items threshold for loop parallelization in various places (TODO: auto).

  var ignoreCostsWithUndefMeasuredAtoms: Boolean = false // if true, inner costs which contain undefined measured atoms are replaced with
  // 0. However, an undefined measured atoms is likely undefined by mistake, so adding a spanning rule for it is normally better.

  // ------ Experimental solver settings (most of these can also be set with --solverarg, if they are var's).
  // Use with care, may not work as expected:

  var maxBurstR: Int = 0 //-5000 // If x>0, the x highest ranked unassigned parameter literals (random variables) are assigned in one go, which can
  // improve optimization performance if many parameter literals are probabilistically independent from each other. If x<0, the actual maxBurst will
  // be automatically determined and varied at runtime in dependency from the current maxBurst and the amount of conflicts generated during BCP,
  // with -x as the initial maxBurst value.
  // x != 0 leads to an increase of conflicts and possibly non-convergence for unsuitable problems.

  var useBurstWithHeap: Boolean = false // for !noHeap, there is some overhead to make it work with maxBurst which might sometimes nullify the benefit of maxBurst

  var burstPlainElis: Boolean = false // if true, maxBurstR also applies to unassigned non-parameter literals.

  var maxBurstAdaptOffset: Double = 0d

  var nogoodShareProbability: Float = 0f // exchange of learned nogoods between solver threads. 0f = no exchange

  var nogoodShareSizeThresh: Int = Int.MaxValue // only learned nogoods with size below that threshold are copied to other threads

  var variableOrNogoodElimConfig: (Boolean, Double, Double, Float, Boolean) = (false /*on/off*/ , 0d /*amount that #resolvents can be larger than original nogood set for candidate variable, in % of nogis */ ,
    0d /*#literals in original nogood set can be larger than literals in resolvents, in % of literals. NB: total #literals can
    still become larger than original total #literals even with 0d here*/ ,
    0.2f /*maximum product of literals with positive or negative occurrence of variable candidate, in % of sqrt(all literals)*/ ,
    false /*true currently not available yet; true materially removes eliminated variables (instead of just ignoring them) <- "true" only
    for SAT mode, not fully working yet. Also see code in findFreeEli() */ )
  // On the commandline, use like this: --solverarg "variableOrNogoodElimConfig" "true 0.5 0.5 0.001 false"

  var progressCheckEveryTrialsR: Int = 15000

  var abandonOrSwitchSlowThreads: Double = 0d //-1.01d  // if != 0, solver threads which seemingly fell behind competing solver threads by a certain amount
  // are aborted, changed in their priority or switched to a different branching approach. See slowThreadAction for the concrete action.
  // "Switch" currently only in terms of free eli search approach.
  // Lower absolute values mean earlier change/removal of seemingly slower solver threads.
  // If x < 0 a different stagnation detection approach is used with different semantics of threshold:
  // floor(-x) determines how frequently progress is checked and the value after the decimal point is the actual threshold.
  // If there is currently only one solver thread, the latter approach (i.e., negative x) is enforced.
  // NB (1): the "slowness" criteria are greedy and cannot guarantee that the abandonded/switched solver threads are actually the least suitable
  // for the problem at hand (but see slowThreadAction = 2 below).
  // NB (2): the frequency of "slowness" checks also depends on setting progressCheckEveryTrialsR (lower value = more frequent checks).
  // NB (3): decreasing progressCheckEveryTrialsR might be necessary

  var slowThreadAction: Int = 0 // determines the action on seemingly slow threads if setting abandonOrSwitchSlowThreads is active.
  // If 0, kill thread (giving remaining threads more CPU time/higher core frequency).
  // If 1, reduce thread priority (if supported by JVM and OS). Since priorities are reduced in relation to other threads' priorities,
  // this approach also allows for indirect increase of priority if the "slower" thread catches up speed at a later point.
  // If 2: as with 1 but reverse action: priorities of "slow" threads are increased, i.e. a non-greedy approach.
  // If 3 and there are different free eli search approaches in current threads, "slow" solver threads are
  // switched to the next approach in the sequence freeEliSearchConfigsP. slowThreadAction = 1 is enforced if slowThreadAction = 0 and there is only one solver thread left.

  var maxApproachSwitchesPerSolverThread: Int = Int.MaxValue // maximum number of switches per solver thread if slowThreadAction = 3

  var emitClauses: Boolean = false // if true, after solving clauses corresponding to clark nogoods and any loop nogoods are printed. Observe that
  // this doesn't emit an equivalent theory in case the ASP program isn't tight since the set of loop nogoods isn't complete. However,
  // if the emitted clauses are used with a SAT solver and the resulting model is an answer set (checkable in P time), it is an answer
  // set of the original answer set program.

  val stopAfterNModels: Boolean = false // if true, we stop sampling after the (using -n) specified number of models have been reached even if
  // the accuracy threshold or cost stagnation has not been reached yet.

  var stagnationTolDiv: Double = 100d  // the threshold used to determine whether there is cost stagnation is calculated as accuracy threshold / stagnationTolDiv

  var enforceStopWhenSampleSizeReached: Boolean = false // with true and -n <n> with n > 0, sampling stops when the specified number of models has
  // been reached even if the cost minimum has not been reached up to the given threshold.

  @volatile var emittedClauses = false

  // ------ Internal solver settings (most of these can also be set with --solverarg, if they are var's).
  // Should normally not changed:

  @deprecated var ensureParamAtomsAreMeasured: Boolean = false // Deprecated; if true, every parameter atom which isn't already a measured atom will
  // be made a measured atom. That's only useful if the weight of the parameter atom needs to be _directly_ controlled during sampling.
  // Normally, autoGenerateCostLinesForHypotheses should be set to true in that case too.

  @deprecated var autoGenerateCostLinesForHypotheses: Boolean = false // Deprecated; generates an inner MSE cost function for each parameter atom which isn't
  // part of any cost, that is, for hypothesis parameter atoms. The generated inner costs are required because for hypotheses and
  // the older numerical diff approach, we needed a (changing, "moving") target probability (computed using an "outer" gradient descent).
  // true requires that ensureParamAtomsAreMeasured is also true.

  var ignoreParamIfNotMeasured: Boolean = false // if true, parameter atoms which aren't also measured atoms are ignored. Works
  // only with allowNumFiniteDiff=true.

  var resetsNumericalOuterLoopOnStagnation: Int = 10 // for allowNumFiniteDiff; if > 0, bag of samples models is cleared if
  // there are no significant cost improvements although the threshold has not been reached yet, in order to escape a local minimum.
  // Decremented after each reset.

  var numFinDiffShuffleProb: Double = 0.0005d   // used with allowNumFiniteDiff to avoid getting stuck in a local minimum. But
  // if this value is too large, nontermination (because of non-convergence to _any_ minimum) can occur.

  var useCounters: Boolean = true // use nogood literal assignment counters instead of head/tail list-like approach

  var levelledRestarts: Boolean = false

  var shuffleRandomVariables: Boolean = true

  var initiallyResolveSingletonNogoods: Boolean = false

  var initCleanUpArrangeClarkNogoods: Boolean = true // leave at true

  var omitSingletonBlits: Boolean = true // leave at true

  var defaultThreshold: Double = 0.01d // default cost function threshold. Lower value = more accurate results. Change as appropriate for problem and cost function(s)
  // To set the threshold, it is recommended to use console argument -t instead of changing this default.

  var absEliScoreInitVal: Float = 1.01f

  var absEliScoreFactP: Seq[Float] = Seq(1.000001f)

  var reviseScoreFreq: Int = 1 // every x conflicts

  var reviseScoreFact: Float = 0.6f // <= 1f; 1f = no rescaling

  var scaleScoreUpdateFactOutOfRange: Float = 1.01f // factor for scaling eliScoreUpdateFact up/down in case the activity sum falls out of range

  var singleLineProgress: Boolean = true // show progress (see above) at a fixed position in the console (doesn't work with most Linux terminals)

  var globalPassCache: Boolean = true

  var primeUnassigned: Boolean = true // always assumed false if globalPassCache = true

  var rearrangeEliPoolOnRestart: Boolean = false

  var probabilisticFactPrefix: String = "_pr_"

  var patFactPrefix: String = "_pat_"

  var costFactPrefix: String = "_cost_"

  var evalFactPrefix: String = "_eval_"

  var probabilisticFactProbDivider: Int = 10000 // since our solver (like most ASP solvers) doesn't support floating point numbers, we divide integers

  var showProbsOfSymbols: Boolean = false // shows the approx. probabilities of all non-auxiliary symbols after sampling (useful for debugging)

  var suppressAnswers: Boolean = false // if true, the resulting models aren't printed (useful if number of sampled models is large)

  val addHocConjunctiveQueries: Seq[Seq[String]] = Seq() // note that this works only for symbols defined in rules - if x is an undefined predicate (or _eval_),
  // addHocQueries cannot be used to deduce Pr(x) = 0.
  /* Example: Seq( // conjunctions c of atoms whose marginal probabilities Pr(c) should be printed after sampling
    Seq("flip(1)", "head(1)"),
    Seq("flip(2)", "head(2)"),
    Seq("flip(3)", "head(3)")
    )
    */

  val addHocDisjunctiveQueries: Seq[Seq[String]] = Seq()  // analogous to addHocConjunctiveQueries, but each element is a clause (disjunction of literals)
    /*Example (SAT mode): Seq(
    Seq("1", "-2", "3"),
    Seq("-1", "3")
    ) */

  //NB: these default setting are overridden in Prob-LP's setSolverSettingDefaults()

  checkSettings

  // ================== ================== ================== ================== ================== ================== ================== ==================

  def checkSettings = {

    if (!(
      seedP == Seq(-1) || !diversify
      ) || variableOrNogoodElimConfig._5 ||
      (autoGenerateCostLinesForHypotheses && !ensureParamAtomsAreMeasured)) {

      //System.out.println(seedP + "," + diversify + "," + variableOrNogoodElimConfig._5 + "," + autoGenerateCostLinesForHypotheses + ", " + ensureParamAtomsAreMeasured)

      delSAT.stomp(-5006)

    }

  }

  // ================== ================== ================== ================== ================== ================== ================== ==================

  val unsafeRefl = classOf[Unsafe].getDeclaredField("theUnsafe")

  unsafeRefl.setAccessible(true)

  val unsafe: Unsafe = unsafeRefl.get(null).asInstanceOf[Unsafe]

  var omitSysExit0 = false // If this .jar is dynamically included in prasp2 using classloader, we must not sys.exit in case of successful termination (except -v/-hashOfPass), as this
  // would quit the overall program. We could prevent this issue using some additional wrapper method, but we want to keep prasp2 compatible with Java tools other than this.
  // If on the other hand the tool is invoked as an external process, sys.exit(0) is required.

  def overrideSolverArgs(additionalSolverArgsR: mutable.HashMap[String, String]) = {

    delSAT.log("additionalSolverArgsR = " + additionalSolverArgsR)

    val additionalSolverArgs = additionalSolverArgsR.map((tuple: (String, String)) => (tuple._1.replaceAllLiterally("\"", "").trim, tuple._2.replaceAllLiterally("\"", "").trim))

    additionalSolverArgs.foreach { case (paramName, paramValueStr) => { // see above for meaning of these parameters

      (paramName, paramValueStr.split("\\s+")) match {

        case ("showProgressStats", Array(v1)) => showProgressStats = v1.toBoolean

        case ("partDerivComplete", Array(v1)) => partDerivComplete = v1.toBoolean

        case ("maxSolverThreadsR", Array(v1)) => maxSolverThreadsR = v1.toInt

        case ("freeEliSearchConfigsP", Array(v@_*)) => freeEliSearchConfigsP = v.map(_.toInt)

        case ("arrangeEliPoolP", Array(v@_*)) => arrangeEliPoolP = v.map(_.toInt)

        case ("restartTriggerConfPe", Array(v1, v2, v3)) => restartTriggerConfP = (v1.toInt, Seq(v2.toInt), Seq(v3.toDouble))

        case ("rndmBranchP", Array(v@_*)) => rndmBranchP = v.map(_.toDouble)

        case ("noHeapP", Array(v@_*)) => noHeapP = v.map(_.toInt)

        case ("switchToBestConfigAfterFirstModel", Array(v1)) => switchToBestConfigAfterFirstModel = v1.toInt

        case ("abandonOrSwitchSlowThreads", Array(v1)) => abandonOrSwitchSlowThreads = v1.toInt

        case ("slowThreadAction", Array(v1)) => slowThreadAction = v1.toInt

        case ("maxApproachSwitchesPerSolverThread", Array(v1)) => maxApproachSwitchesPerSolverThread = v1.toInt

        case ("primeUnassigned", Array(v1)) => primeUnassigned = v1.toBoolean

        case ("rearrangeEliPoolOnRestart", Array(v1)) => rearrangeEliPoolOnRestart = v1.toBoolean

        case ("autoGenerateCostLinesForHypotheses", Array(v1)) => autoGenerateCostLinesForHypotheses = v1.toBoolean

        case ("probabilisticFactPrefix", Array(v1)) => probabilisticFactPrefix = v1.toString

        case ("patFactPrefix", Array(v1)) => patFactPrefix = v1.toString

        case ("costFactPrefix", Array(v1)) => costFactPrefix = v1.toString

        case ("maxBurstR", Array(v1)) => maxBurstR = v1.toInt

        case ("useBurstWithHeap", Array(v1)) => useBurstWithHeap = v1.toBoolean

        case ("burstPlainElis", Array(v1)) => burstPlainElis = v1.toBoolean

        case ("diversify", Array(v1)) => diversify = v1.toBoolean

        case ("absEliScoreInitVal", Array(v1)) => absEliScoreInitVal = v1.toFloat

        case ("absEliScoreFactP", Array(v@_*)) => absEliScoreFactP = v.map(_.toFloat)

        case ("rndmIgnLearnedNogoodThresholdP", Array(v@_*)) => rndmIgnLearnedNogoodThresholdP = v.map(_.toFloat)

        case ("reviseScoreFreq", Array(v1)) => reviseScoreFreq = v1.toInt

        case ("reviseScoreFact", Array(v1)) => reviseScoreFact = v1.toFloat

        case ("localSolverParallelThresh", Array(v1)) => localSolverParallelThresh = v1.toInt

        case ("resetsNumericalOuterLoopOnStagnation", Array(v1)) => resetsNumericalOuterLoopOnStagnation = v1.toInt

        case ("ignoreParamVariablesR", Array(v1)) => ignoreParamVariablesR = v1.toBoolean

        case ("noOfUnfolds", Array(v1)) => noOfUnfolds = v1.toInt

        case ("nogoodShareProbability", Array(v1)) => nogoodShareProbability = v1.toFloat

        case ("nogoodShareSizeThresh", Array(v1)) => nogoodShareSizeThresh = v1.toInt

        case ("progressCheckEveryTrialsR", Array(v1)) => progressCheckEveryTrialsR = v1.toInt

        case ("variableOrNogoodElimConfig", Array(v1, v2, v3, v4, v5)) => variableOrNogoodElimConfig = (v1.toBoolean, v2.toDouble, v3.toDouble, v4.toFloat, v5.toBoolean)

        case ("maxSamplingIterations", Array(v1)) => maxSamplingIterations = v1.toInt

        case ("emitClauses", Array(v1)) => emitClauses = v1.toBoolean

        case ("shuffleRandomVariables", Array(v1)) => shuffleRandomVariables = v1.toBoolean

        case ("allowNumFiniteDiff", Array(v1)) => allowNumFiniteDiff = v1.toBoolean

        case ("numFinDiffShuffleProb", Array(v1)) => numFinDiffShuffleProb = v1.toDouble

        case ("stopSamplingOnStagnation", Array(v1)) => stopSamplingOnStagnation = v1.toBoolean

        case ("stopAfterNModels", Array(v1)) => stopSamplingOnStagnation = v1.toBoolean

        case ("mixedScenario", Array(v1)) => mixedScenario = v1.toBoolean

        case ("ignoreCostsWithUndefMeasuredAtoms", Array(v1)) => ignoreCostsWithUndefMeasuredAtoms = v1.toBoolean

        case ("showProbsOfSymbols", Array(v1)) => showProbsOfSymbols = v1.toBoolean

        case ("suppressAnswers", Array(v1)) => suppressAnswers = v1.toBoolean

        case ("diversifyLight", Array(v1)) => diversifyLight = v1.toBoolean

        case ("ignoreParamIfNotMeasured", Array(v1)) => ignoreParamIfNotMeasured = v1.toBoolean

        case ("stagnationTolDiv", Array(v1)) => stagnationTolDiv = v1.toDouble

        case ("enforceStopWhenSampleSizeReached", Array(v1)) => enforceStopWhenSampleSizeReached = v1.toBoolean

        case (arg: String, Array(v1)) => delSAT.stomp(-1, "--solverarg " + arg + " " + v1)

      }

      checkSettings

    }

    }

  }

  // ================== ================== ================== ================== ================== ================== ================== ================== ==================

  type Eli = Int

  type Nogi = Int

  final case class Rule(headAtomsElis: Array[Eli],
                        bodyPosAtomsElis: Array[Eli],
                        bodyNegAtomsElis: Array[Eli],
                        blit: Eli /*note: if omitSingletonBlits, this is an ordinary (non body) eli if there's just one body literal*/) {

    def toString(context: Preparation): String = {

      import context._

      assert(headAtomsElis.forall(isPosEli(_)))
      assert(headAtomsElis.length == 1) // delSAT supports disjunctive rules, but by this point they are transformed (normalized) already (also any :- constraints)

      if (bodyNegAtomsElis.isEmpty && bodyPosAtomsElis.isEmpty)
        symbols(headAtomsElis.head) + "."
      else {

        symbols(headAtomsElis.head) + " :- " + bodyPosAtomsElis.map(symbols(_)).mkString(", ") +
          ((if (bodyNegAtomsElis.isEmpty || bodyPosAtomsElis.isEmpty) "" else ", ") + bodyNegAtomsElis.map(nEli => "not " + symbols(negateNegEli(nEli))).mkString(", ")) + "."

      }

    }

  }

  val newAspifEliOffsets = 5000000

  val newAspifEliBoundary = Int.MaxValue - newAspifEliOffsets * 3

  val aspifExtraShowEliBoundary = newAspifEliBoundary

  val extraShowAspifElitCount = new java.util.concurrent.atomic.AtomicInteger(0)

  val aspiEliForAuxSymbolForSpanningBoundary = aspifExtraShowEliBoundary + newAspifEliOffsets

  val newFalseAspifElisBoundary = aspiEliForAuxSymbolForSpanningBoundary + newAspifEliOffsets

  val newFalsePredsCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  def isNewFalsePosAspifEli(aspifEli: Int) = aspifEli >= newFalseAspifElisBoundary

  final case class AspifOrDIMACSPlainParserResult(symbols: Array[String],
                                                  rulesOrClauseNogoods: Either[
                                                    /*from aspif:*/ ArrayBuffer[Rule],
                                                    /*from DIMACS:*/ Array[IntArrayUnsafeS]],
                                                  noOfPosBlits: Int,
                                                  externalAtomElis: Seq[Eli], // for aspif only - TODO: #external not implemented yet
                                                  assumptionElis: Seq[Eli], // filtering assumptions
                                                  emptyBodyBlit: Int = -1,
                                                  directClauseNogoodsOpt: Option[Array[IntArrayUnsafeS]] = None /*for debugging/crosschecks*/ ,
                                                  clauseTokensOpt: Option[Array[Array[Int]]],
                                                  symbolToEliOpt: Option[Predef.Map[String, Eli]],
                                                  additionalUncertainAtomsInnerCostsStrs: (Array[String], Array[String], Array[String] /*<-original _eval_ terms*/ ) //additionalUncertainAtomsSeprtOpt: Option[UncertainAtomsSeprt]
                                                  // ^ we allow probabilistic parameter atoms to be
                                                  // stated as ASP facts too in the aspif, in addition to those provided using "pats" and "cost" lines.
                                                  // They are treated as MSE inner cost functions.
                                                 ) {}

  type RandomGen = java.util.SplittableRandom

  val rngGlobal: java.util.Random = new XORShift32() // Not normally to be used. Also not thread-safe. We use different random number generators within the solver threads.

  val rngGlobalRG = new java.util.SplittableRandom()

  @inline def shuffleArray[A](array: mutable.Seq[A], rg: RandomGen, to: Int = -1): Unit = { // plain Fisher-Yates shuffle on init of array

    if (to < 0 && array.length >= 16384)
      shuffleArrayBlocked[A](array, rg)
    else {

      val l = if (to < 0) array.length - 1 else to

      var i = l

      while (i > 0) {

        val j = rg.nextInt(i + 1)

        val temp = array(j)

        array(j) = array(i)

        array(i) = temp

        i -= 1

      }

    }

  }

  @inline def shuffleArrayUnsafe(array: IntArrayUnsafeS, rg: /*java.util.Random*/ RandomGen, to: Long = -1): Unit = { // plain Fisher-Yates shuffle

    val l = if (to < 0l) array.sizev - 1 else to

    var i: Long = l

    while (i > 0l) {

      val j = rg.nextInt(i.toInt + 1)

      val temp = array.get(j)

      array.update(j, array.get(i))

      array.update(i, temp)

      i -= 1

    }

  }

  @inline def shuffleArrayBlocked[A](arr: mutable.Seq[A], rg: RandomGen): Unit = { // Blocked Fisher-Yates shuffle
    // (method code based on public domain code from https://github.com/lemire/Code-used-on-Daniel-Lemire-s-blog)

    def swap(i: Int, j: Int) = {

      val tmp = arr(i)

      arr(i) = arr(j)

      arr(j) = tmp

    }

    val size = arr.length

    val block = 1024

    val buffer = Array.ofDim[Int](block)

    var i = size

    while (i > block + 1) {

      var k = 0

      while (k < block) {

        buffer(k) = rg.nextInt(i - k)

        k += 1

      }

      k = 0

      while (k < block) {

        swap(i - 1 - k, buffer(k))

        k += 1

      }

      i -= block

    }

    while (i > 1) {

      swap(i - 1, rg.nextInt(i))

      i -= 1

    }

  }

  class ArrayValExtensible[T: Numeric : ClassTag](var buffer: Array[T]) { // our low-level non-boxing replacement for
    // a growable-only ArrayBuffer. Similar to ArrayBuilder, but with random access and traversal.
    // NB: buffer may be modified, so before calling constructor, clone if necessary.

    var l = buffer.length // generally, buffer contains items only up to index l-1, which might be less than buffer.length-1

    var incSize = l / 4

    @inline def setContent(content: Array[T]) = {

      buffer = content

      l = buffer.length

    }

    @inline def getContent = {

      buffer.take(l)

    }

    @inline def getContentExceptInt(except: Int) = {

      val ab = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val item = buffer(i).asInstanceOf[Int]

        if (item != except)
          ab += item

        i += 1

      }

      ab.result()

    }

    @inline def length = l

    @inline def bufferSize = buffer.length

    @inline def get(index: Int): T = buffer(index)

    @inline def traverseUntil(itemOp: T => Boolean) = {

      var i = 0

      var stop = false

      while (!stop) {

        stop = i >= l || itemOp(buffer(i))

        i += 1

      }

    }

    @inline def count(pred: T => Boolean): Int = {

      var i = l - 1

      var count = 0

      while (i >= 0) {

        if (pred(buffer(i)))
          count += 1

        i -= 1

      }

      count

    }

    @inline def append(item: T) = {

      if (l >= buffer.length) {

        val newContent: Array[T] = Array.ofDim[T](l + incSize)

        incSize += 300

        Array.copy(buffer, 0, newContent, 0, buffer.length)

        buffer = newContent

      }

      buffer(l) = item

      l += 1

    }

    @inline def removeItem(item /*<- not an index*/ : T): Int /*Index of removed item (only the first occurrence is considered), or -1 */ = {

      var indexOfItem = -1

      var i = 0

      while (i < l && indexOfItem == -1) {

        if (buffer(i) == item)
          indexOfItem = i

        i += 1

      }

      if (indexOfItem >= 0) {

        System.arraycopy(buffer, indexOfItem + 1, buffer, indexOfItem, l - 1 - indexOfItem)

        l -= 1

      }

      indexOfItem

    }

    @inline def removeIntItemsRange(from: Int /*first item, not an index!*/ , to: Int): Unit = {

      val bld: ArrayBuilder.ofInt = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val bi = buffer(i).asInstanceOf[Int]

        if (bi < from || bi > to)
          bld.+=(bi)

        i += 1

      }

      buffer = bld.result().asInstanceOf[Array[T]]

      l = buffer.length

    }

  }

  class ArrayValExtensibleIntUnsafe(var buffer: IntArrayUnsafeS) { // our unsafe low-level non-boxing replacement for
    // a growable-only ArrayBuffer. Similar to ArrayBuilder, but with random access and traversal.
    // NB: buffer may be modified, so before calling constructor, clone if necessary.

    var incSize = 128

    var l = buffer.sizev // generally, buffer contains items only up to index l-1, which might be less than buffer.length-1

    @inline def this(bufferLen: Int, incr: Int) {

      this(new IntArrayUnsafeS(sizev = bufferLen, aligned = false))

      l = 0

      incSize = incr

    }

    @inline def this(bufferA: Array[Int], c: Boolean = false, setFromBufferR: Boolean = true) {

      this(new IntArrayUnsafeS(bufferA.length, aligned = false))

      if (setFromBufferR)
        buffer.setFromIntArray(bufferA)

    }

    @inline def setContent(content: Array[Int]) = {

      buffer.setFromIntArray(content)

      l = buffer.sizev

    }

    @inline def getContent: Array[Int] = {

      buffer.toArray.take(l)

    }

    @inline def getContentExceptInt(except: Int) = {

      val ab = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val item = buffer.get(i)

        if (item != except)
          ab += item

        i += 1

      }

      ab.result()

    }

    @inline def getContentUnsafeExceptInt(except: Int): IntArrayUnsafeS = {

      val ab = new IntArrayUnsafeS(length, aligned = false)

      var i = 0

      var j = 0

      while (i < l) {

        val item = buffer.get(i)

        if (item != except) {

          ab.update(j, item)

          j += 1

        }

        i += 1

      }

      ab.sizev = j

      ab

    }

    @inline def length = l

    @inline def bufferSize = buffer.sizev

    @inline def get(index: Int): Int = buffer.get(index)

    @inline def get(index: Long): Int = buffer.get(index)

    @inline def traverseUntil(itemOp: Int => Boolean) = {

      var i = 0

      var stop = false

      while (!stop) {

        stop = i >= l || itemOp(buffer.get(i))

        i += 1

      }

    }

    @inline def contains(item: Int, until: Int): Boolean = {

      var i = until - 1

      while (i >= 0) {

        if (buffer.get(i) == item)
          return true

        i -= 1

      }

      false

    }

    @inline def append(item: Int) = {

      //val zero: T = implicitly[Numeric[T]].zero

      if (l >= buffer.sizev) {

        buffer = buffer.clone(incSize)

      }

      buffer.update(l, item)

      l += 1

    }

    @inline def removeIntItemsRange(from: Int /*item, not an index!*/ , to: Int): Unit = {

      var i = l - 1

      while (i >= 0) {

        val bi = buffer.get(i)

        if (bi >= from && bi <= to) {

          buffer.remove(i)

          l -= 1

        }

        i -= 1

      }

    }

  }

  @inline def timerToElapsedMs(startNano: Long): Long = (System.nanoTime() - startNano) / 1000000

  @inline def next2Pow(x: Int) = if (x == 0) 0 else 1 << (32 - Integer.numberOfLeadingZeros(x - 1))

  @inline def binLog(x: Int): Int = {

    //assert(x != 0)

    31 - Integer.numberOfLeadingZeros(x)

  }

}
