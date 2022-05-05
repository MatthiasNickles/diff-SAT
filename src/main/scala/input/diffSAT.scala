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

package input

import java.io._
import java.util.concurrent.locks.ReentrantLock

import com.sun.management.OperatingSystemMXBean // can be safely omitted if delayed start feature not needed (see further below)

import aspIOutils._
import userAPItests.APITests
import sharedDefs.{runAPITests, _}

import solving.{Preparation, SamplingResult, SolverMulti}

import utils.{ByteArrayUnsafeS, DoubleArrayUnsafeS, FloatArrayUnsafeS, Stats}
import utils.Various._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  *
  * @author Matthias Nickles
  *
  */
object diffSAT extends APITests {

  /*

  diff-SAT console use examples see README.md and --help
  For how to use diff-SAT using its User API, see doc of [[input.ProbabilisticAnswerSetProgram]] and [[input.BooleanFormulaWithCosts]].
  For list of global settings see [[sharedDefs]] and --help

  */

  val version = "0.5.3"

  val copyright = "Copyright (c) 2018-2022 Matthias Nickles\nLicense: https://github.com/MatthiasNickles/diff-SAT/blob/master/LICENSE"

  val copyrightAndVersionText = "diff-SAT " + version + "\n" + copyright

  val defaultCmdlNoOfModelsStr = "-1"

  val defaultCmdlOffHeapGarbageCollectionModeR = "-1" //see solver.SampleMultiConf.offHeapGarbageCollectionMode for possible values

  val thirdPartyLibs = "diff-SAT " + version +
    """ uses or links the following third-party software:

   JAutoDiff
     Copyright (c) 2012 uniker9 (https://github.com/uniker9/JAutoDiff)
     License: https://github.com/uniker9/JAutoDiff/blob/master/LICENSE.txt
     Copyright (c) 2017 AccelaD (https://github.com/accelad-com/nilgiri-math/tree/master/src/main/java/com/accelad/math/nilgiri)
     License: https://github.com/accelad-com/nilgiri-math/blob/master/src/main/java/com/accelad/math/nilgiri/LICENSE

   Parsington (https://github.com/scijava/parsington)
     Copyright (c) 2015-2016, Board of Regents of the University of Wisconsin-Madison
     License: https://github.com/scijava/parsington/blob/master/LICENSE.txt

   fastutil (http://fastutil.di.unimi.it)
     Copyright (c) 2002-2017 Sebastiano Vigna
     License: https://github.com/vigna/fastutil/blob/master/LICENSE-2.0

   Apache Commons Math (https://commons.apache.org/proper/commons-math/)
     License: https://github.com/apache/commons-math/blob/master/LICENSE.txt

   jsoniter (https://jsoniter.com/)
     Copyright (c) 2016 Tao Wen
     License: https://github.com/json-iterator/java/blob/master/LICENSE

   """

  val helpText =
    """
     SAT and ASP portfolio solver for probabilistic SAT/ASP and sampling-based
     multi-model optimization using Differentiable Satisfiability.

     Default global PRNG seed (override with --solverarg seedRngGlobalR <s>):
     """ + (if (seedRngGlobalR == -1l) "[random number]" else seedRngGlobalR) +
      """

      Command line parameters:

             [<filename>] [--version|-v|--about] [--help|-h]
             [-n <n>] [-s <s>] [-t <t>] [-ci] [-mse] [-gc <gc>]
             [[--thread i] [--solverarg "name" "value"]*]*
             [--showaux] [--verbose] [--writestatsto <dir>]

      Reads from a file or STDIN input programs or clauses in aspif or
      DIMACS-CNF format or extended aspif or DIMACS with list of parameter
      atoms and cost function(s). To obtain aspif from a non-ground plain
      Answer Set Program, preprocess using, e.g.,
      clingo myProg.lp --trans-ext=all --pre=aspif
      Input is obtained from STDIN if no file name is provided or if
      flag -ci is specified.

      Parameters:

      -n <n> with n>0 lets the sampler sample at least n (not necessarily
      different) models such that the sampled multiset of models solves
      the given cost up to the specified accuracy if possible (or the
      maximum number of trials is reached). Target accuracy
      is specified using an error threshold (see parameter -t below).

      If -n is absent or n = -1, sampling generates models until a minimum
      multiset of models has been generated st. the specified or default
      error threshold (or maximum number of trials) is reached (a
      multisolution).

      If n < -1, sampling firstly generates a minimum multiset of size m
      to reach a cost minimum (as with -n -1) and then samples -n-m
      further models uniformly from the minimum multiset (that is, it
      "fills" the minimum sample up by sampling uniformly from it).
      Primary use case of -n with n>0 is to increase of solution entropy
      by sampling a larger number of models.

      -s <s> with s>0 samples n models uniformly with replacement from
      the discovered multisolution (i.e., the multiset that would be
      printed with -n alone). Observe that diff-SAT possibly finds different
      multisolutions when called multiple times for the same input.
      Only these models are printed with -s. -s allows for a different
      sampling semantics - if, e.g., a Boolean variable 'a' is assigned
      (via the cost) probability 0.6, -n -1 results in a multiset of models
      where in 60% of all models 'a' holds. In contrast, with -s 1 only
      a single model is printed. With probability 0.6, in this model 'a'
      holds and with probability 0.4 'a' does not hold.

      Models are either stable models (answer sets) or satisfying Boolean
      assignments (in case the input is in DIMACS CNF or in PCNF
      (Probabilistic SAT) format).

      -t <threshold> specifies the error threshold for the total cost
      function (small threshold means higher accuracy but more time
      required for sampling).

      -mse promises that the costs are provided entirely as part costs
      with inner MSE terms of the form (p-f(v))^2 where p is a probability
      and v is a parameter atom symbol (random variable). -mse is optional
      even for MSE-type costs but allows for faster parsing of large lists
      of such functions.

      -gc <gc> specifies the off-heap garbage collection mode. <gc>=0:
      no off-heap garbage collection. <gc> = 1: perform off-heap garbage
      collection when estimated available off-heap memory falls below 50%.
      <gc> = -1 (default): sets garbage collection mode using a heuristics
      based on the number of requested models and whether sampling
      is performed. <gc> = 2: enforces garbage collection after each model
      regardless of available memory.
      If diff-SAT runs out of memory, increase JVM heap using -Xmx and use
      -gc 1.
      -Xmx is also relevant for off-heap(!) available memory estimation
      (lower -Xmx: more frequent off-heap garbage collection).

      --solverarg "argname" "value" is used to specify an advanced solver
      argument.
      See sharedDefs.scala for the full list and default values of
      such arguments.
      Multiple --solverarg can be specified. Use --thread to group
      --solverarg arguments threadwise in the overall solver portfolio.
      Examples:
        --solverarg timeoutMs 600000 specifies a solver timeout of 10 min.
        --solverarg partDerivComplete true (activates support for certain
        non-MSE-style costs, see documentation)
        --solverarg maxSolverThreadsR 6 --solverarg freeEliSearchConfigsP "15 15 12"
        activates parallel portfolio solving using max. 6 threads and branching
        approaches 15,15,12 (i.e. approach 15 for the first two threads, 12 for
        the third and the default branching approach (see sharedDefs) for
        threads $4, $5 and $6).
        --solverarg diversify true (aims at generating more diverse models,
        but typically decreases speed)

      --thread i associates the following set of --solverarg arguments with
      thread $i, i>0.
      If no --thread is provided earlier in the parameter list, the
      --solverarg argument is used as a default if the number of actual solver
      threads exceeds the number of provided --thread arguments.
      Observe that only those settings in sharedDefs.scala whose names end
      with "P" can differ across individual threads. The other settings have
      the same value in all threads, regardless of any preceding --thread
      argument.
      Important: the number of --thread arguments does NOT determine the
      actual number of solver threads. Use --solverarg maxSolverThreadsR n
      to specify the number of threads (if omitted, a heuristically determined
      number based on the number of cores is used).
      Example:
        --solverarg seedP 1 --thread 1 --solverarg seedP 123 --thread 2 --solverarg seedP 456
      If there are four actual solver threads, this makes thread $1 use seed
      123, thread $2 use seed 456 and threads $3 and $4 use seed 1.

      --showaux also prints in models auxiliary atoms introduced for spanning
      formulas (omitted by default)

      -ci enforces reading from STDIN

      --writestatsto <dir> creates a JSON file with runtime statistics in
      folder <dir>.
      The data in this file can be analyzed using program RuntimeStats. Runtime
      statistics file generation is also active in debug mode.

      --verbose shows additional information about the solving and sampling
      process

      --version|-v|--about prints information about version and third-party
      software used by diff-SAT (including copyrights and license information),
      then exits.

      --help|-h prints this information and exits
     """

  /* Internal use only:

      --batchtests <folder>  (don't use with large number of files. Split such a folder into several folders)
      --apitests
      --timeoutbench <sec> (don't use. Use external script for wall-clock time-based benchmarking instead)

   */

  @inline def osWin: Boolean = System.getProperty("os.name").toLowerCase().contains("win")

  @inline def changeConsoleWidthUnderWin = true

  // ==================================================================================================================

  object MessageTypes extends Enumeration {

    type MessageType = Value

    val /*INFO,*/ WARNING, ERROR = Value
    //(we don't use a logger since we don't write a significant amount of log messages, and for
    // performance reasons we need to guard any message emission anyway with, e.g., if(debug)...)

  }

  import MessageTypes._

  val stompMessages = Map(

    -1 -> ("Invalid command line argument", ERROR),

    -2 -> ("File error", ERROR),

    -3 -> ("External program call failed", ERROR),

    -4 -> ("I/O error", ERROR),

    -5 -> ("JVM option couldn't be set at runtime. It is recommended to specify it on the command line", WARNING),

    -100 -> ("Invalid input data", ERROR),

    -101 -> ("Timeout or maximum number of trials exceeded. Sampling aborted", WARNING),

    -102 -> ("Unsupported line in aspif input", ERROR),

    -103 -> ("Weighted atoms only supported via cost functions", ERROR),

    -104 -> ("Disjunctive head(s) found in ASP rules. Translation of disjunctions using current shift/unfold settings doesn't guarantee that any or all answer sets are discovered.\n Consider increasing the number of unfolds in case of non-convergence.", WARNING),

    -200 -> ("Unknown operator in expression", ERROR),

    -201 -> ("Call of unknown function in expression", ERROR),

    -202 -> ("Syntax error in cost function", ERROR),

    -203 -> ("Undefined predicate in possible measured atom position in cost function", WARNING),

    -204 -> ("Undefined predicate in measured or parameter atoms set, its frequency will always be 0 in cost functions", WARNING),

    -205 -> ("Constant inner cost function (possibly because of an undefined measured atom)", WARNING),

    -206 -> ("Unrecognized variable or constant in cost function", WARNING),

    -207 -> ("Costs and parameter variables ignored (ignoreParamVariablesR=true)", WARNING),

    -208 -> ("Inner cost replaced with zero (ignoreCostsWithUndefMeasuredAtoms=true)", WARNING),

    -209 -> ("Undefined " + evalFactPrefix + " term", ERROR),

    -5000 -> ("Specified local greedy decision policy won't work as expected since some measured atoms are not parameter atoms", WARNING),

    -5001 -> ("Lists of parameter or measured atoms found both separately given and within DIMACS-CNF-PR - using only the former lists.", WARNING),

    -5002 -> ("assureIsTight=true; This will lead to non-termination or wrong results if the ASP program isn't tight.", WARNING),

    -5003 -> ("Inner cost function(s) might not work with current approach to differentiation.\n Consider removing -mse (if present) and adding argument --solverarg partDerivComplete true", WARNING),

    -5004 -> ("Unsupported type of rule", ERROR),

    -5005 -> ("Undefined predicate", WARNING),

    -5007 -> ("Experimental feature, might give wrong results", WARNING),

    -5008 -> ("Sampling ended but specified threshold not reached", WARNING), // also see -5018

    -5009 -> ("Invalid settings", ERROR),

    /*deprecated*/ -5010 -> ("Literal scores out of valid range. Setting 'eliScoreUpdateFact' will be adapted in current solver thread.", WARNING),

    -5011 -> ("Cost stagnates, sampling aborted (set flag stopSamplingOnStagnation to false to change this behavior)", WARNING),

    -5012 -> ("enforceStopWhenSampleSizeReached = true (i.e., sampling stops after n models even if specified cost minimum not reached yet)", WARNING),

    -5013 -> ("Index out of bounds", ERROR),

    -5014 -> ("Incompatible settings; ignored or amended", WARNING), // use where incompatibility is benevolent

    -5015 -> ("Number of solver threads too small to accommodate all portfolio setting combinations. A random subset will be used", WARNING),

    -5016 -> ("Setting not recommended", WARNING),

    -5017 -> ("Setting may cause problems", WARNING),

    -5018 -> ("Sampling aborted because of timeout", WARNING), // also see -5008

    -5019 -> ("Absent unnegated form of classically negated atom", WARNING),

    -5020 -> ("Parser warning", WARNING),

    -6000 -> ("Corrupt or invalid JSON statistics file", WARNING),

    -10000 -> ("Internal error", ERROR),

    -10001 -> ("Internal serialization error", ERROR),

    -10002 -> ("Internal warning", WARNING),

    -20000 -> ("Batch testing failure", ERROR),

    -20001 -> ("Batch testing warning", WARNING),

  )

  def stomp(code: Int, additionalInfo: String = ""): Unit = {

    val message = stompMessages(code)

    val fullMessage = " [" + code + "]: " + message._1 + ": " + additionalInfo

    if (message._2 == ERROR) {

      System.err.println("\nError" + fullMessage)

      if (code != -10001 && writeRuntimeStatsToFile)
        stats.writeToFile()

      sys.exit(code)

    } else if (message._2 == WARNING)
      System.err.println("\nWarning" + fullMessage)
    else
      assert(false)

  }

  /*
  @inline def log(debugMessage: => Any): Unit = {  // even using call-by-name this could be too slow (depending on compiler optimization)

    if (debug)
      System.out.println(debugMessage.toString)

  } */

  var fileNameOpt: Option[String] = None

  var stats: Stats = null

  val diffSATGlobalLock = new ReentrantLock()

  @inline def parseDouble(s: String): Option[Double] = { // TODO move elsewhere

    try {

      Some(s.toDouble)

    } catch {

      case _: NumberFormatException => None

    }

  }

  /**
    * Reads input from file (if file name is given) or STDIN (in various alternative formats, with input typically generated by prasp2)
    *
    * @param fileNameOpt
    * @param mseInCommandLineOpt see command line option -mse
    * @return Option[InputData]
    */
  def obtainInputFromText(fileNameOpt: Either[Option[String], String], mseInCommandLineOpt: Option[Boolean]): (InputData, Boolean,
    /*inline arguments (if any)-->*/ Option[(mutable.HashMap[Symbol, List[String]], mutable.HashMap[(String, Int), String])],
    /*commentInFileSaysUNSAT, ...SaysSAT-->*/ (Boolean, Boolean),
    /*Inline probability checks (if any)-->*/ Option[(Double, Iterator[(String, Double)])],
    /*Inline set of expected models (if any) using c (or 10) #all_models {model} {model} ... -->*/ Option[Array[Array[Pred]]],
    /*Inline set of expected models using c #all_models_begin\nc model\nc model\n... c #all_models_end*/ Option[Array[Array[Pred]]]) = {

    /* Remark: We receive the inner cost functions (if any) as plain text formulas which we need to convert
       to DifferentialFunction[DoubleReal] here.

       There are two stages for each inner cost function:
          1) as an incoming cost string, e.g., (0.5-f(v))^2, where the arguments v of function f are measured atoms
          2) in autodiff format, with f(atom) everywhere replaced with variable freqx_(eli_of_v)
    */

    import java.nio.charset.StandardCharsets

    val inputStr: String = fileNameOpt match {

      case Left(Some(fileName)) => {

        import java.nio.file.{Files, Paths}

        try {
/*
          val checkUTF16Buffer: Array[Byte] = new Array[Byte](2)

          val checkIS = new java.io.RandomAccessFile(Paths.get(fileName).toAbsolutePath.toString, "r")

          checkIS.readFully(checkUTF16Buffer)

          val probablyUtf16 = checkUTF16Buffer(0) <= 0.toByte && checkUTF16Buffer(1) <= 0.toByte

          new String(Files.readAllBytes(Paths.get(fileName)), if(probablyUtf16) StandardCharsets.UTF_16 else StandardCharsets.UTF_8) */

          val checkUTF16OrBOM_Buffer: Array[Byte] = new Array[Byte](3)

          val checkIS = new java.io.RandomAccessFile(Paths.get(fileName).toAbsolutePath.toString, "r")

          checkIS.readFully(checkUTF16OrBOM_Buffer)

          val hasBOM = checkUTF16OrBOM_Buffer(0) == 0xEF.toByte && checkUTF16OrBOM_Buffer(1) == 0xBB.toByte && checkUTF16OrBOM_Buffer(2) == 0xBF.toByte

          val probablyUtf16 = !hasBOM && checkUTF16OrBOM_Buffer(0) <= 0.toByte && checkUTF16OrBOM_Buffer(1) <= 0.toByte

          val contentBytes = Files.readAllBytes(Paths.get(fileName))

          new String(if(hasBOM) contentBytes.drop(3) else contentBytes, if(probablyUtf16) StandardCharsets.UTF_16 else StandardCharsets.UTF_8)

        } catch {

          case e: java.nio.file.NoSuchFileException => {

            stomp(-2, "File not found: " + fileName)

            ""

          }

          case e: Exception => {

            stomp(-4, e.toString)

            ""

          }

        }

      }

      case Left(None) => {

        val inStream: BufferedInputStream = new BufferedInputStream(System.in, 32768)

        slurpFromInputStream(inStream)

      }

      case Right(progStr) => progStr

    }

    val satMode = !inputStr.startsWith("asp")

    val (inlineArgsOpt, commentInFileSaysUNSAT, commentInFileSaysSAT, inlineProbabilityChecksOpt,
    inlineAllModelsCheckTokensOpt, inlineAllModelsMultilineCheckTokensOpt) = if (runBatchTests) {

      // We extract comments (i.e., after c ... (cnf) respectively 10 ... (aspif)) which start
      // with # to allow file-specific inline arguments (same format as command line arguments) and also batch testing to
      // do some basic result checks.

      // #... is currently used only internally for debugging purposes - for documentation
      // see _KnowledgeBase_diffSAT_internal.txt

      val inlineArgsChecksConsiderationStr = inputStr.take(1024)

      val (commentInFileSaysUNSAT, commentInFileSaysSAT) =
        (inlineArgsChecksConsiderationStr.contains("#sat? false"),
          inlineArgsChecksConsiderationStr.contains("#sat? true"))

      if (inlineArgsChecksConsiderationStr.contains("WARNING:"))
        stomp(-20001, "Batch test file " + fileNameOpt.left.get.get + " contains a warning (see file for details)")

      //E.g., #cmdl --solverarg diversify true -n 1000
      val inlineCmdlPattern = raw"(#cmdl\s+)(.+)".r

      val inlineCmdlMatchOpt = inlineCmdlPattern.findFirstMatchIn(inlineArgsChecksConsiderationStr)

      val inlineArgsOpt: Option[(mutable.HashMap[Symbol, List[String]], mutable.HashMap[(String, Int), String])] =
        inlineCmdlMatchOpt.map { inlineCmdlMatch =>

          val inlineCmdl = inlineCmdlMatch.group(2)

          val cdlSplitPattern = "([^\"]\\S*|\".+?\")\\s*".r // doesn't account for inner quotes or escaped quotes

          val m = cdlSplitPattern.findAllIn(inlineCmdl.trim)

          val inlineArgs = m.map(_.trim.stripPrefix("\"").stripSuffix("\"").trim).toArray

          val (parseInlineArgs: ArgsList, advancedSolverArgsFromInline: mutable.HashMap[(String, Nogi), String]) =
            parseArgs(args = inlineArgs)

          // println(parseInlineArgs + "\n" + advancedSolverArgsFromInline)

          val parseInlineArgsAsMap = mutable.HashMap[Symbol, List[String]]().++(parseInlineArgs.toMap)

          (parseInlineArgsAsMap, advancedSolverArgsFromInline)

        }

      //E.g., 10 #exp_pr 0.01 "__aux_R_1_2(132,217)" 0.8 "__aux_R_1_2(131,115)" 0.8
      val inlineProbabilityCheckPattern = raw"(#exp_pr\s+)(.+)".r

      val inlineProbabilityCheckMatchOpt = inlineProbabilityCheckPattern.findFirstMatchIn(inlineArgsChecksConsiderationStr)

      val inlineProbabilityCheckTokensOpt: Option[Array[String]] = inlineProbabilityCheckMatchOpt.map { inlineProbabilityCheckMatch =>

        val inlineProbabilityChecks = inlineProbabilityCheckMatch.group(2)

        val cdlSplitPattern = "([^\"]\\S*|\".+?\")\\s*".r // doesn't account for inner quotes or escaped quotes

        val m = cdlSplitPattern.findAllIn(inlineProbabilityChecks.trim)

        m.map(_.trim.stripPrefix("\"").stripSuffix("\"").trim).toArray

      }

      val inlineProbabilityChecksOpt: Option[(Double, Iterator[(String, Double)])] = inlineProbabilityCheckTokensOpt.map { tokens: Array[String] => {

        val tolerance = tokens(0).toDouble

        val atomsAndProbs: Iterator[(String, Double)] = tokens.drop(1).sliding(2, 2).map(ap => (ap(0), ap(1).toDouble))

        (tolerance, atomsAndProbs)

      }
      }

      // E.g., 10 #all_models { blub(1,2) b a} { x  y z  } {m} {} {  u(v,w)  }
      val inlineAllModelsCheckPattern = raw"(#all_models\s+)(.+)".r

      val inlineAllModelsCheckMatchOpt = inlineAllModelsCheckPattern.findFirstMatchIn(inlineArgsChecksConsiderationStr)

      val inlineAllModelsCheckTokensOpt: Option[Array[Array[Pred]]] = inlineAllModelsCheckMatchOpt.map { inlineProbabilityCheckMatch =>

        val inlineAllModelsChecks = inlineProbabilityCheckMatch.group(2)

        val modelPattern = raw"\{.*?\}".r

        val m = modelPattern.findAllIn(inlineAllModelsChecks.trim)

        val r = m.map(_.trim.stripSuffix("}").stripPrefix("{").trim.split("\\s+"))

        // println(r.map(_.mkString(";")).mkString("\n"))

        r.toArray

      }

      val inlineAllModelsMultilineCheckPattern = raw"(?s)(#all_models_begin[\s\\n\\r\\t]*)([\S\\n\\r\s]+)((c|10)\s#all_models_end[\s\\n\\r\\t]*)".r

      val inlineAllModelsMultilineCheckMatchOpt = inlineAllModelsMultilineCheckPattern.findFirstMatchIn(inlineArgsChecksConsiderationStr)

      val inlineAllModelsMultilineCheckTokensOpt: Option[Array[Array[Pred]]] = inlineAllModelsMultilineCheckMatchOpt.map { inlineProbabilityCheckMatch =>

        val inlineAllModelsMultilineChecks = inlineProbabilityCheckMatch.group(2)

        val modelPattern = raw"(.+)[\s\\r\\n]*".r

        val m = modelPattern.findAllIn(inlineAllModelsMultilineChecks.trim)

        val r = m.toSeq.map(_.trim.stripPrefix("c ").stripPrefix("10 ").trim.split("\\s+")).toArray

        //println(r.map(_.mkString(";")).mkString("\n"))

        r

      }

      (inlineArgsOpt, commentInFileSaysUNSAT, commentInFileSaysSAT, inlineProbabilityChecksOpt, inlineAllModelsCheckTokensOpt, inlineAllModelsMultilineCheckTokensOpt)

    } else // if not in batch testing mode, special #-comments in input files are ignored
      (None, false, false, None, None, None)

    if (inputStr.startsWith("asp ") || inputStr.startsWith("p cnf ") || inputStr.startsWith("p pcnf ") || inputStr.startsWith("c ")) { // we allow "c " as first line in DIMACS too, but not, e.g., "cx"

      val posExtras = if (ignoreParamVariablesR) {

        stomp(-207)

        -1

      } else inputStr.indexOf("\npats ")

      val mse: Boolean = mseInCommandLineOpt.getOrElse(inlineArgsOpt.getOrElse((mutable.HashMap[Symbol, List[String]](), mutable.HashMap[(String, Int), String]()))._1.contains('mse))
      // ^we need to know mse already now, for parseOptimizationTerms()

      val spanningProgramASPNormGroundAspif_OrDIMACSCNF = if (posExtras == -1) inputStr.trim else inputStr.substring(0, posExtras - 1).trim

      val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult = if (!satMode)
        AspifPlainParser.parseAspif(spanningProgramASPNormGroundAspif_OrDIMACSCNF,
          shiftAndUnfoldForDisjunctions = true, maxNoOfUnfolds = maxNoOfUnfolds)
      else
        DIMACPlainSparser.parseDIMACS(spanningProgramASPNormGroundAspif_OrDIMACSCNF)

      if (inputStr.startsWith("p pcnf "))
        println("\nAuxiliary Boolean variables introduced for PCNF: " + aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._1.mkString(",")) // these are currently not filtered out in the final answers,
      // so we better tell the user about them to avoid confusion

      val paramAtomsAndInnerCostsStrOpt = if (posExtras == -1) None else Some(inputStr.substring(posExtras).trim)

      val r: (InputData, Boolean) = ParseOptimizationTerms.parseOptimizationTerms(mse = mse,
        paramAtomsAndInnerCostsStrOpt = paramAtomsAndInnerCostsStrOpt, /*inputStr,*/
        satMode = satMode, aspifOrDIMACSParserResult = aspifOrDIMACSParserResult)

      (r._1, r._2, inlineArgsOpt, (commentInFileSaysUNSAT, commentInFileSaysSAT), inlineProbabilityChecksOpt, inlineAllModelsCheckTokensOpt, inlineAllModelsMultilineCheckTokensOpt)

    } else {

      if (inputStr(0).isWhitespace)
        stomp(-100, "Observe that input files are not allowed to start with whitespace characters")
      else
        stomp(-100)

      (null, false, inlineArgsOpt, (commentInFileSaysUNSAT, commentInFileSaysSAT), inlineProbabilityChecksOpt, inlineAllModelsCheckTokensOpt, inlineAllModelsMultilineCheckTokensOpt)

    }

  }

  /**
    * Wrapper method for invoking the multimodel sampler - don't invoke directly when using the User API, use [[input.ProbabilisticAnswerSetProgram#solve(input.SolverParametersOverlay, scala.Option)]] instead.
    *
    * See sampleMulti() in SolverMulti.scala for the actual sampling method.
    *
    * @param inputData
    * @param advancedSolverParametersOverlay
    * @param satMode
    * @return Sample (bag of sampled models) in symbolic form and as list of (eli array, eli hash set). An eli is our internally used numerical representation
    *         of a literal (not identical to numerical literals in DIMACS or aspif!).
    */
  def invokeSampler(inputData: InputData,
                    advancedSolverParametersOverlay: SolverParametersOverlay,
                    baseSettingsForBatchTestsOpt: Option[Array[(String, AnyRef)]],
                    satMode: Boolean):
  (SamplingResult, AspifOrDIMACSPlainParserResult) = {

    if (!diffSATGlobalLock.tryLock())
      stomp(-10000, "invokeSampler() cannot run concurrently")

    overrideAdvancedSolverArgs(advancedSolverParametersOverlay.advancedSolverArgs,
      baseSettingsOpt = baseSettingsForBatchTestsOpt) // settings are for performance reasons global static, so we
    // need to "activate" them (overriding any default values / base settings in sharedDefs)

    if (noOfMinibenchmarkTrials > 1)
      Thread.sleep(1000)

    if (maxAssumedConsoleWidth > 0 && osWin && changeConsoleWidthUnderWin) {  // TODO: necessary with older Windows version

      //println("Changing console width to " + maxAssumedConsoleWidth)
      new ProcessBuilder("cmd", "/c", "start /b powershell -command \"&{$H=get-host;$W=$H.ui.rawui;$B=$W.buffersize;If($B.width -lt " + maxAssumedConsoleWidth + ") { $B.width=" + maxAssumedConsoleWidth + "};$W.buffersize=$B;}\"").inheritIO().start().waitFor()

      //new ProcessBuilder("cmd", "/c", "start /b powershell -command \"$host.UI.RawUI.BufferSize = New-Object System.Management.Automation.Host.size(210,2000)\"").inheritIO().start().waitFor()

    }

    val timerInitNs = System.nanoTime()

    if (showIntermediateTimers)
      println("inittimer after Parse: " + timerToElapsedMs(timerInitNs) + " ms")

    val prep: Preparation = new solving.Preparation(inputData.aspifOrDIMACSPlainParserResult, inputData.costsOpt, satModeR = satMode,
      omitAtomNogoods = false)

    if (showIntermediateTimers)
      println("inittimer after Preparation: " + timerToElapsedMs(timerInitNs) + " ms")

    var sampledModels = null.asInstanceOf[SamplingResult] //null.asInstanceOf[(mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)], Long /*time for sampling in nanosec*/ )]

    val warmupTrialNo = if (noOfMinibenchmarkTrials == 1) 0 else 3

    val trialDurations = (1 to warmupTrialNo + noOfMinibenchmarkTrials).map(benchTrial => {

      if (verbose || noOfMinibenchmarkTrials > 1)
        println("\nSolving... " + (if (noOfMinibenchmarkTrials > 1) "(mini-benchmark trial " + benchTrial + ")" else ""))

      //System.gc()

      val startTrialTimeNs = System.nanoTime()

      val ctms = System.currentTimeMillis()

      val maxSamplingTimeMs = ctms + timeoutMs // this must of course be measured against currentTimeMillis calls, not scaled nanoTime

      val solver = new SolverMulti(prep)

      val sampleMultiConf = solver.SampleMultiModelsConf(
        requestedNoOfModelsBelowThresholdOrAuto = advancedSolverParametersOverlay.noOfModels,
        prep = prep,
        requestedNumberOfModels = advancedSolverParametersOverlay.noOfModels,
        noOfSecondaryModels = advancedSolverParametersOverlay.noOfSecondaryModels,
        costThreshold = advancedSolverParametersOverlay.thresholdOpt.getOrElse(defaultThreshold),
        maxIt = maxSamplingIterationsR.max(advancedSolverParametersOverlay.noOfModels * 1000),
        maxSamplingTimeMs = maxSamplingTimeMs,
        offHeapGarbageCollectionMode = advancedSolverParametersOverlay.offHeapGarbageCollectionModeR)

      sampledModels = solver.sampleMulti(sampleMultiConf)

      if (benchTrial <= warmupTrialNo) 0l else System.nanoTime() - startTrialTimeNs // somewhat above than sampledModels._3

    })

    if (showIntermediateTimers)
      println("inittimer after solving & sampling: " + timerToElapsedMs(timerInitNs) + " ms")

    val avgDuration = ((trialDurations.sum.toDouble / noOfMinibenchmarkTrials.toDouble) / 1000000).toInt

    if (writeRuntimeStatsToFile)
      stats.writeEntry(key = "noOfMinibenchmarkTrials", value = noOfMinibenchmarkTrials, solverThreadNo = 0)

    if (noOfMinibenchmarkTrials > 1) {

      println("\n@@@@@@ Average duration solver.sampleMulti (from " + noOfMinibenchmarkTrials + " reruns): " + avgDuration + " ms\n")

      if (writeRuntimeStatsToFile)
        stats.writeEntry(key = "avgBenchmarkTrialTimeMs", value = avgDuration, solverThreadNo = 0)

    }

    diffSATGlobalLock.unlock()

    (sampledModels, inputData.aspifOrDIMACSPlainParserResult)

  }

  type ArgsList = List[(Symbol, List[String])]

  def parseArgs(args: Array[String]): (ArgsList, mutable.HashMap[(String /*param name*/ , Int /*<-thread*/ ), String /*param value*/ ]) = {

    val advancedSolverArgs /*from --solverarg arguments*/ =
      mutable.HashMap[(String /*param name*/ , Nogi /*<-thread*/ ), String /*param value*/ ]()

    var portfolioThreadToAssociateWith = 0 // 0 = no/any thread

    val arglist = args.toList

    def nextArg(argsList: ArgsList, list: List[String]): ArgsList = {

      @inline def isSwitch(s: String) = (s(0) == '-')

      list match {

        case Nil => argsList

        case ("--version" | "-v" | "--about") :: tail => {

          println(copyrightAndVersionText)

          println(thirdPartyLibs)

          sys.exit(0)

        }

        case ("--help" | "-h") :: tail => {

          println(copyright + "\n\n" + helpText)

          sys.exit(0)

        }

        case ("--verbose") :: tail => {

          verbose = true

          nextArg(argsList, tail)

        }

        case ("--omitSysExit0") :: tail => {

          omitSysExit0 = true

          nextArg(argsList, tail)

        }

        case "-ci" :: tail => {

          nextArg(argsList ++ List('enforceReadingFromSTDIN -> List("")), tail)

        }

        case ("-n") :: arg :: tail => {

          if (!(arg.stripPrefix("-").forall(_.isDigit))) {

            stomp(-1, "Number expected after -n")

            argsList

          } else {

            val argT = if (arg == "0") Int.MaxValue.toString else arg // NB: this is different from -n 0 like in Clingo, because diff-SAT doesn't do enumeration but sampling

            nextArg(argsList ++ Map('n -> List(argT)), tail)

          }

        }

        case ("-s") :: arg :: tail => {

          if (!arg.forall(_.isDigit)) {

            stomp(-1, "Positive number or -1 expected after -s")

            argsList

          } else {

            if (arg != "-1")
              nextArg(argsList ++ Map('s -> List(arg)), tail)
            else
              nextArg(argsList, tail)

          }

        }

        case ("-gc") :: arg :: tail => {

          if (!arg.forall(_.isDigit)) {

            stomp(-1, "Positive number or -1 expected after -gc")

            argsList

          } else {

            if (arg != "-1")
              nextArg(argsList ++ Map('gc -> List(arg)), tail)
            else
              nextArg(argsList, tail)

          }

        }

        case ("-t") :: arg :: tail => {

          val threshOpt: Option[Double] = parseDouble(arg)

          if (threshOpt.isEmpty || threshOpt.get < 0d) {

            stomp(-1, "Positive number or zero expected after -t")

            argsList

          } else {

            nextArg(argsList ++ Map('t -> threshOpt.map(_.toString).toList), tail)

          }

        }

        case ("--conf") :: sampleConfJsonStr :: tail => { // ignored for now

          nextArg(argsList, tail)

        }

        case "--thread" :: arg1 :: tail => {

          portfolioThreadToAssociateWith = arg1.toInt

          nextArg(argsList, tail)

        }

        case "--solverarg" :: arg1 :: arg2 :: tail => {

          advancedSolverArgs.update((arg1, portfolioThreadToAssociateWith), arg2)

          nextArg(argsList, tail)

        }

        case "-mse" :: tail => {

          nextArg(argsList ++ List('mse -> List()), tail)

        }

        case "--showaux" :: tail => {

          nextArg(argsList ++ List('showaux -> List()), tail)

        }

        case "--writestatsto" :: arg1 :: tail => {

          writeStatsDirectory = arg1

          enforceWriteRuntimeStatsToFileOpt = Some(true)

          nextArg(argsList, tail)

        }

        case "--batchtests" :: arg1 :: tail => {

          runBatchTests = true

          batchTestDir = arg1

          nextArg(argsList, tail)

        }

        case "--timeoutbench" :: arg1 :: arg2 :: tail => {  // TODO: doesn't work well (piles up too much waste in memory). Use external script for benchmarking.

          runTimeoutBenchmarks = true

          timeoutBenchmarkTimeoutSec = arg1.toInt

          timeoutBenchmarkDir = arg2

          nextArg(argsList, tail)

        }

        case "--apitests" :: tail => {

          runAPITests = true

          nextArg(argsList, tail)

        }

        case fileName :: tail if !isSwitch(fileName) => {

          if (runBatchTests || runTimeoutBenchmarks)
            stomp(-5009, "If runBatchTests=true or runTimeoutBenchmarks=true, no input file names can be specified on the command line")

          nextArg(argsList ++ List('inputFile -> List(fileName)), tail)

        }

        case option :: tail if option.startsWith("-") => stomp(-1, option); nextArg(argsList, tail)

      }

    }

    val parsedCommandlineArgs: ArgsList = nextArg(Nil, arglist)

    (parsedCommandlineArgs, advancedSolverArgs)

  }

  /**
    * Commandline processing
    *
    * @param args
    */
  def main(args: Array[String]): Unit = {

    if (args.contains("--apitests"))
      runAPITests = true

    if (runAPITests)
      runAllAPITests

    // =============================================================================================

    if (delayStartUntilCPULoadTo >= 0d) {

      println("Delayed start until system load falls to " + delayStartUntilCPULoadTo + "...")

      Thread.sleep(1000) // with some OS required to get meaningful load values

      import java.lang.management.ManagementFactory

      val systemMXBean = ManagementFactory.getOperatingSystemMXBean.asInstanceOf[OperatingSystemMXBean]

      while (systemMXBean.getSystemCpuLoad() > delayStartUntilCPULoadTo) {

        println("System load: " + systemMXBean.getSystemCpuLoad() + ", waiting...")

        Thread.sleep(1000)

      }

      Thread.sleep(1000)

    }

    val timerOverallNs = System.nanoTime()

    println("diff-SAT " + diffSAT.version)

    FloatArrayUnsafeS.init(unsafe)

    DoubleArrayUnsafeS.init(unsafe)

    ByteArrayUnsafeS.init(unsafe)

    /*try {  // not available in all Java  SDKs

      import java.lang.management.ManagementFactory

      import com.sun.management.HotSpotDiagnosticMXBean

      val hsDiag = ManagementFactory.getPlatformMXBean(classOf[HotSpotDiagnosticMXBean])

      //hsDiag.setVMOption("MaxInlineSize", "4096")

      //hsDiag.setVMOption("FreqInlineSize", "4096")

      //hsDiag.setVMOption("InlineSmallCode", "4096")

      //hsDiag.setVMOption("AllocatePrefetchStyle", "1")

    } catch {

      case t: Throwable => stomp(-5, t.toString)

    }*/

    if (debug) {

      val p = System.getProperties

      p.list(System.out)

      System.out.println("\navailableProcessors: " + Runtime.getRuntime.availableProcessors)

      System.out.println("maxMemory: " + Runtime.getRuntime.maxMemory / 1073741824l + " GB")

      System.out.println("totalMemory: " + Runtime.getRuntime.totalMemory / 1073741824l + " GB")

      // not available anymore in some recent JDKs: System.out.println("sun.misc.VM.maxDirectMemory (off-heap memory): " + sun.misc.VM.maxDirectMemory() / 1073741824l + " GB")

      System.out.println

    }

    if(runBatchTests && runTimeoutBenchmarks && (noOfMinibenchmarkTrials > 1) || runBatchTests && runTimeoutBenchmarks || runBatchTests && (noOfMinibenchmarkTrials > 1) || runTimeoutBenchmarks && (noOfMinibenchmarkTrials > 1))
      stomp(-5009, "Only one of the following can be performed: batch testing, timeout benchmarks, mini benchmarks")

    val (parsedCommandlineArgs: ArgsList, advancedSolverArgsFromCommandline /*from --solverarg*/ : mutable.HashMap[(String, Nogi), String]) =
      parseArgs(args = args)

    if (debug) println("Command line arguments in diff-SAT: " + parsedCommandlineArgs)

    sharedDefs.commandLineTakeNote = parsedCommandlineArgs.mkString(" ")

    val parsedCommandlineArgsMap: mutable.HashMap[Symbol, List[String]] =
      mutable.HashMap[Symbol, List[String]]().++(parsedCommandlineArgs.toMap)

    if (showIntermediateTimers)
      if (debug) println("\notime args: " + timerToElapsedMs(timerOverallNs) + " ms")

    def recursiveAllFiles(f: File): Array[File] = {

      val filesHere = f.listFiles

      filesHere ++ filesHere.filter(_.isDirectory).flatMap(recursiveAllFiles)

    }

    val inputFileList: ArrayBuffer[(File, Nogi)] = if (runBatchTests) {

      val fl = recursiveAllFiles(new File(batchTestDir)).filter(file =>
        !file.isDirectory && batchTestFileEndings.contains(file.getName.substring(file.getName.lastIndexOf('.'))))

      println("\n**** Running batch tests (" + fl.size + " files from directory " + new File(batchTestDir).getAbsolutePath + ")...\n")

      fl.zipWithIndex.to(ArrayBuffer)

    } else if(runTimeoutBenchmarks) {

      val fl = recursiveAllFiles(new File(timeoutBenchmarkDir)).filter(file =>
        !file.isDirectory && timeoutBenchmarkFileEndings.contains(file.getName.substring(file.getName.lastIndexOf('.'))))

      println("\n**** Running timeout benchmark (" + fl.size + " files from directory " + new File(timeoutBenchmarkDir).getAbsolutePath + ")...\nTimeout per file: " + timeoutBenchmarkTimeoutSec + " seconds\n")

      fl.zipWithIndex.to(ArrayBuffer)

    } else {

      if (parsedCommandlineArgs.exists(_._1 == 'enforceReadingFromSTDIN) || !parsedCommandlineArgs.exists(_._1 == 'inputFile))
        ArrayBuffer[(File, Nogi)]()
      else
        ArrayBuffer((new File(parsedCommandlineArgsMap.get('inputFile).get.headOption.getOrElse("")), 0))

    }

    val originalInputFileListSize = inputFileList.size

    val baseSettingsForBatchProcessingOpt: Option[Array[(String, AnyRef)]] = if (runBatchTests || runTimeoutBenchmarks)
      Some(getSharedFieldsUsingReflection(omitRefType = false, omitScalaGen = true))
    else
      None

    do { // batch processing loop

      fileNameOpt = if (originalInputFileListSize == 0) None else Some(inputFileList.head._1.getAbsolutePath) //parsedArgsMap.get('inputFile).get.headOption

      if (writeRuntimeStatsToFile) {

        stats = new Stats(problemFile = fileNameOpt.getOrElse("<unknown problem file>"))

        stats.initializeStatsFile()

        stats.writeEntry(key = "runCompleted", value = "false", solverThreadNo = 0) // will be replaced with true if completed

        stats.writeEntry(key = "debugLevel", value = if (debug2) 2 else if (debug) 1 else 0, solverThreadNo = 0)

        stats.writeEntry(key = "solver", value = "diff-SAT " + version, solverThreadNo = 0)

      }

      val (inputData: InputData, satMode,
      inlineArgsOpt: Option[(mutable.HashMap[Symbol, List[String]], mutable.HashMap[(String, Nogi), String])],
      (commentInFileSaysUNSAT: Boolean, commentInFileSaysSAT: Boolean),
      (inlineProbabilityChecksOpt: Option[(Double, Iterator[(String, Double)])]),
      inlineAllModelsCheckTokensOpt: Option[Array[Array[Pred]]],
      inlineAllModelsMultilineCheckTokensOpt: Option[Array[Array[Pred]]]) = if (fileNameOpt.isEmpty)
        obtainInputFromText(Left(None), mseInCommandLineOpt = if (parsedCommandlineArgsMap.contains('mse)) Some(true) else None) // we read from STDIN
      else {

        if (runBatchTests || runTimeoutBenchmarks)
          println("\n****************************************\n" +
            "**** Next file in batch: " + fileNameOpt.get + " (remaining: " + (originalInputFileListSize - inputFileList.head._2) + ")\n")

        inputFileList.remove(0)

        obtainInputFromText(Left(fileNameOpt), mseInCommandLineOpt = if (parsedCommandlineArgsMap.contains('mse)) Some(true) else None)

      }

      if (showIntermediateTimers)
        println("\notimer inputData: " + timerToElapsedMs(timerOverallNs) + " ms")

      // If there are any arguments specified inline in the input file itself, we use these for solving but with arguments of the same name
      // specified on the command line overriding the inline arguments:

      val parsedArgsMap = (inlineArgsOpt.map(_._1).getOrElse(mutable.HashMap[Symbol, List[String]]())).++(parsedCommandlineArgsMap)

      val advancedSolverArgs /*from inline --solverarg*/ : mutable.HashMap[(String, Int), String] =
        (inlineArgsOpt.map(_._2).getOrElse(mutable.HashMap[(String, Int), String]())).++(advancedSolverArgsFromCommandline)

      //val timeoutMs = (if(runTimeoutBenchmarks) timeoutBenchmarkTimeoutSec * 1000 else advancedSolverArgs.get("timeoutMs", )).toLong

      val advancedSolverArgsNewTimeout = if (runTimeoutBenchmarks) advancedSolverArgs.+(("timeoutMs", 0) -> (timeoutBenchmarkTimeoutSec * 1000).toString) else advancedSolverArgs

      val solverParametersOverlay = input.SolverParametersOverlay(
        noOfModels = parsedArgsMap.getOrElse('n, List(defaultCmdlNoOfModelsStr)).head.toInt,
        noOfSecondaryModels = parsedArgsMap.getOrElse('s, List(defaultCmdlNoOfModelsStr)).head.toInt,
        offHeapGarbageCollectionModeR = if (noOfMinibenchmarkTrials > 1 || runBatchTests || runTimeoutBenchmarks) 1 else
          parsedArgsMap.getOrElse('gc, List(defaultCmdlOffHeapGarbageCollectionModeR)).head.toInt,
        thresholdOpt = parsedArgsMap.get('t).map(_.head.toDouble),
        showauxInSATmode = parsedArgsMap.contains('showaux),
        assureMSE = parsedArgsMap.contains('mse),
        advancedSolverArgs = advancedSolverArgsNewTimeout
      )

      val (samplingResult: SamplingResult,
      parserResult: AspifOrDIMACSPlainParserResult) =
        invokeSampler(inputData = inputData,
          advancedSolverParametersOverlay = solverParametersOverlay,
          baseSettingsForBatchTestsOpt = baseSettingsForBatchProcessingOpt,
          satMode = satMode)

      if (!samplingResult.modelsSymbolic.isEmpty) {

        val (sampledModelsWithSymbolsCleaned, _, _, _, _) = queryAndPrintSolverResult(showauxInASPmode = solverParametersOverlay.showauxInSATmode,
          satMode = satMode,
          samplingResult,
          parserResultForSanityChecksOpt = Some(parserResult),
          adHocDisjunctiveQueries = adHocDisjunctiveQueries,
          adHocConjunctiveQueries = adHocConjunctiveQueries,
          adHocSimpleGroundRuleQueries = adHocSimpleGroundRuleQueries,
          adHocConjunctionOfSimpleGroundRulesQuery = adHocCollectionOfSimpleGroundRuleQuery)

        // We optionally do a simple frequency check (typically used in batch testing mode) to check if the
        // probabilities of given atoms in the sample are approximately correct (approach like for ad hoc queries):

        inlineProbabilityChecksOpt.foreach((toleranceAtomsProbs: (Double, Iterator[(String, Double)])) => {

          val tolerance: Double = toleranceAtomsProbs._1

          val atomsProbs: Iterator[(String, Double)] = toleranceAtomsProbs._2

          atomsProbs.foreach(atomProb => {

            val frequencyAtomInModels = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

              // (Remark: Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
              // are simply absent positive atoms in the orignal model.)

              model.contains(atomProb._1)

            }).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

            println("Atom " + atomProb._1 + ": actual frequency = " + frequencyAtomInModels + " vs. expected frequency = " + atomProb._2)

            if (frequencyAtomInModels < atomProb._2 - tolerance || frequencyAtomInModels > atomProb._2 + tolerance)
              stomp(-20000, "Frequency " + frequencyAtomInModels + " of atom " + atomProb._1 + " in sampled model deviates from expected probability " + atomProb._2 + "\nProblem file: " + fileNameOpt.get)

          })

        })

        val exhaustiveKnownModels: Seq[Array[Pred]] = inlineAllModelsCheckTokensOpt.toList.flatten ++ inlineAllModelsMultilineCheckTokensOpt.toList.flatten

        if (!exhaustiveKnownModels.isEmpty) {

          // We cannot check whether the sample covers all existing models (simply because we sample and don't exhaustively enumerate), but
          // we can check if each sampled model is actually a model according to inline #all_models (which needs to be exhaustive, of course):

          sampledModelsWithSymbolsCleaned.foreach((sampledModel: Array[Pred]) => {

            val r = exhaustiveKnownModels.exists(inlineModel => {

              sampledModel.forall(symInSampledModel => inlineModel.contains(symInSampledModel)) &&
                sampledModel.length == inlineModel.length

            })

            if (!r)
              stomp(-20000, "The following sampled model is not part of the #all_models or #all_models_begin... set in problem file: " + sampledModel.mkString(" "))
            else
              println("\nIn batch test: Check of sampled model against inline #all_models or #all_models_begin... succeeded (checked model against complete set of " + exhaustiveKnownModels.length + " different models).")

          })

        }

      } else if (inlineProbabilityChecksOpt.isDefined || inlineAllModelsCheckTokensOpt.isDefined)
        stomp(-20000, "Inline probability or #all_models checks present but result of solver is UNSAT.\nProblem file: " + fileNameOpt.get)

      val samplingTimeMs = samplingResult.samplingDurationNs /*<- this is not the sampling start time but the actual elapsed sampling time */ / 1000000 //timerToElapsedMs(sampledModels._3) // doesn't include parsing, preparation, JVM startup etc time

      if (noOfMinibenchmarkTrials <= 1)
        println("\nTime for multi-model sampling (" + samplingResult.modelsSymbolic.length + " model(s)): " + samplingTimeMs + " ms (" + (samplingTimeMs / 1000f) + " sec, " + Math.rint(samplingTimeMs / 1000f / 60f * 1000f) / 1000f + " min)")

      if (writeRuntimeStatsToFile)
        stats.writeEntry(key = "samplingTimeMs", value = samplingTimeMs, solverThreadNo = 0)

      if (!runBatchTests && !runTimeoutBenchmarks) {

        val overallTimeMs = timerToElapsedMs(timerOverallNs) // doesn't include JVM startup time (before actual diff-SAT code runs)

        println("\nOverall time (incl parsing/pre-/post-processing/printing): " + overallTimeMs + " ms (" + (overallTimeMs / 1000f) + " sec, " + Math.rint(overallTimeMs / 1000f / 60f * 1000f) / 1000f + " min)")

        if (writeRuntimeStatsToFile)
          stats.writeEntry(key = "overallTimeMs", value = overallTimeMs, solverThreadNo = 0)

      }

      if (writeRuntimeStatsToFile) {

        stats.writeEntry(key = "runCompleted", value = "true", solverThreadNo = 0, replace = true)

        println("\nWriting stats to " + stats.outFile.getAbsolutePath() + "...")

        stats.writeToFile()

      }

      if (commentInFileSaysUNSAT && !samplingResult.modelsSymbolic.isEmpty ||
        commentInFileSaysSAT && samplingResult.modelsSymbolic.isEmpty)
        stomp(-20000, "Batch tests aborted because unexpected SAT result on file declared to be SAT or UNSAT in comment.\nProblem file: " + fileNameOpt.get)

    } while (!inputFileList.isEmpty)

    if (runBatchTests /*|| runTimeoutBenchmarks*/) {

      println("\n****************************************\n**** Batch processing complete (" + originalInputFileListSize + " files).\n")

      val overallTimeMs = timerToElapsedMs(timerOverallNs) // doesn't include JVM startup time (before actual diff-SAT code runs)

      println("**** Time for batch processing (incl parsing/pre-/post-processing/printing): " + overallTimeMs + " ms (" + (overallTimeMs / 1000f) + " sec, " + Math.rint(overallTimeMs / 1000f / 60f * 1000f) / 1000f + " min)")

      if (writeRuntimeStatsToFile) {

        stats = new Stats(problemFile = "Batch_(" + originalInputFileListSize + " files)")

        stats.initializeStatsFile()

        stats.writeEntry(key = "overallTimeBatchProcessingMs", value = overallTimeMs, solverThreadNo = 0)

        println("\nWriting batch processing overall stats to " + stats.outFile.getAbsolutePath() + "...")

        stats.writeToFile()

      }

    }

    if (!omitSysExit0) // we need exit if jar isn't loaded dynamically into the current JVM. Otherwise, we need return
      sys.exit(0)
    else
      return

  }

  /**
    * Prints the sampled models and resolves so-called ad hoc queries.
    *
    * See [[input.ProbabilisticAnswerSetProgram]] for an example.
    *
    * For each of ad hoc query, the frequency of how often the respective query formula holds in the sample (multiset
    * of models) is determined. The following types of ad hoc queries are supported:
    *
    * adHocConjunctiveQueries specifies multiple queries, each consisting of a conjunction of literals
    *
    * adHocDisjunctiveQueries as adHocConjunctiveQueries but with disjunctions
    *
    * adHocSimpleGroundRuleQueries as adHocConjunctiveQueries but with simple rules consisting of a single head literal
    * and a set of body literals (all ground). Observe that the rule format is much simpler than GroundSymbolicASPRule;
    * to use more complex types of rules as queries (e.g., choice rules), a tool like staspquery is required.
    *
    * adHocCollectionOfGroundRuleQuery specifies a single(!) query consisting of a conjunction of ground rules, that is,
    * rule1 ^ rule2 ^ ...
    *
    * @param showauxInASPmode
    * @param satMode
    * @param samplingResult
    * @param parserResultForSanityChecksOpt
    * @param adHocConjunctiveQueries
    * @param adHocDisjunctiveQueries
    * @param adHocSimpleGroundRuleQueries
    * @param adHocConjunctionOfSimpleGroundRulesQuery
    * @param printAnswers
    * @param printAdHocQueryResults
    */
  def queryAndPrintSolverResult(showauxInASPmode: Boolean,
                                satMode: Boolean,
                                samplingResult: SamplingResult,
                                parserResultForSanityChecksOpt: Option[AspifOrDIMACSPlainParserResult] = None,
                                adHocConjunctiveQueries: Seq[Seq[Pred]] = Seq(),
                                adHocDisjunctiveQueries: Seq[Seq[Pred]] = Seq(),
                                adHocSimpleGroundRuleQueries: Seq[(Pred /*<--head*/ , Seq[Pred] /*<--body*/ )] = Seq(),
                                adHocConjunctionOfSimpleGroundRulesQuery: Seq[(Pred /*<--head*/ , Seq[Pred] /*<--body*/ )] = Seq(),
                                printAnswers: Boolean = printAnswers,
                                printAdHocQueryResults: Boolean = true): (
    mutable.Seq[Array[Pred]] /*<-- models (cleaned) */ ,
      Seq[(String, Double)] /*<-- adHocConjunctiveQueries results*/ ,
      Seq[(String, Double)] /*<-- adHocDisjunctiveQueries results*/ ,
      Seq[(String, Double)] /*<-- adHocSimpleGroundRuleQueries results*/ ,
      Seq[(String, Double)] /*<-- adHocCollectionOfSimpleGroundRuleQuery result (singleton sequence or empty)*/ ) = samplingResult match {

    case SamplingResult(modelsSymbolic, modelsUsingElis, samplingDurationNs) => {

      val hideAuxPreds: Int = if (showauxInASPmode) 4 else 5

      val sampledModelsWithSymbolsCleaned: mutable.Seq[Array[Pred]] = if (hideAuxPreds == 4)
        modelsSymbolic.map(_.filterNot(l => isLatentSymbolAuxAtom(l.stripPrefix("-"))))
      else if (hideAuxPreds == 1) modelsSymbolic.map(_.filterNot(a => isAuxAtom(a.stripPrefix("-")) && !isSpanAuxAtom(a.stripPrefix("-"))))
      else if (hideAuxPreds == 2) modelsSymbolic.map(_.filterNot(l => isAuxAtom(l.stripPrefix("-"))))
      else if (hideAuxPreds == 3) modelsSymbolic.map(_.filterNot(l => isSpanAuxAtom(l.stripPrefix("-"))))
      else if (hideAuxPreds == 5) modelsSymbolic.map(_.filterNot(a => isSpanAuxAtom(a.stripPrefix("-")) || isLatentSymbolAuxAtom(a.stripPrefix("-"))))
      else
        modelsSymbolic

      if (performSanityChecks && satMode) { // see further sanity checks in SolverMulti.scala

        if (parserResultForSanityChecksOpt.isEmpty)
          stomp(-5014, "Sanity checks in printSolverResult requested but parseResult is missing")

        parserResultForSanityChecksOpt.foreach(parserResult => {

          sampledModelsWithSymbolsCleaned.foreach(fullModelWithSymbols => {

            println("Sanity check 2 (outside solver thread, SAT mode only): Checking cleaned model against original DIMACS-CNF clauses...")

            var checkedDIMACSclauses = 0

            val violatedDIMACSClauses: Boolean = if (!parserResult.clausesForChecksOpt.isDefined) {

              println("WARNING: enforceSanityChecks=true but cannot check for violatedDIMACSClauses!");

              false

            } else {

              val modelCandWithSymbolsSet = fullModelWithSymbols.toSet

              parserResult.clausesForChecksOpt.get.exists(clause => { // TODO: optimize:

                val clauseSatisfied = clause.exists((dimacsVarPN: Nogi) => {

                  modelCandWithSymbolsSet.contains(dimacsVarPN.toString)

                })

                if (!clauseSatisfied)
                  println("\\\\\\\\  Violated original CNF clauses: " + clause.mkString(" "))

                checkedDIMACSclauses += 1

                if (checkedDIMACSclauses % 500000 == 0)
                  println("  original clauses checked so far: " + checkedDIMACSclauses + " / " + parserResult.clausesForChecksOpt.get.length)

                !clauseSatisfied

              })

            }
            println("Any violated original DIMACS clauses: " + violatedDIMACSClauses + " (checked: " + checkedDIMACSclauses + ")\n")

            assert(checkedDIMACSclauses == parserResult.clausesForChecksOpt.get.length &&
              checkedDIMACSclauses == parserResult.rulesOrClauseNogoods.right.get.length /*parserResult.directClauseNogoodsOpt.get.length*/)

            if (violatedDIMACSClauses) {

              println("\n\\/\\/\\/\\/ Internal error: Sanity check on original DIMACS clauses failed on model candidate!\n")

              sys.exit(-5)

            }

          })

        })

      }

      val resultsAdHocQueriesConjunctive: Seq[(String, Double)] = adHocConjunctiveQueries.map((conjAtoms: Seq[String]) => {

        val freqInModels = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

          conjAtoms.forall(lit => {

            // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
            // are simply absent positive atoms in the orignal model.

            if (lit.startsWith("not ")) !model.contains(lit.stripPrefix("not ")) else model.contains(lit)

          })

        }).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

        if (printAdHocQueryResults) println("Pr(" + conjAtoms.mkString(" ^ ") + ") = " + freqInModels)

        (conjAtoms.mkString(" ^ "), freqInModels)

      })

      val resultsAdHocQueriesDisjunctive: Seq[(String, Double)] = adHocDisjunctiveQueries.map((disjAtoms: Seq[String]) => {

        val freqInModels = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

          disjAtoms.exists(lit => {

            // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
            // are simply absent positive atoms in the orignal model.

            //model.contains(atom)
            if (lit.startsWith("not ")) !model.contains(lit.stripPrefix("not ")) else model.contains(lit)

          })
        }).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

        if (printAdHocQueryResults) println("Pr(" + disjAtoms.mkString(" v ") + ") = " + freqInModels)

        (disjAtoms.mkString(" v "), freqInModels)

      })

      val resultsAdHocQueriesRule: Seq[(String, Double)] = adHocSimpleGroundRuleQueries.map((ruleHeadBody: (Pred, Seq[Pred])) => {

        val freqInModels: Double = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

          val bodyHolds = ruleHeadBody._2.forall(lit => {

            // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
            // are simply absent positive atoms in the orignal model.

            if (lit.startsWith("not ")) !model.contains(lit.stripPrefix("not ")) else model.contains(lit)

          })

          lazy val headHolds = if (ruleHeadBody._1.startsWith("not ")) !model.contains(ruleHeadBody._1.stripPrefix("not ")) else model.contains(ruleHeadBody._1)

          !bodyHolds || headHolds

        }).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

        val queryHandleStr = ruleHeadBody._1 + ":-" + ruleHeadBody._2.mkString(",")

        if (printAdHocQueryResults) println("Pr(" + queryHandleStr + ") = " + freqInModels)

        (queryHandleStr, freqInModels)

      })

      val resultAdHocCollectionOfSimpleGroundRuleQuery: Seq[(String, Double)] = if (adHocConjunctionOfSimpleGroundRulesQuery.isEmpty) Seq() else Seq {

        val freqInModels: Double = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

          adHocConjunctionOfSimpleGroundRulesQuery.forall((ruleHeadBody: (Pred, Seq[Pred])) => {

            val bodyHolds = ruleHeadBody._2.forall(lit => {

              // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
              // are simply absent positive atoms in the orignal model.

              if (lit.startsWith("not ")) !model.contains(lit.stripPrefix("not ")) else model.contains(lit)

            })

            lazy val headHolds = if (ruleHeadBody._1.startsWith("not ")) !model.contains(ruleHeadBody._1.stripPrefix("not ")) else model.contains(ruleHeadBody._1)

            !bodyHolds || headHolds

          })

        }).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

        val queryHandleStr = adHocConjunctionOfSimpleGroundRulesQuery.map((ruleHeadBody: (Pred, Seq[Pred])) => {

          ruleHeadBody._1 + ":-" + ruleHeadBody._2.mkString(",")

        }).mkString("\n")

        if (printAdHocQueryResults) println("Pr(" + queryHandleStr + ") = " + freqInModels)

        (queryHandleStr, freqInModels)

      }

      if (printAnswers) {

        sampledModelsWithSymbolsCleaned.zipWithIndex.foreach { case (model, index) =>
          System.out.println("Answer: " + (index + 1) + "\n" + model.mkString(" ")) // recall that in contrast to plain ASP solvers, the same
          // sampled answer can be printed multiple times here.
        }

      }

      if (!modelsSymbolic.isEmpty)
        System.out.println("SATISFIABLE ") // this must be printed _directly_ after the list of answers (no empty line allowed in between)
      // ^^^^NB (TODO): "UNSAT" is already printed in the solver thread, since at this later point, there is no information anymore
      // of why the set of models is empty (abort or unsat?)

      (sampledModelsWithSymbolsCleaned, resultsAdHocQueriesConjunctive, resultsAdHocQueriesDisjunctive,
        resultsAdHocQueriesRule, resultAdHocCollectionOfSimpleGroundRuleQuery)

    }

  }

}
