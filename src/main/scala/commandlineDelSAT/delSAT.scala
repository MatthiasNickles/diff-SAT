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

package commandlineDelSAT

import java.io.{BufferedInputStream, PrintWriter}
import java.util

import aspIOutils._
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, Variable}
import com.accelad.math.nilgiri.{DoubleReal, autodiff}
import diff.UncertainAtomsSeprt
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.scijava.parse.ExpressionParser
import parsing.{AspifPlainParser, DIMACPlainSparser}
import sharedDefs._
import solving.{Preparation, SolverMulti}
import utils.{ByteArrayUnsafeS, FloatArrayUnsafeS}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/*
  * See sharedDefs.scala for solver settings available
  * (most of these can also be specified on the command line using --solverarg, see --help below)
  *
  * @author Matthias Nickles
  *
  */
object delSAT {

  val debug = false

  /* For JVM flight control, use e.g. -XX:+FlightRecorder -XX:StartFlightRecording=duration=60s,filename=delsatRecording.jfr

   For scalac compiler options see https://docs.scala-lang.org/overviews/compiler-options/index.html
   Full "optimization" using scalac 2.12.x: -opt-inline-from -opt-inline-from:** but this doesn't seem to improve performance for delSAT.
   Try compiling from Scala without any "optimization" arguments first - this was actually the fastest approach in our tests.

   Use Scala compiler option -Xdisable-assertions (unless for debgging purposes).

   */

  var verbose = false || debug

  val noOfMinibenchmarkTrials = 1 // (this is just for a quick local mini-benchmark to get a very rough idea of performance)

  val enforceSanityChecks = false && noOfMinibenchmarkTrials == 1 // NB: for ASP, any invalid models are first bounced back to
  // the solver before this check could occur (see SolverMulti.scala).
  // NB: enforceSanityChecks currently doesn't check UNSAT results yet.

  // !! Set enforceSanityChecks to false before running via prasp2 or any benchmarks !!
  // Also: disable assertions and recompile for any benchmarks: -Xdisable-assertions

  def printAnswers = !suppressAnswers && noOfMinibenchmarkTrials == 1 && !enforceSanityChecks // false only for debugging purposes

  assert(!(printAnswers && enforceSanityChecks))

  val version = "0.4.1"

  val copyrightAndVersionText = "delSAT " + version + "\nCopyright (c) 2018, 2019 Matthias Nickles\nLicense: https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE"

  val defaultNoOfModelsStr = "-1"

  val thirdPartyLibs = "delSAT " + version + """ uses or incorporates the following third-party software:

JAutoDiff
  Copyright (c) 2012 uniker9 (https://github.com/uniker9/JAutoDiff)
  License: https://github.com/uniker9/JAutoDiff/blob/master/LICENSE.txt
  Copyright (c) 2017 AccelaD (https://github.com/accelad-com/nilgiri-math/tree/master/src/main/java/com/accelad/math/nilgiri)
  License: https://github.com/accelad-com/nilgiri-math/blob/master/src/main/java/com/accelad/math/nilgiri/LICENSE

Parsington (https://github.com/scijava/parsington)
  Copyright (c) 2015 - 2016, Board of Regents of the University of Wisconsin-Madison
  License: https://github.com/scijava/parsington/blob/master/LICENSE.txt

fastutil (http://fastutil.di.unimi.it)
  Copyright (c) 2002-2017 Sebastiano Vigna
  License: https://github.com/vigna/fastutil/blob/master/LICENSE-2.0
"""

  val helpText =
    """
     ASP and SAT solver for sampling-based multi-model optimization using a
     differentiable SAT solving approach.

     Command line parameters:

            [<filename>] [--version|-v|--about] [--help|-h]
            [-n <n>] [-s <s>] [-t <t>] [-ci] [-mse]
            [--solverarg "name" "value"]*

     Reads from a file or STDIN input programs or clauses in aspif or DIMACS-CNF format or
     extended aspif or DIMACS with list of parameter atoms and cost function(s). To
     obtain aspif from a non-ground plain Answer Set Program, preprocess using, e.g.,
      clingo myProg.lp --trans-ext=all --pre=aspif
     Input is obtained from STDIN if no file name is provided or if flag -ci is specified.

     Parameters:

     -n <n> with n>0 lets the sampler sample at least n (not necessarily different) models such
     that the sampled multiset of models solves the given cost up to the specified
     accuracy if possible (or the maximum number of trials is reached). Target accuracy
     is specified using an error threshold (see parameter -t below).

     If -n is absent or n = -1, sampling generates models until a minimum multiset of models
     has been generated st. the specified or default error threshold (or maximum number of
     trials) is reached (a multisolution).

     If n < -1, sampling firstly generates a minimum multiset of size m to reach a cost
     minimum (as with -n -1) and then samples -n-m further models uniformly from the minimum
     multiset (that is, it "fills" the minimum sample up by sampling uniformly from it).
     Primary use case of -n with n>0 is to increase of solution entropy by sampling a
     larger number of models.

     -s <s> with s>0 samples n models uniformly with replacement from the discovered
     multisolution (i.e., the multiset that would be printed with -n alone). Observe
     that delSAT possibly finds different multisolutions when called multiple times
     for the same input.
     Only these models are printed with -s. -s allows for a different sampling semantics -
     if, e.g., a Boolean variable 'a' is assigned (via the cost) probability 0.6, -n -1
     results in a multiset of models where in 60% of all models 'a' holds. In contrast,
     with -s 1 only a single model is printed. With probability 0.6, in this model 'a'
     holds and with probability 0.4 'a' does not hold.

     Models are either stable models (answer sets) or satisfying Boolean assignments (in
     case the input is in DIMACS CNF or in PCNF format).

     -t <threshold> specifies the error threshold for the total cost function (small
     threshold means higher accuracy but more time required for sampling).

     -mse promises that the costs are provided entirely as part costs with inner MSE terms
     of the form (p-f(v))^2 where p is a probability and v is a parameter atom symbol
     (random variable). -mse is optional even for MSE-type costs but allows for faster
     parsing of large lists of such functions.

     --solverarg "argname" "value" specifies additional solver arguments. See
     sharedDefs.scala for the full list. Multiple --solverarg can be specified.
     Examples:
       --solverarg "partDerivComplete" "true" (activates support for certain
       non-MSE-style costs, see documentation)
       --solverarg "maxSolverThreadsR" "6" --solverarg "freeEliSearchConfigsP" "4 3 8"
       activates parallel portfolio solving using max. 6 threads and approaches 4,3,8 (with 4
       chosen with priority when creating the solver threads)
       --solverarg "diversify" "true" (aims at generating more diverse models, but typically
       decreases speed)

     --showaux also prints in models auxiliary atoms introduced for spanning formulas (omitted
       by default)

     -ci enforces reading from STDIN

     --verbose shows additional information about the solving and sampling process

     --version|-v|--about prints information about version and third-party software
     used by delSAT (including copyrights and license information), then exits.

     --help|-h prints this information and exits
"""

  object MessageTypes extends Enumeration {

    type MessageType = Value

    val /*INFO,*/ WARNING, ERROR = Value

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

    -104 -> ("Disjunction found in ASP input. Translation of disjunctions using shift/unfold doesn't guarantee a complete set of answers set.\n Consider increasing the number of unfolds in case of non-convergence.", WARNING),

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

    -5006 -> ("Incompatible settings, see def checkSettings in sharedDefs.scala for details", ERROR),

    -5007 -> ("Experimental feature, might give wrong results", WARNING),

    -5008 -> ("Sampling ended but specified threshold not reached!", WARNING),

    -5009 -> ("Invalid settings, see sharedDefs.scala for details", ERROR),

    -5010 -> ("Literal scores out of valid range. Setting 'eliScoreUpdateFact' will be adapted in current solver thread.", WARNING),

    -5011 -> ("Cost stagnates, sampling aborted (set flag stopSamplingOnStagnation to false to change this behavior)", WARNING),

    -5012 -> ("enforceStopWhenSampleSizeReached = true (i.e., sampling stops after n models even if specified cost minimum not reached yet)", WARNING),

    -10000 -> ("Internal error", ERROR)

  )

  def stomp(code: Int, additionalInfo: String = "") = {

    val message = stompMessages(code)

    if (message._2 == ERROR) {

      System.err.println("\nError: " + message._1 + ": " + additionalInfo)

      sys.exit(code)

    } else if (message._2 == WARNING)
      System.out.println("\nWarning: " + message._1 + ": " + additionalInfo)
    else
      assert(false) //System.out.println("Info: " + message._1 + " " + additionalInfo)

  }

  @inline def log(debugMessage: => Any): Unit = {

    if (debug)
      System.out.println(debugMessage.toString)

  }

  @inline def parseDouble(s: String): Option[Double] = {

    try {

      Some(s.toDouble)

    } catch {

      case _: NumberFormatException => None

    }

  }

  final case class InputData(aspifOrDIMACSPlainParserResult: AspifOrDIMACSPlainParserResult,
                             costsOpt: Option[UncertainAtomsSeprt]) {}

  @inline def generateMeasuredAtomVariableInCost(weightedAtomStr: String, dFFactory: diff.DifferentialFunctionFactoryStasp,
                                                 aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult,
                                                 eliToVariableInCostFunctions: mutable.HashMap[Int, Variable[DoubleReal]]): Variable[DoubleReal] = {

    val eli = aspifOrDIMACSParserResult.symbolToEliOpt.map(_ (weightedAtomStr)).getOrElse(weightedAtomStr.toInt - 1)

    eliToVariableInCostFunctions.getOrElseUpdate(eli, dFFactory.`var`("freqx" + eli + "_", new DoubleReal(-1d /*value will later be updated with measured frequency*/)))

  }

  @inline def unmangleMeasuredAtomName(measuredAtom: String) = measuredAtom.replaceAllLiterally("ä", "_").replaceAllLiterally(".0" /*because we get a real number here*/ , "")

  /** Converts a postfix queue of arithmetic expression tokens (e.g. from org.scijava.parse) into a JAutoDiff (using, e.g., fork com.accelad.math.nilgiri.diff) expression, using a stack */
  def convertToDfNEW(tokensQueue: util.LinkedList[Object], measuredAtomsSet: mutable.HashSet[Pred],
                     aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult,
                     eliToVariableInCostFunctions: mutable.HashMap[Int, Variable[DoubleReal]],
                     satMode: Boolean):
  DifferentialFunction[DoubleReal] = {

    // TODO: see https://github.com/scijava/parsington/blob/master/src/test/java/org/scijava/parse/ExpressionParserTest.java

    val tokenStack = scala.collection.mutable.Stack[Object]() // can contain both autodiff. and org.scijava.parse. objects

    val dFFactory = new diff.DifferentialFunctionFactoryStasp()

    @inline def popArgOpt: Option[DifferentialFunction[DoubleReal]] = {

      val arg = tokenStack.pop()

      arg match {

        case dArg: DifferentialFunction[DoubleReal] => Some(dArg)

        case dNum: DoubleReal => Some(dFFactory.`val`(new DoubleReal(dNum.doubleValue())))

        case eVar: org.scijava.parse.Variable => {

          val eVarStr = eVar.getToken

          val dVar: autodiff.Variable[DoubleReal] = dFFactory.`var`(eVarStr, new DoubleReal(0d))

          Some(dVar)

        }

        //case dConst: autodiff.Variable[DoubleReal] => Some(dConst)

        //case dVar: autodiff.Constant[DoubleReal] => Some(dVar)

        case x => {

          stomp(-202, "Invalid type of argument in inner cost expression: " + x)

          None

        }

      }

    }

    import scala.collection.JavaConverters._

    val tokens = tokensQueue.asScala

    tokens.zipWithIndex.foreach { case (token, index) => { // we convert the raw postfix expression into a nilgiri.autodiff expression.
      // ...f(SomeMeasuredAtom)... becomes a DifferentialFunction "...freqxEliOfMeasuredUncertainAtom_..."

      token match {

        case symbolInExpr: org.scijava.parse.Variable => { // this can be an actual variable or a function name (!)

          val name = unmangleMeasuredAtomName(if (satMode) symbolInExpr.toString.stripPrefix("v") else symbolInExpr.toString) //symbol.toString.replaceAllLiterally("ä", "_")

          if (measuredAtomsSet.contains(name)) {

            tokenStack.push(generateMeasuredAtomVariableInCost(/*unmangleMeasuredAtomName*/ (name), dFFactory, aspifOrDIMACSParserResult, eliToVariableInCostFunctions))

          } else {

            //stomp(-203, name)

            tokenStack.push(symbolInExpr) // the symbol is either an actual function name or a part of a nested predicate, or there is no eli for the
            // symbol (in that case the symbol might be an undefined predicate), or the symbol is special variable "wDf" (moving target weight
            // of a hypothesis parameter atom - deprecated!).

          }

        }

        case number: java.lang.Float => {

          tokenStack.push(dFFactory.`val`(new DoubleReal(number.doubleValue())))

        }

        case number: java.lang.Double => {

          tokenStack.push(dFFactory.`val`(new DoubleReal(number.doubleValue())))

        }

        case number: java.lang.Integer => {

          tokenStack.push(dFFactory.`val`(new DoubleReal(number.doubleValue())))

        }

        case operator: org.scijava.parse.Operator if (operator.getToken != "(" && !operator.getToken.startsWith("<")) => {

          if (operator.getArity == 1) {

            popArgOpt.foreach((value: DifferentialFunction[DoubleReal]) =>

              if (operator.compareTo(org.scijava.parse.Operators.NEG) == 0)
                tokenStack.push(value.negate())
              else if (operator.compareTo(org.scijava.parse.Operators.POS) == 0)
                tokenStack.push(value)
              else
                stomp(-200, ": " + operator)

            )

          } else if (operator.getArity == 2) {

            val argROpt = popArgOpt

            val argLOpt = popArgOpt

            (argLOpt, argROpt) match {

              case (None, None) => stomp(-202, "Insufficient arguments for operator " + operator + " in inner cost expression")

              case (Some(argL), Some(argR)) => {

                if (operator == org.scijava.parse.Operators.ADD)
                  tokenStack.push(argL.plus(argR))
                else if (operator == org.scijava.parse.Operators.SUB)
                  tokenStack.push(argL.minus(argR))
                else if (operator == org.scijava.parse.Operators.MUL)
                  tokenStack.push(argL.mul(argR))
                else if (operator == org.scijava.parse.Operators.DIV)
                  tokenStack.push(argL.div(argR))
                else if (operator == org.scijava.parse.Operators.POW)
                  tokenStack.push(argL.pow(argR.getReal.toInt))
                else
                  stomp(-200, ": " + operator)

              }

              case _ => stomp(-200, ": " + operator)

            }

          }

        }

        case fnTag: org.scijava.parse.Function => { // <fn> (where fn is literally "fn", not a function name)

          val nextTag = tokenStack.pop()

          nextTag match {

            case groupTag: org.scijava.parse.Group => {

              val arity = groupTag.getArity

              val dArgs: Seq[DifferentialFunction[DoubleReal]] = (1 to arity).flatMap { case _ => popArgOpt }

              val eFnSymbol = tokenStack.pop()

              eFnSymbol match {

                case eFnSymbol: org.scijava.parse.Variable => { // this is how function names are represented in expression parser

                  val fnName = eFnSymbol.toString

                  if (fnName == "f") { // convert into variable freqx<EliOfMeasuredAtom>_

                    // The argument is an index into the list of measured atoms (implies that all atoms in inner cost functions must be measured (but not necessarily be parameter atoms!))

                    //tokenStack.push(dFFactory.phi(dArgs(0))) // a pseudo-real constant which is an index into measured atoms; these indices later need to be translated into (positive atom) elis.)
                    tokenStack.push(dArgs(0))

                  } else if (fnName == "sqrt")
                    tokenStack.push(dFFactory.sqrt(dArgs(0)))
                  else if (fnName == "subtr") // we need this because the delSAT caller might use prefix notation instead of operators +,-,*,/ etc
                    tokenStack.push(dArgs(1).minus(dArgs(0)))
                  else if (fnName == "add") // we need this because the delSAT caller might use prefix notation instead of operators +,-,*,/ etc
                    tokenStack.push(dArgs(1).plus(dArgs(0)))
                  else if (fnName == "mult") // we need this because the delSAT caller might use prefix notation instead of operators +,-,*,/ etc
                    tokenStack.push(dArgs(1).mul(dArgs(0)))
                  else if (fnName == "div") // we need this because the delSAT caller might use prefix notation instead of operators +,-,*,/ etc
                    tokenStack.push(dArgs(1).div(dArgs(0)))
                  else if (fnName == "pow") // we need this because the delSAT caller might use prefix notation instead of operators +,-,*,/ etc
                    tokenStack.push(dArgs(1).pow(dArgs(0).getReal.toInt))
                  else if (fnName == "abs")
                    tokenStack.push(dFFactory.sqrt(dFFactory.square(dArgs(0)))) // there's a less costly way using modulo, which dFFactory doesn't support
                  else if (fnName == "log")
                    tokenStack.push(dFFactory.log(dArgs(0)))
                  else if (fnName == "exp")
                    tokenStack.push(dFFactory.exp(dArgs(0)))
                  else if (fnName == "inv")
                    tokenStack.push(dArgs(0).inverse())
                  else if (fnName == "floor")
                    tokenStack.push(dFFactory.floor(dArgs(0)))
                  else if (fnName == "sin")
                    tokenStack.push(dFFactory.sin(dArgs(0)))
                  else if (fnName == "cos")
                    tokenStack.push(dFFactory.cos(dArgs(0)))
                  else if (fnName == "tan")
                    tokenStack.push(dFFactory.tan(dArgs(0)))
                  else if (fnName == "asin")
                    tokenStack.push(dFFactory.asin(dArgs(0)))
                  else if (fnName == "acos")
                    tokenStack.push(dFFactory.acos(dArgs(0)))
                  else if (fnName == "atan")
                    tokenStack.push(dFFactory.atan(dArgs(0)))
                  else if (fnName == "asinh")
                    tokenStack.push(dFFactory.asinh(dArgs(0)))
                  else if (fnName == "acosh")
                    tokenStack.push(dFFactory.acosh(dArgs(0)))
                  else if (fnName == "atanh")
                    tokenStack.push(dFFactory.atanh(dArgs(0)))
                  // TODO: support further functions?
                  else {

                    // At this point, we know that the "function" with its arguments is likely an atom (in form of a predicate with arguments) instead
                    // (since there are no other actual functions than f(...) and the built-in functions like sqrt(...)).

                    // Also, we know that the atom must be a measured atom, as these are the only ones allowed in
                    // cost functions (see M.Nickles ILP'18 paper for difference between parameter and measured variables or literals).

                    // We convert the "function application" therefore into a variable which is also (via its name) an eli of its corresponding measured atom
                    // (whose frequency in the sample the function f(measuredAtom) represents:

                    val measuredAtom = eFnSymbol + "(" + dArgs.reverse.map(d => {

                      d match {

                        case dVar: autodiff.Variable[DoubleReal] => dVar.getName

                        case x => x.toString

                      }

                    }).mkString(",") + ")"

                    val name = unmangleMeasuredAtomName(measuredAtom)

                    if (measuredAtomsSet.contains(name))
                      tokenStack.push(generateMeasuredAtomVariableInCost(name, dFFactory, aspifOrDIMACSParserResult, eliToVariableInCostFunctions))
                    else {

                      //stomp(-203, name)

                      tokenStack.push(dFFactory.`val`(new DoubleReal(0d)) /*dFFactory.`var`(name, new DoubleReal(-1d))*/)

                    }

                  }

                }

                case _ => stomp(-202)

              }

            }

            case _ => stomp(-202)

          }

        }

        case groupTag: org.scijava.parse.Group => { // "(number of things in brackets)", e.g. (but not only), arguments of a subsequent function tag <fn>

          if (index < tokens.length - 1 && tokens(index + 1).toString == "<Fn>")
            tokenStack.push(groupTag)
          else if (groupTag.getArity != 1)
            stomp(-202)

          // we just ignore (1) tags, unless they refer to the (arguments) of a function

        }

        case x => tokenStack.push(x)

      }

    }

    }

    val result = tokenStack.pop()

    result match {

      case dF: DifferentialFunction[DoubleReal] => dF

      case _ => {

        stomp(-202)

        null

      }

    }

  }

  /**
    * Reads input from file (if file name is given) or STDIN (in various alternative formats, with input typically generated by prasp2)
    *
    * @param fileNameOpt
    * @param mse see command line option -mse
    * @return Option[InputData]
    */
  def readInputData(fileNameOpt: Either[Option[String], String], mse: Boolean): (InputData, Boolean) = {

    /* We receive the inner cost functions as plain text formulas which we need to convert
       to DifferentialFunction[DoubleReal] here.

       There are two stages for each inner cost function:
          1) as an incoming cost string, e.g., (0.5-f(v))^2, where the arguments v of function f are measured atoms
          2) in autodiff format, with f(atom) everywhere replaced with variable freqx_(eli_of_v)

    */

    import java.nio.charset.StandardCharsets
    import java.nio.file.{Files, Paths}

    val inputStr: String = fileNameOpt match {

      case Left(Some(fileName)) => {

        new String(Files.readAllBytes(Paths.get(fileName)), StandardCharsets.UTF_8)

      }

      case Left(None) => {

        val inStream: BufferedInputStream = new BufferedInputStream(System.in, 32768)

        slurpFromInputStream(inStream)

      }

      case Right(progStr) => progStr

    }

    val satMode = !inputStr.startsWith("asp")

    def parseTermToPostfixTokens(innerCostFunStr: Pred) = {
      val underscoreReplInner: String = innerCostFunStr.replaceAllLiterally("_", "ä") // ExpressionParser only recognizes Java-style identifiers
      // with unicode characters but without leading underscores

      val postfixTokens: util.LinkedList[Object] = try {

        new ExpressionParser().parsePostfix(underscoreReplInner)

      } catch {

        case e: Throwable => {

          new PrintWriter("err") {
            write("Internal expression parse error for " + underscoreReplInner + "\n" + e);
            close
          }

          println("Internal expression parse error for " + underscoreReplInner + "\n" + e)

          System.err.println("Internal expression parse error for " + underscoreReplInner + "\n" + e)

          new util.LinkedList[Object]()

        }

      }
      postfixTokens
    }

    if (inputStr.startsWith("asp ") || inputStr.startsWith("p cnf ") || inputStr.startsWith("p pcnf ") || inputStr.startsWith("c ")) { // we allow "c " as first line in DIMACS too, but not, e.g., "cx"

      val posExtras = if (ignoreParamVariablesR) {

        stomp(-207)

        -1

      } else inputStr.indexOf("\npats ")

      {

        val spanningProgramASPNormGroundAspif_OrDIMACSCNF = if (posExtras == -1) inputStr.trim else inputStr.substring(0, posExtras - 1).trim

        val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult = if (!satMode)
          AspifPlainParser.parseAspif(spanningProgramASPNormGroundAspif_OrDIMACSCNF, shiftAndUnfoldForDisjunctions = true, noOfUnfolds = noOfUnfolds)
        else
          DIMACPlainSparser.parseDIMACS(spanningProgramASPNormGroundAspif_OrDIMACSCNF)

        val timerInputBNs = System.nanoTime()

        val symbolsSet: Set[Pred] = aspifOrDIMACSParserResult.symbols.toSet

        log("\notimer timerInputBNs: " + timerToElapsedMs(timerInputBNs) + " ms")

        val paramAtomsAndInnerCostsStr = if (posExtras == -1) "" else inputStr.substring(posExtras).trim

        val paramAtomsAndInnerCostsLines: Array[String] = if (posExtras == -1) Array[String]() else paramAtomsAndInnerCostsStr.lines.toArray

        val parameterAtomsSeq: Array[Pred] = (paramAtomsAndInnerCostsLines.take(1).mkString.trim.split("\\s+").drop(1) ++
          aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._1).distinct.filter(pa => {  // TODO: optimize

          val r = symbolsSet.contains(pa)

          if (!r)
            stomp(-204, pa)

          r

        })

        val eliToVariableInCostFunctions = mutable.HashMap[Int, Variable[DoubleReal]]()

        val costLines: ArrayBuffer[String] = paramAtomsAndInnerCostsLines.filter(_.startsWith("cost ")).to[ArrayBuffer].map(_.stripPrefix("cost ").replaceAllLiterally(" ", "")) ++
          aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._2  // TODO: optimize

        val evalLines = aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._3 // from _eval_("term","?") facts. ASP mode only.

        // (Remark: we can also process deprecated .opt files produced by prasp2 which contain [?] query lines, simply by
        // ignoring these lines.)

        // We now obtain the measured atoms from the cost function expressions. Note that not all measured atoms are necessarily also
        // parameter atoms (pats), the two sets can even be disjoint.

        // NB: in satMode, we require that each propositional variable in cost expressions is prefixed by letter "v". We keep this prefix only
        // in org.scijava.parse expressions (but NOT in diff expressions or parameter or measured atoms sets).

        val measuredAtomsSet: mutable.HashSet[Pred] = mutable.HashSet[Pred]() ++ (costLines ++ evalLines).foldLeft(ArrayBuffer[Pred]()) {

          case (ms: ArrayBuffer[Pred], costLine: String) => {

            val mil = ArrayBuffer[String]()

            var is = 0

            do {

              val s = costLine.indexOf("f(", is)

              if (s >= 0) {

                var b = 0

                var i = s + 2

                while (!(costLine(i) == ')' && b == 0)) {

                  if (costLine(i) == '(')
                    b += 1
                  else if (costLine(i) == ')')
                    b -= 1

                  i += 1

                  if (i >= costLine.length)
                    stomp(-202, costLine)

                }

                val arg: String = costLine.slice(s + 2, i)

                if (satMode) {

                  if (arg(0) != 'v')
                    stomp(-206, "Measured variables in cost expressions need to be prefixed by 'v' in SAT mode")

                  mil.append(arg.stripPrefix("v"))

                } else
                  mil.append(arg)

                is = s + 2

              } else
                is = costLine.length

            } while (is < costLine.length)

            ms ++ mil

          }

        }.toSet.filter(pa => {

          val r = symbolsSet.contains(pa)

          if (!r)
            stomp(-204, pa)

          r

        })

        val oldCostLinesSize = costLines.length

        val hypothesisParamAtoms = parameterAtomsSeq.filterNot(measuredAtomsSet.contains(_))

        if (!hypothesisParamAtoms.isEmpty && autoGenerateCostLinesForHypotheses) { // deprecated

          hypothesisParamAtoms.map(hypothParamAtom => {

            if (ensureParamAtomsAreMeasured)
              measuredAtomsSet.add(hypothParamAtom)

            // same effect as _cost_("(wDf-f(hypoth))^2").

            val varName = if (satMode) "v" + hypothParamAtom else hypothParamAtom

            costLines.append("(wDf-f(" + varName + "))^2")

          })

          if (verbose) {

            println("Parameter atoms not part of cost expressions (hypothesis parameter atoms): " + hypothesisParamAtoms.mkString(" "))

            println("Auto-generated cost expressions for hypothesis parameter atoms:\n" + costLines.drop(oldCostLinesSize).mkString("\n"))

          }

        }

        val measuredAtomsSeq = measuredAtomsSet.toArray //.sorted

        log("\notimer timerInputBNs A: " + timerToElapsedMs(timerInputBNs) + " ms")

        val innerCostExpressionInstancesPerUncertainAtom: Array[DifferentialFunction[DoubleReal]] = {

          costLines.toArray.map(costLine => {

            val innerCostFunStr = costLine.stripPrefix("cost ").trim

            if (!mse) {

              val postfixTokens: _root_.java.util.LinkedList[_root_.java.lang.Object] = parseTermToPostfixTokens(innerCostFunStr)

              val dfInnerCostExpression = convertToDfNEW(postfixTokens, measuredAtomsSet, aspifOrDIMACSParserResult, eliToVariableInCostFunctions, satMode = satMode)

              dfInnerCostExpression

            } else {

              val dFFactory = new diff.DifferentialFunctionFactoryStasp() //null

              val dNumStr = innerCostFunStr.drop(1).takeWhile(c => c.isDigit || c == '.')

              if (dNumStr.isEmpty) {

                stomp(-5003)

              }

              val weightDNum = dFFactory.`val`(new DoubleReal(java.lang.Double.parseDouble(dNumStr).doubleValue()))

              // (if you get a numerical format exception here, check first whether flag -mse is set and appropriate)

              val weightedAtomStrV = innerCostFunStr.drop(1).dropWhile(_ != '(').drop(1).dropRight(4)

              val weightedAtomStr = if (satMode) weightedAtomStrV.stripPrefix("v") else weightedAtomStrV

              val atomName = unmangleMeasuredAtomName(weightedAtomStr)

              val uncertAtomVar = if (measuredAtomsSet.contains(atomName))
                generateMeasuredAtomVariableInCost(atomName, dFFactory, aspifOrDIMACSParserResult, eliToVariableInCostFunctions)
              else {

                //stomp(-203, atomName)

                //dFFactory.`var`(atomName, new DoubleReal(-1d))

                dFFactory.`val`(new DoubleReal(0d))

              }

              val innerMSEDTerm: DifferentialFunction[DoubleReal] = weightDNum.minus(uncertAtomVar /*phi*/).pow(2)

              innerMSEDTerm

            }

          })

        }

        val evalExpressionToFct: Map[String, DifferentialFunction[DoubleReal]] = {

          evalLines.map(evalLine => {

            val evalTermStr = evalLine.stripPrefix("eval ").trim // deprecated TODO: remove

            val postfixTokens: _root_.java.util.LinkedList[_root_.java.lang.Object] = parseTermToPostfixTokens(evalTermStr)

            val dfEvalExpression = convertToDfNEW(postfixTokens, measuredAtomsSet, aspifOrDIMACSParserResult, eliToVariableInCostFunctions, satMode = satMode)

            (evalTermStr, dfEvalExpression)

          }).toMap

        }

        log("\notimer timerInputBNs B: " + timerToElapsedMs(timerInputBNs) + " ms")

        (InputData(/*Some(spanningProgramASPNormGroundAspif_OrDIMACSCNF)*/ aspifOrDIMACSParserResult,
          Some(new UncertainAtomsSeprt(parameterAtomsSeq, measuredAtomsSeq,
            innerCostExpressionInstancesPerUncertainAtom, eliToVariableInCostFunctions, evalExpressionToFct))), satMode)

      }

    } else {

      if(inputStr(0).isWhitespace)
        stomp(-100, "Observe that input files are not allowed to start with whitespace characters")
      else
        stomp(-100)

      (null, false)

    }

  }

  /**
    * Wrapper method for invoking the multimodel sampler. See sampleMulti() in SolverMulti.scala for the actual sampling method.
    *
    * @param inputData
    * @param noOfModels
    * @param noOfSecondaryModels
    * @param thresholdOpt
    * @param satMode
    * @return Sample (bag of sampled models) in symbolic form and as list of (eli array, eli hash set). An eli is our internally used numerical representation
    *         of a literal (not identical to numerical literals in DIMACS or aspif!).
    */
  def invokeSampler(inputData: InputData,
                    noOfModels: Int, noOfSecondaryModels: Int,
                    thresholdOpt: Option[Double],
                    satMode: Boolean /*, additionalSolverArgs: mutable.HashMap[String, String]*/):
  ((mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)]), AspifOrDIMACSPlainParserResult) = {

    if (noOfMinibenchmarkTrials > 1)
      Thread.sleep(3000)

    println("delSAT " + commandlineDelSAT.delSAT.version + "\n")

    val timerInitNs = System.nanoTime()

    //assert(inputData.spanningProgramAspifOrDIMACSOpt.isDefined)

    log("inittimer after Parse: " + timerToElapsedMs(timerInitNs) + " ms")

    val prep: Preparation = new solving.Preparation(inputData.aspifOrDIMACSPlainParserResult, inputData.costsOpt, satModeR = satMode,
      omitAtomNogoods = false)

    log("inittimer after Preparation: " + timerToElapsedMs(timerInitNs) + " ms")

    var sampledModels = null.asInstanceOf[(mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)])]

    assert(noOfMinibenchmarkTrials == 1 || noOfMinibenchmarkTrials >= 10)

    val warmupTrialNo = noOfMinibenchmarkTrials / 10

    val trialDurations = (1 to warmupTrialNo + noOfMinibenchmarkTrials).map(trial => {

      if (verbose)
        println("Solving... " + (if (noOfMinibenchmarkTrials > 1) "(trial " + trial + ")" else ""))

      System.gc()

      val startTrialTimeNs = System.nanoTime()

      val solver = new SolverMulti(prep)

      val sampleMultiConf = solver.SampleMultiConf(
        requestedNoOfModelsBelowThresholdOrAuto = noOfModels,
        prep = prep,
        requestedNumberOfModels = noOfModels,
        noOfSecondaryModels = noOfSecondaryModels,
        threshold = thresholdOpt.getOrElse(defaultThreshold),
        maxIt = maxSamplingIterations)

      sampledModels = solver.sampleMulti(sampleMultiConf)

      if (trial <= warmupTrialNo) 0l else System.nanoTime() - startTrialTimeNs

    })

    log("inittimer after solving & sampling: " + timerToElapsedMs(timerInitNs) + " ms")

    val avgDuration = ((trialDurations.sum.toDouble / noOfMinibenchmarkTrials.toDouble) / 1000000).toInt

    if (noOfMinibenchmarkTrials > 1)
      println("\n@@@@@@ Average overall duration solver.sampleMulti: " + avgDuration + " ms\n")

    (sampledModels, inputData.aspifOrDIMACSPlainParserResult)

  }

  /**
    * Command line processing
    *
    * @param args
    */
  def main(args: Array[String]): Unit = {

    val timerOverallNs = System.nanoTime()

    FloatArrayUnsafeS.init(unsafe)

    ByteArrayUnsafeS.init(unsafe)

    try {

      import java.lang.management.ManagementFactory

      import com.sun.management.HotSpotDiagnosticMXBean

      val hsDiag = ManagementFactory.getPlatformMXBean(classOf[HotSpotDiagnosticMXBean])

      //hsDiag.setVMOption("MaxInlineSize", "4096")

      //hsDiag.setVMOption("FreqInlineSize", "4096")

      //hsDiag.setVMOption("InlineSmallCode", "4096")

      //hsDiag.setVMOption("AllocatePrefetchStyle", "1")

    } catch {

      case t: Throwable => stomp(-5, t.toString)

    }

    if (debug) {

      val p = System.getProperties

      p.list(System.out)

      System.out.println("\navailableProcessors: " + Runtime.getRuntime.availableProcessors)

      System.out.println("maxMemory: " + Runtime.getRuntime.maxMemory / 1073741824l + " GB")

      System.out.println("freeMemory: " + Runtime.getRuntime.freeMemory / 1073741824l + " GB")

      System.out.println

    }

    val arglist = args.toList

    val additionalSolverArgs = mutable.HashMap[String, String]()

    type ArgsList = List[(Symbol, List[String])]

    def nextArg(argsList: ArgsList, list: List[String]): ArgsList = {

      log("argsList: " + arglist)

      @inline def isSwitch(s: String) = (s(0) == '-')

      list match {

        case Nil => argsList

        case ("--version" | "-v" | "--about") :: tail => {

          println(copyrightAndVersionText)

          println(thirdPartyLibs)

          sys.exit(0)

        }

        case ("--help" | "-h") :: tail => {

          println(copyrightAndVersionText + "\n\n" + helpText)

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

            val argT = if (arg == "0") Int.MaxValue.toString else arg // NB: this is different from -n 0 like in Clingo, because delSAT doesn't do enumeration but sampling

            nextArg(argsList ++ Map('n -> List(argT)), tail)

          }

        }

        case ("-s") :: arg :: tail => {

          if (!arg.forall(_.isDigit)) {

            stomp(-1, "Positive number or -1 expected after -s")

            argsList

          } else {

            if(arg != "-1")
              nextArg(argsList ++ Map('s -> List(arg)), tail)
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

        case "--solverarg" :: arg1 :: arg2 :: tail => {

          additionalSolverArgs.update(arg1, arg2)

          nextArg(argsList, tail)

        }

        case "-mse" :: tail => {

          nextArg(argsList ++ List('mse -> List()), tail)

        }

        case "--showaux" :: tail => {

          nextArg(argsList ++ List('showaux -> List()), tail)

        }

        case fileName :: tail if !isSwitch(fileName) => {

          nextArg(argsList ++ List('inputFile -> List(fileName)), tail)

        }

        case option :: tail if option.startsWith("-") => stomp(-1, option); nextArg(argsList, tail)

      }

    }

    val parsedArgs: ArgsList = nextArg(Nil, arglist)

    log("Command line arguments in delSAT: " + parsedArgs)

    val parsedArgsMap: mutable.HashMap[Symbol, List[String]] = mutable.HashMap[Symbol, List[String]]().++(parsedArgs.toMap)

    log("\notime args: " + timerToElapsedMs(timerOverallNs) + " ms")

    val noOfModels = parsedArgsMap.getOrElse('n, List(defaultNoOfModelsStr)).head.toInt

    val noOfSecondaryModels = parsedArgsMap.getOrElse('s, List(defaultNoOfModelsStr)).head.toInt

    val thresholdOpt: Option[Double] = parsedArgsMap.get('t).map(_.head.toDouble)

    val showaux = parsedArgsMap.contains('showaux)

    val mse = parsedArgsMap.contains('mse)

    overrideSolverArgs(additionalSolverArgs)

    val (inputData: InputData, satMode) = if (parsedArgs.exists(_._1 == 'enforceReadingFromSTDIN) || !parsedArgs.exists(_._1 == 'inputFile))
      readInputData(Left(None), mse = mse) // we read from STDIN
    else {

      val fileName = parsedArgsMap.get('inputFile).get.head

      readInputData(Left(Some(fileName)), mse = mse)

    }

    log("\notimer inputData: " + timerToElapsedMs(timerOverallNs) + " ms")

    val (sampledModels: (mutable.Seq[Array[Pred]], ArrayBuffer[(Array[Eli], IntOpenHashSet)]),
    parserResult: AspifOrDIMACSPlainParserResult) =
      invokeSampler(inputData, noOfModels, noOfSecondaryModels, thresholdOpt, satMode = satMode)

    if (!sampledModels._1.isEmpty) {

      val hideAuxPreds: Int = if (showaux) 4 else 5

      val sampledModelsWithSymbolsCleanedR: mutable.Seq[Array[Pred]] = if (hideAuxPreds == 4)
        sampledModels._1.map(_.filterNot(isLatentSymbolAuxAtom(_)))
      else if (hideAuxPreds == 1) sampledModels._1.map(_.filterNot(a => isAuxAtom(a) && !isSpanAuxAtom(a)))
      else if (hideAuxPreds == 2) sampledModels._1.map(_.filterNot(isAuxAtom(_)))
      else if (hideAuxPreds == 3) sampledModels._1.map(_.filterNot(isSpanAuxAtom(_)))
      else if (hideAuxPreds == 5) sampledModels._1.map(_.filterNot(a => isSpanAuxAtom(a) || isLatentSymbolAuxAtom(a)))
      else
        sampledModels._1

      val symbolsSeq = parserResult.symbols

      val sampledModelsWithSymbolsCleaned: mutable.Seq[Array[Pred]] = if (!satMode) sampledModelsWithSymbolsCleanedR else
        sampledModels._2.map((model: (Array[Eli], IntOpenHashSet)) => {

          val fullModelWithSymbols = symbolsSeq.map(symbol => if (model._2.contains(symbol.toInt - 1)) symbol else "-" + symbol)

          if (enforceSanityChecks && satMode) { // see further sanity checks in SolverMulti.scala

            if (satMode) println("Checking model against original DIMACS-CNF clauses...")

            var checkedDIMACSclauses = 0

            val violatedDIMACSClauses: Boolean = if (!parserResult.clauseTokensOpt.isDefined) {

              println("WARNING: enforceSanityChecks=true but cannot determine violatedDIMACSClauses!");

              false

            } else {

              val modelCandWithSymbolsSet = fullModelWithSymbols.toSet

              parserResult.clauseTokensOpt.get.exists(clause => { // TODO: optimize:

                val clauseFulfilled = clause.exists((dimacsVarPN: Int) => {

                  modelCandWithSymbolsSet.contains(dimacsVarPN.toString)

                })

                if (!clauseFulfilled)
                  println("\\\\\\\\  Violated original CNF clauses: " + clause.mkString(" "))

                checkedDIMACSclauses += 1

                if (checkedDIMACSclauses % 500000 == 0)
                  println("  original clauses checked so far: " + checkedDIMACSclauses + " / " + parserResult.clauseTokensOpt.get.length)

                !clauseFulfilled

              })

            }

            assert(checkedDIMACSclauses == parserResult.clauseTokensOpt.get.length &&
              checkedDIMACSclauses == parserResult.directClauseNogoodsOpt.get.length)

            println("Any violated original DIMACS clauses: " + violatedDIMACSClauses + " (checked: " + checkedDIMACSclauses + ")")

            if (violatedDIMACSClauses) {

              println("\n\\/\\/\\/\\/ Internal error: Sanity check on original DIMACS clauses failed on model candidate!\n")

              sys.exit(-5)

            }

          }

          fullModelWithSymbols

        })

      if(!addHocConjunctiveQueries.isEmpty || !addHocDisjunctiveQueries.isEmpty) {

        println("Results of ad hoc queries:\n")

        addHocConjunctiveQueries.foreach((conjAtoms: Seq[String]) => {

          val freqInModels = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

            conjAtoms.forall(atom => {

              // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
              // are simply absent positive atoms in the orignal model.

              model.contains(atom)

            })}).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

          println("Pr(" + conjAtoms.mkString(" ^ ") + ") = " + freqInModels)

        })

        addHocDisjunctiveQueries.foreach((conjAtoms: Seq[String]) => {

          val freqInModels = sampledModelsWithSymbolsCleaned.count((model: Array[Pred]) => {

            conjAtoms.exists(atom => {

              // Recall that in ASP mode, any classical negation op "-" would be part of the symbol itself, whereas in SAT mode, the negative variables (-atom)
              // are simply absent positive atoms in the orignal model.

              model.contains(atom)

            })}).toDouble / sampledModelsWithSymbolsCleaned.length.toDouble

          println("Pr(" + conjAtoms.mkString(" v ") + ") = " + freqInModels)

        })

        println

      }

      // ----------------------

      if (printAnswers)
        sampledModelsWithSymbolsCleaned.zipWithIndex.foreach { case (model, index) =>
          System.out.println("Answer: " + (index + 1) + "\n" + model.mkString(" ")) // recall that in contrast to plain ASP solvers, the same
          // sampled answer can be printed multiple times here.
        }

      System.out.println("SATISFIABLE") // this must be printed _directly_ after the list of answers (no empty line allowed in between)

      // ----------------------

    }

    val overallTimeMs = timerToElapsedMs(timerOverallNs) // doesn't include JVM startup time

    println("\nOverall time spent in delSAT (incl parsing/pre-/post-processing): " + overallTimeMs + " ms (" + (overallTimeMs / 1000f) + " sec, " + (overallTimeMs / 1000f / 60f) + " min)")
    // Note: string "Overall time spent in delSAT" literally used in some benchmark programs to identify this line with the time.

    if (!omitSysExit0) // we need exit if jar isn't loaded dynamically into the current JVM. Otherwise, we need return
      sys.exit(0)
    else
      return

  }

}
