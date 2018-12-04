/**
  * DelSAT
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE
  *
  */

package commandline

import java.io._
import java.util

import aspIOutils._

import com.accelad.math.nilgiri.{DoubleReal, autodiff}
import com.accelad.math.nilgiri.autodiff.DifferentialFunction

import diff.UncertainAtomsSeprt

import org.scijava.parse.ExpressionParser

import parsing.{AspifPlainParser, DIMACPlainSparser}

import sharedDefs._

import solving.{Preparation, SolverMulti}

import sun.misc.Unsafe

import utils.{FloatArrayUnsafe, IntArrayUnsafe, LongArrayUnsafe}

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

  // For flight control, use e.g. -XX:+UnlockCommercialFeatures -XX:+FlightRecorder -XX:StartFlightRecording=duration=60s,filename=delsatRecording.jfr

  var verbose = false


  val noOfMinibenchmarkTrials = 1 // this is just for a quick local mini-benchmark to get a (very) rough idea of performance

  val enforceSanityChecks = false && noOfMinibenchmarkTrials == 1 // NB: for ASP, invalid models are first bounced back to the solver before this check could occur

  val printAnswers = true && noOfMinibenchmarkTrials == 1 && !enforceSanityChecks // false only for debugging purposes

  assert(!(printAnswers && enforceSanityChecks))

  val version = "0.2"

  val copyrightAndVersionText = "DelSAT " + version + "\nCopyright (c) 2018 Matthias Nickles\nLicense: https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE"

  val defaultNoOfModelsStr = "-1"

  val thirdPartyLibs = "DelSAT " + version + """ uses the following third-party software:

JAutoDiff (https://github.com/accelad-com/nilgiri-math)
  Copyright (c) 2017 AccelaD
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
     A SAT and ASP solver for sampling-based multi-model optimization.

     Usage:

     delSAT [--version|-v|--about] [--help|-h]
            [-n <n>] [-t <t>] [-ci] [-mse]
            [--solverarg "name" "value"]* [<filename>]

     Reads from a file or STDIN input programs or clauses in aspif or DIMACS-CNF format or
     extended aspif or DIMACS-CNF with list of parameter atoms and cost function(s). To
     obtain aspif from a non-ground plain Answer Set Program, preprocess using, e.g.,
     clingo myProg.lp --trans-ext=all --pre=aspif
     Input is obtained from STDIN if no file name is provided or if flag -ci is specified.

     Arguments:

     -n <n> lets the sampler sample <n> (not necessarily different) models such
     that the specified or default threshold is reached. If -n is missing, sampling
     continues until the minimum multiset of models has been generated st. the specified
     or default threshold (or timeout) is reached. Models are either stable models
     (answer sets) or satisfying Boolean assignments (in case the input is in extended
     or plain DIMACS format). Use case of -n is primarly increase of entropy with
     larger number of models.

     -t <threshold> specifies the error threshold for the total cost function (small
     threshold means higher accuracy but more time required for sampling)

     -mse promises that the costs are provided entirely as part costs with inner MSE terms
     of the form (p-f(v))^2 where p is a probability and v is a parameter atom symbol
     (random variable). -mse is optional even for MSE-type costs but allows for faster
     parsing of large lists of such functions.

     --solverarg "argname" "value" specifies additional solver arguments (see
     sharedDefs.scala for the full list). Multiple --solverarg can be specified.
     Examples:
       --solverarg "partDerivComplete" "true" (activates support for certain
       non-MSE-style costs)
       --solverarg "maxCompetingSolverThreads" "6" --solverarg "freeEliSearchConfigsP" "2 3 3 4 5 7"
       activates parallel portfolio solving using max. 6 threads and approaches 0,3,3,4,2,6
       --solverarg "diversify" "true" (aims at generating more diverse models, might
       decrease speed. Note that while this might achieve some degree of uniformity, DelSAT
       does not aim to be a uniform sampling tool.)

     --showaux shows auxiliary atoms introduced for spanning formulas (omitted by
     default).

     -ci enforces reading from STDIN.

     --verbose shows additional information

     --version|-v|--about prints information about version and third-party software
     used by DelSAT (including copyrights and license information), then exits.

     --help|-h prints this information and exits.
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

    -100 -> ("Invalid input data", ERROR),

    -101 -> ("Timeout or maximum number of trials exceeded. Sampling aborted", WARNING),

    -102 -> ("Unsupported line in aspif input", ERROR),

    -103 -> ("Weighted atoms only supported via cost functions", ERROR),

    -104 -> ("Disjunction found in ASP input. Translation of disjunctions using shift/unfold doesn't guarantee a complete set of answers set.\n Consider increasing the number of unfolds in case of non-convergence.", ERROR),

    -200 -> ("Unknown operator in expression", ERROR),

    -201 -> ("Call of unknown function in expression", ERROR),

    -202 -> ("Syntax error in cost function", ERROR),

    -5000 -> ("Specified local greedy decision policy won't work as expected since some measured atoms are not parameter atoms", WARNING),

    -5001 -> ("Lists of parameter or measured atoms found both separately given and within DIMACS-CNF-PR - using only the former lists.", WARNING),

    -5002 -> ("assureIsTight=true; This will lead to non-termination or wrong results if the ASP program isn't tight.", WARNING),

    -5003 -> ("Inner cost function(s) invalid for selected type of differentiation. Try with command line argument\n --solverarg \"partDerivComplete\" \"true\"", ERROR),

    -5004 -> ("Unsupported type of rule", ERROR),

    -5005 -> ("Undefined predicate", WARNING),

    -5006 -> ("Incompatible settings, see def checkSettings in sharedDefs.scala for details", ERROR),

    -5007 -> ("Experimental feature, might give wrong results", WARNING),

    -5008 -> ("Sampling ended but specified threshold not reached!", WARNING),

    -5009 -> ("Invalid setting, see sharedDefs.scala for details", ERROR),

    -10000 -> ("Internal error", ERROR)

  )

  def stomp(code: Int, additionalInfo: String = "") = {

    val message = stompMessages(code)

    if (message._2 == ERROR) {

      System.err.println("\nError: " + message._1 + " " + additionalInfo)

      sys.exit(code)

    } else if (message._2 == WARNING)
      System.out.println("Warning: " + message._1 + " " + additionalInfo)
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

  final case class InputData(spanningProgramAspifOrDIMACSOpt: Option[String],
                             costsOpt: Option[UncertainAtomsSeprt]) {}

  @inline def measuredAtomIndex(atom: Pred, measuredAtomsSeqSorted: Array[String]): Int = {

    val measuredAtomNameInExpr = atom

    val m: String = measuredAtomNameInExpr.replaceAllLiterally("ä", "_").replaceAllLiterally(".0" /*because we get a real number here*/ , "")

    util.Arrays.binarySearch(measuredAtomsSeqSorted.asInstanceOf[Array[Object]] /*Scala arrays aren't covariant*/ , m)
    // TODO: ^^ check again, find cleaner solution

  }

  /** Converts a postfix queue of arithmetic expression tokens (e.g. from org.scijava.parse) into a com.accelad.math.nilgiri.diff-expression, using a stack */
  def convertToDfNEW(tokensQueue: util.LinkedList[Object], measuredAtomsSeqSorted: Array[String], measuredAtomsSet: mutable.HashSet[Pred]):
  DifferentialFunction[DoubleReal] = {

    // TODO: see https://github.com/scijava/parsington/blob/master/src/test/java/org/scijava/parse/ExpressionParserTest.java

    val tokenStack = scala.collection.mutable.Stack[Object]() // can contain both autodiff. and org.scijava.parse. objects

    val dFFactory = new diff.DifferentialFunctionFactoryStasp()

    @inline def popArgOpt: Option[DifferentialFunction[DoubleReal]] = {

      val arg = tokenStack.pop()

      arg match {

        case dArg: DifferentialFunction[DoubleReal] => Some(dArg)

        case dNum: DoubleReal => {

          Some(dFFactory.`val`(new DoubleReal(dNum.doubleValue())))

        }

        case eVar: org.scijava.parse.Variable => {

          val dVar: autodiff.Variable[DoubleReal] = dFFactory.`var`(eVar.getToken,
            new DoubleReal(-1d))

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
      // ...f(SomeMeasuredAtom)... becomes a DifferentialFunction "...phi(indexOfMeasuredAtom)..."
      // (analogously for w(SomeMeasuredAtom))

      token match {

        case symbol: org.scijava.parse.Variable => { // this can be an actual variable or a function name (!)

          val name = symbol.toString.replaceAllLiterally("ä", "_")

          if (measuredAtomsSet.contains(name)) {

            val dConstFromMeasuredAtomIndex = dFFactory.`val`(new DoubleReal(measuredAtomIndex(name, measuredAtomsSeqSorted)))
            // ^a pseudo-real constant which is an index into measures atoms; these indices later need to be
            // translated into (positive atom) elis.

            tokenStack.push(dConstFromMeasuredAtomIndex)

          } else
            tokenStack.push(symbol) // the symbol is either an actual function name or a part of a nested predicate

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

                  if (fnName == "f") { // convert into phi(indexOfMeasuredUncertainAtom)

                    // The argument is an index into the list of measured atoms (implies that all atoms in inner cost functions must be measured (but not necessarily parameter atoms))

                    tokenStack.push(dFFactory.phi(dArgs(0))) // a pseudo-real constant which is an index into measured atoms; these indices later need to be translated into (positive atom) elis.)

                  } else if (fnName == "sqrt")
                    tokenStack.push(dFFactory.sqrt(dArgs(0)))
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
                    // (since there are no other actual functions than f(...), w(...) and the built-in functions like sqrt(...)).

                    // Also, we know that the atom must be a measured atom, as these are the only ones allowed in
                    // cost functions.

                    // We convert the "function application" therefore into a constant whose "real" value is the index
                    // into the list of measured atoms:

                    val measuredAtom = eFnSymbol + "(" + dArgs.reverse.map(d => {

                      d match {

                        case dVar: autodiff.Variable[DoubleReal] => dVar.getName

                        case x => x.toString

                      }

                    }).mkString(",") + ")"

                    val dConst = dFFactory.`val`(new DoubleReal(measuredAtomIndex(measuredAtom, measuredAtomsSeqSorted)))

                    tokenStack.push(dConst)

                  }

                }

                case _ => stomp(-202)

              }

            }

            case _ => stomp(-202)

          }

        }

        case groupTag: org.scijava.parse.Group => { // "(number of things in brackets)", e.g. (but not only), arguments of a subsequent function tag <fn>

          if (tokens(index + 1).toString == "<Fn>")
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
    */
  def readInputData(fileNameOpt: Option[String], mse: Boolean = false): Option[InputData] = {

    /* In contrast to nablaSAT, we receive the inner cost functions as plain text formulas which we need to convert
       to DifferentialFunction[DoubleReal] here.

       There are three stages for each inner cost function:
          1) as a string coming from prasp2 or the user, e.g., (0.5-f(v))^2
          2) in autodiff format, with f(atom) replaced with phi(index_in_measured_atoms_seq),
              e.g., (0.5-phi(3.0))^2, where 3.0 is actually an int (index)
              (produced in this method)
          3) in autodiff format, with phi(index) replaced with variable freqxEli_, where Eli
              is the measured atom eli. E.g., (0.5-freqx5_)^2
    */

    import java.nio.charset.StandardCharsets
    import java.nio.file.Files
    import java.nio.file.Paths

    val inputStr: String = fileNameOpt match {

      case Some(fileName) => {

        val timer = System.nanoTime()

        new String(Files.readAllBytes(Paths.get(fileName)), StandardCharsets.UTF_8)

      }

      case None => {

        val inStream: BufferedInputStream = new BufferedInputStream(System.in, 32768)

        slurpFromInputStream(inStream)

      }

    }

    if (inputStr.startsWith("asp ") || inputStr.startsWith("p cnf ") || inputStr.startsWith("c ")) { // we allow "c " as first line in DIMACS too, but not, e.g., "cx"

      val posExtras = inputStr.indexOf("\npats ")

      if (posExtras == -1)
        Some(InputData(Some(inputStr.trim), None))
      else {

        val spanningProgramASPNormGroundAspif_OrDIMACSCNF = if (posExtras == -1) inputStr.trim else inputStr.substring(0, posExtras - 1).trim

        val paramAtomsAndInnerCostsStr = if (posExtras == -1) "" else inputStr.substring(posExtras).trim

        val paramAtomsAndInnerCostsLines: Array[String] = paramAtomsAndInnerCostsStr.lines.toArray

        val parameterAtomsSeq: Array[Pred] = paramAtomsAndInnerCostsLines.take(1).mkString.trim.split("\\s+").drop(1).distinct

        val costLines: Array[String] = paramAtomsAndInnerCostsLines.filter(_.startsWith("cost ")).map(_.stripPrefix("cost ").trim)

        // we obtain the measured atoms from the cost function expressions (whereas "pats ..." is the list of parameter atoms):

        val measuredAtomsSet: mutable.HashSet[Pred] = mutable.HashSet[Pred]() ++ costLines.foldLeft(ArrayBuffer[Pred]()) {

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

                mil.append(arg)

                is = s + 2

              } else
                is = costLine.length

            } while (is < costLine.length)

            ms ++ mil

          }
        }.toSet

        val measuredAtomsSeqSorted = measuredAtomsSet.toArray.sorted

        val innerCostExpressionInstancesPerUncertainAtom: Array[DifferentialFunction[DoubleReal]] = {

          costLines.map(costLine => {

            val innerCostFunStr = costLine.stripPrefix("cost ").trim

            if (!mse) {

              val underscoreReplInner = innerCostFunStr.replaceAllLiterally("_", "ä") // ExpressionParser only recognizes Java-style identifiers
              // with unicode characters but without leading underscores

              val postfixTokens = new ExpressionParser().parsePostfix(underscoreReplInner)

              val dfInnerCostExpression = convertToDfNEW(postfixTokens, measuredAtomsSeqSorted, measuredAtomsSet)

              dfInnerCostExpression

            } else {

              val dFFactory = new diff.DifferentialFunctionFactoryStasp() //null /*missing until we deserialize in nablaSAT*/)

              val dNumStr = innerCostFunStr.drop(1).takeWhile(c => c.isDigit || c == '.')

              val weightDNum = dFFactory.`val`(new DoubleReal(java.lang.Double.parseDouble(dNumStr).doubleValue()))

              // (if you get a numerical format exception here, check first whether flag -mse is set and appropriate)

              val weightedAtom = innerCostFunStr.drop(1).dropWhile(_ != '(').drop(1).dropRight(4)

              val weightedAtomIndexDConst = dFFactory.`val`(new DoubleReal(measuredAtomIndex(weightedAtom, measuredAtomsSeqSorted)))

              val phi = dFFactory.phi(weightedAtomIndexDConst)

              val innerMSEDTerm = weightDNum.minus(phi).pow(2)

              innerMSEDTerm

            }

          })

        }

        Some(InputData(Some(spanningProgramASPNormGroundAspif_OrDIMACSCNF), Some(new UncertainAtomsSeprt(parameterAtomsSeq, measuredAtomsSeqSorted,
          innerCostExpressionInstancesPerUncertainAtom, null))))

      }

    } else {

      stomp(-100)

      None

    }

  }

  def invokeSampler(inputData: InputData, noOfModels: Int, thresholdOpt: Option[Double],
                    showaux: Boolean, satMode: Boolean, additionalSolverArgs: mutable.HashMap[String, String]):
  (mutable.Seq[Array[Pred]], AspifOrDIMACSPlainParserResult) = {

    if (noOfMinibenchmarkTrials > 1)
      Thread.sleep(3000)

    println("DelSAT " + commandline.delSAT.version + "\n")

    val timerInitNs = System.nanoTime()

    assert(inputData.spanningProgramAspifOrDIMACSOpt.isDefined)

    overrideSolverArgs(additionalSolverArgs)

    val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult = if (!satMode)
      AspifPlainParser.parseAspif(inputData.spanningProgramAspifOrDIMACSOpt.get, shiftAndUnfoldForDisjunctions = true, noOfUnfolds = noOfUnfolds)
    else
      DIMACPlainSparser.parseDIMACS(inputData.spanningProgramAspifOrDIMACSOpt.get)

    log("inittimer after Parse: " + timerToElapsedMs(timerInitNs) + " ms")

    val prep: Preparation = new solving.Preparation(aspifOrDIMACSParserResult, inputData.costsOpt, satModeR = satMode,
      omitAtomNogoods = false)

    log("inittimer after Preparation: " + timerToElapsedMs(timerInitNs) + " ms")

    var res = mutable.Seq[Array[Pred]]()

    val warmupTrialNo = if (noOfMinibenchmarkTrials > 1) 10 else 0

    val trialDurations = (1 to warmupTrialNo + noOfMinibenchmarkTrials).map(trial => {

      if (verbose)
        println("Solving... " + (if (noOfMinibenchmarkTrials > 1) "(trial " + trial + ")" else ""))

      val startTrialTimeNs = System.nanoTime()

      val solver = new SolverMulti(prep)

      val sampleMultiConf = solver.SampleMultiConf(inputData.costsOpt,
        requestedNoOfModelsBelowThresholdOrAuto = noOfModels,
        prep = prep,
        requestedNumberOfModels = noOfModels,
        threshold = thresholdOpt.getOrElse(0.001d),
        maxIt = 100000)

      res = solver.sampleMulti(sampleMultiConf)

      if (trial <= warmupTrialNo) 0l else System.nanoTime() - startTrialTimeNs

    })

    log("inittimer after solving & sampling: " + timerToElapsedMs(timerInitNs) + " ms")

    val avgDuration = ((trialDurations.sum.toDouble / noOfMinibenchmarkTrials.toDouble) / 1000000).toInt

    if (noOfMinibenchmarkTrials > 1) /*println("\nOverall duration solving and sampling: " + avgDuration + " ms\n") else*/
      println("\n@@@@@@ Average overall duration solver.sampleMulti: " + avgDuration + " ms\n")

    (res, aspifOrDIMACSParserResult)

  }

  def main(args: Array[String]): Unit = {

    //scala.io.StdIn.readLine()

    val timerOverallNs = System.nanoTime()

    val unsafeRefl = classOf[Unsafe].getDeclaredField("theUnsafe")

    unsafeRefl.setAccessible(true)

    val unsafe = unsafeRefl.get(null).asInstanceOf[Unsafe]

    IntArrayUnsafe.init(unsafe)

    LongArrayUnsafe.init(unsafe)

    FloatArrayUnsafe.init(unsafe)

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

          if (!(arg == "-1" || arg.forall(_.isDigit))) {

            stomp(-1, "Positive number or -1 expected after -n")

            argsList

          } else {

            val argT = if (arg == "0") Int.MaxValue.toString else arg // note: this is different from -n 0 like in Clingo, because DelSAT doesn't do enumeration but sampling

            nextArg(argsList ++ Map('n -> List(argT)), tail)

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

    log("Arguments in delSAT: " + parsedArgs)

    val parsedArgsMap: mutable.HashMap[Symbol, List[String]] = mutable.HashMap[Symbol, List[String]]().++(parsedArgs.toMap)

    log("\notime args: " + timerToElapsedMs(timerOverallNs) + " ms")

    val noOfModels = parsedArgsMap.getOrElse('n, List(defaultNoOfModelsStr)).head.toInt

    val thresholdOpt: Option[Double] = parsedArgsMap.get('t).map(_.head.toDouble)

    val showaux = parsedArgsMap.contains('showaux)

    val mse = parsedArgsMap.contains('mse)

    val inputData = if (parsedArgs.exists(_._1 == 'enforceReadingFromSTDIN) || !parsedArgs.exists(_._1 == 'inputFile))
      readInputData(None, mse = mse).get // we read from STDIN
    else {

      val fileName = parsedArgsMap.get('inputFile).get.head

      val inputDataOpt: Option[InputData] = readInputData(Some(fileName), mse = mse)

      inputDataOpt.get

    }

    log("\notimer inputData: " + timerToElapsedMs(timerOverallNs) + " ms")

    val satMode = !inputData.spanningProgramAspifOrDIMACSOpt.get.startsWith("asp")

    var (sampledModelsWithSymbols: mutable.Seq[Array[Pred]], parserResult: AspifOrDIMACSPlainParserResult) =
      invokeSampler(inputData, noOfModels, thresholdOpt, showaux = showaux,
        satMode = satMode, additionalSolverArgs = additionalSolverArgs)

    if (!sampledModelsWithSymbols.isEmpty) {

      val hideAuxPreds: Int = 4 // TODO

      val sampledModelsWithSymbolsCleanedR: mutable.Seq[Array[Pred]] = if (hideAuxPreds == 4)
        sampledModelsWithSymbols.map(_.filterNot(isLatentSymbolAuxAtom(_)))
      else if (hideAuxPreds == 1) sampledModelsWithSymbols.map(_.filterNot(a => isAuxAtom(a) && !isSpanAuxAtom(a)))
      else if (hideAuxPreds == 2) sampledModelsWithSymbols.map(_.filterNot(isAuxAtom(_)))
      else if (hideAuxPreds == 3) sampledModelsWithSymbols.map(_.filterNot(isSpanAuxAtom(_)))
      else
        sampledModelsWithSymbols

      val symbolsSeq = parserResult.symbols //.toSeq

      val sampledModelsWithSymbolsCleaned: mutable.Seq[Array[Pred]] = if (!satMode) sampledModelsWithSymbolsCleanedR else
        sampledModelsWithSymbolsCleanedR.map((model: Array[Pred]) => {

          symbolsSeq.map(symbol => if (model.contains(symbol)) symbol else "-" + symbol)

        })

      if (printAnswers)
        sampledModelsWithSymbolsCleaned.zipWithIndex.foreach { case (model, index) =>
          System.out.println("Answer: " + (index + 1) + "\n" + model.mkString(" "))
        }

      System.out.println("SATISFIABLE") // this must be printed _directly_ after the list of answers (no empty line allowed in between)

    }

    val overallTimeMs = timerToElapsedMs(timerOverallNs) // doesn't include JVM startup time

    println("\nOverall time spent in DelSAT (incl parsing/pre-/post-processing): " + overallTimeMs + " ms (" + (overallTimeMs / 1000f) + " sec)")

    if (!omitSysExit0) // we need exit if jar isn't loaded dynamically into the current JVM. Otherwise, we need return
      sys.exit(0)
    else
      return

  }

}
