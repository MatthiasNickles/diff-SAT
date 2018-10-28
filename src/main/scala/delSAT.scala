/**
  * DelSAT
  *
  * A tool for differentiable satisfiability and differentiable answer set programming
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  */

package commandline


import java.io._
import java.util

import aspIOutils._

import com.accelad.math.nilgiri.{DoubleReal, autodiff}
import com.accelad.math.nilgiri.autodiff.{Constant, DifferentialFunction}
import diff.UncertainAtomsSeprt
import org.scijava.parse.ExpressionParser
import parsing.{AspifPlainParser, DIMACPlainSparser}

import sharedDefs._
import solving.{Preparation, SolverMulti}

import sun.misc.Unsafe
import utils.{IntArrayUnsafe, LongArrayUnsafe}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * @author Matthias Nickles
  *
  */
object delSAT {

  val debug = false // before using with, e.g., prasp2, build artifact delSAT.jar and check settings in StochasticCDCL_ASP_SAT.CDCLConfig etc.

  val showProgressStats = false

  val printAnswers = true

  val noOfBenchmarkTrials = 1

  val enforceChecks = false && noOfBenchmarkTrials == 1

  assert(!(printAnswers && enforceChecks))

  val version = "0.1"

  val name = "DelSAT"

  val nameAndVersion = name + " " + version

  val copyrightAndversionText = nameAndVersion + "\nCopyright (c) 2018 Matthias Nickles\n\n"

  val defaultNoOfModelsStr = "-1"

  val helpText = copyrightAndversionText +
    """
     A SAT and ASP solver for sampling-based multi-model optimization.

     Usage:

     delSAT [--version|-v] [--help|-h] [-n <n>] [-t <t>] [-ci] [<filename>]

     Reads from a file or STDIN input programs or clauses in simplified aspif or
     DIMACS-CNF format or extended aspif or DIMACS-CNF with list of parameter
     atoms and cost function(s).
     Input is obtained from STDIN if no file name is provided or if flag -ci is specified.

     Example calls:

     delSAT sat1.dimacs
     delSAT myprog.aspif_cost

     Optional arguments:

     -n <n> lets the sampler invokeSampler <n> (not necessarily different) models such
     that the specified or default threshold is reached. If -n is missing, sampling
     continues until the minimum multiset of models has been generated st. the specified
     or default threshold (or timeout) is reached. Models are either stable models
     (answer sets) or satisfying Boolean assignments (in case the input is in (extended
     or plain) DIMACS format). Use case of -n is primarly increase of entropy with
     larger number of models.

     -t <threshold> specifies the error threshold for the total cost function (small
     threshold means higher accuracy but slower sampling)

     --solverarg "argname" "value" specifies additional solver arguments (see
     sharedDefs.scala).
     Examples:
       --solverarg "partDerivComplete" "true" (activates support for certain
       non-MSE-style costs)
       --solverarg "recAssg" "true" (activates recursive unit propagation which is
       often faster for small problems)
       --solverarg "diversify" "true" (aims at generating more diverse models, might
       decrease speed.
       Note that while this might achieve some degree of uniformity, DelSAT does
       not aim to be a uniform sampling tool.)

     --showaux shows auxiliary atoms introduced for spanning formulas (omitted by
     default).

     -ci enforces reading from STDIN.

     --version|-v prints version and license information, then exits.

     --help|-h prints this information and exits.
"""

  object MessageTypes extends Enumeration {

    type MessageType = Value

    val INFO, WARNING, ERROR = Value

  }

  import MessageTypes._

  val stompMessages = Map(

    -1 -> ("Invalid command line argument", ERROR),

    -2 -> ("File error", ERROR),

    -3 -> ("External program call failed", ERROR),

    -4 -> ("I/O error", ERROR),

    -100 -> ("Invalid input data", ERROR),

    -101 -> ("Timeout or maximum number of trials exceeded. Sampling aborted", WARNING),

    -102 -> ("Unsuppored line in aspif input", ERROR),

    -103 -> ("Weighted atoms only supported via cost functions", ERROR),

    -5000 -> ("Specified local greedy decision policy won't work as expected since some measured atoms are not parameter atoms", WARNING),

    -5001 -> ("Lists of parameter or measured atoms found both separately given and within DIMACS-CNF-PR - using only the former lists.", WARNING),

    -5002 -> ("assureIsTight=true; This will lead to non-termination or wrong results if the ASP program isn't tight.", WARNING),

    -5003 -> ("partDerivComplete=true ignored because numDiffActive=true", WARNING),

    -5004 -> ("useCostBacktracking and localGreedyWithBacktracking are both disabled with numDiffActive\n => no cost minimization", WARNING),

    -5005 -> ("Undefined predicate", WARNING)


  )

  def stomp(code: Int, additionalInfo: String = "") = {

    val message = stompMessages(code)

    if (message._2 == ERROR) {

      System.err.println("\nError: " + message._1 + " " + additionalInfo)

      sys.exit(code)

    } else if (message._2 == WARNING)
      System.out.println("Warning: " + message._1 + " " + additionalInfo)
    else
      System.out.println("Info: " + message._1 + " " + additionalInfo)

  }

  @inline def log(debugMessage: => Any): Unit = {

    if (debug)
      System.out.println(debugMessage.toString)

  }

  @inline def parseDouble(s: String): Option[Double] = {

    val r = try {

      Some(s.toDouble)

    } catch {

      case _: NumberFormatException => None

    }

    r

  }

  final case class InputData(spanningProgramAspifOrDIMACSOpt: Option[String],
                             costsOpt: Option[UncertainAtomsSeprt]) {}

  /** Converts a postfix queue of arithmetic expression tokens (e.g. from org.scijava.parse) into a com.accelad.math.nilgiri.diff-expression, using a stack */
  def convertToDfNEW(tokensQueue: util.LinkedList[Object], measuredAtomsSeqSorted: Array[String], measuredAtomsSet: mutable.HashSet[Pred]):
  DifferentialFunction[DoubleReal] = {

    // TODO: see https://github.com/scijava/parsington/blob/master/src/test/java/org/scijava/parse/ExpressionParserTest.java

    val tokenStack = scala.collection.mutable.Stack[Object]() // can contain both autodiff. and org.scijava.parse. objects

    val dFFactory = new diff.DifferentialFunctionFactoryStasp() //null/*missing until we deserialize in nablaSAT*/)

    def popArgOpt: Option[DifferentialFunction[DoubleReal]] = {

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

        case dConst: autodiff.Variable[DoubleReal] => Some(dConst)

        case dVar: autodiff.Constant[DoubleReal] => Some(dVar)

        case x => {

          assert(false, "Error: Invalid type of argument in inner cost expression: " + x)

          None

        }

      }

    }

    def dConstFromMeasuredAtomIndex(atom: Pred) = {

      val measuredAtomIndex: Int = {

        val measuredAtomNameInExpr = atom

        val m: String = measuredAtomNameInExpr.replaceAllLiterally("ä", "_").replaceAllLiterally(".0" /*because we get a real number here*/ , "")

        util.Arrays.binarySearch(measuredAtomsSeqSorted.asInstanceOf[Array[Object]] /*Scala arrays aren't covariant*/ , m)

        // TODO: ^^ hack; check again, find cleaner solution

      }

      dFFactory.`val`(new DoubleReal(measuredAtomIndex))

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

            val dConst: Constant[DoubleReal] = dConstFromMeasuredAtomIndex(name) // a pseudo-real constant which is an index into measures atoms; these indices later need to be
            // translated into (positive atom) elis in NablaSAT.

            tokenStack.push(dConst)

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

              case (None, None) => assert(false, "Error: Insufficient arguments for operator " + operator + " in inner cost expression")

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

            }

          }

        }

        case fnTag: org.scijava.parse.Function => { // <fn> (where fn is literally "fn", not a function name)

          val nextTag = tokenStack.pop()

          nextTag match {

            case groupTag: org.scijava.parse.Group => {

              val arity = groupTag.getArity

              val dArgs: Seq[DifferentialFunction[DoubleReal]] = (1 to arity).flatMap { case _ => {

                popArgOpt

              }

              }

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

                    // at this point, we know that the "function" with its arguments is likely an atom (in form of a predicate with arguments) instead
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

                    val dConst = dConstFromMeasuredAtomIndex(measuredAtom /*dArgs(0).toString.takeWhile(_ != ':')*/)

                    tokenStack.push(dConst)

                    //assert(false, "Error: Unknown function in inner cost expression: " + eFnSymbol)

                  }

                }

                case _ => {

                  assert(false, "Error: Invalid inner cost expression, parsing error (1)")

                }

              }

            }

            case _ => assert(false, "Error: Invalid inner cost expression, parsing error (2)")

          }

        }

        case groupTag: org.scijava.parse.Group => { // "(number of things in brackets)", e.g. (but not only), arguments of a subsequent function tag <fn>

          if (tokens(index + 1).toString == "<Fn>")
            tokenStack.push(groupTag)
          else if (groupTag.getArity != 1)
            assert(false, "Error: Syntax error in inner cost expression")

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

        assert(false, "Error: Invalid inner cost expression")

        null

      }

    }

  }

  /**
    * Reads input from file (if file name is given) or STDIN (in various alternative formats, with input typically generated by prasp2)
    */
  def readInputData(fileNameOpt: Option[String]): Option[InputData] = {

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

        val r: String = new String(Files.readAllBytes(Paths.get(fileName)), StandardCharsets.UTF_8)

        log("Time file slurp: " + (System.nanoTime() - timer) / 1000000 + "ms")

        r

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

        val paramAtomsAndInnerCostsLines: Iterator[String] = paramAtomsAndInnerCostsStr.lines

        val parameterAtomsSeq: Array[Pred] = paramAtomsAndInnerCostsLines.take(1).mkString.trim.split("\\s+").drop(1).distinct

        val costLines = paramAtomsAndInnerCostsLines.filter(_.startsWith("cost ")).map(_.stripPrefix("cost ").trim).toList

        // we obtain the measured atoms from the cost function expressions (whereas "pats ..." is the list of parameter atoms):

        // val measuredAtomPattern = """(?<!\w)f\(([^()]*)\)""".r

        val measuredAtomsSet: mutable.HashSet[Pred] = mutable.HashSet[Pred]() ++ costLines.foldLeft(ArrayBuffer[Pred]()) {

          case (ms: ArrayBuffer[Pred], costLine: String) => {

            //ms ++ measuredAtomPattern.findAllIn(costLine).matchData.map(_.group(1))

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

                  assert(i < costLine.length, "Error: invalid cost function expression: " + costLine)

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

            val underscoreReplInner = innerCostFunStr.replaceAllLiterally("_", "ä") // ExpressionParser only recognizes Java-style identifiers
            // with unicode characters but without leading underscores

            val postfixTokens = new ExpressionParser().parsePostfix(underscoreReplInner)

            val dfInnerCostExpression = convertToDfNEW(postfixTokens, measuredAtomsSeqSorted, measuredAtomsSet)

            dfInnerCostExpression

          }).toArray

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

    println("DelSAT " + commandline.delSAT.version + "\n")

    val timerInitNs = System.nanoTime()

    assert(inputData.spanningProgramAspifOrDIMACSOpt.isDefined)

    overrideSolverArgs(additionalSolverArgs)

    val aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult = if (!satMode)
      AspifPlainParser.parseAspif(inputData.spanningProgramAspifOrDIMACSOpt.get, shiftAndUnfoldForDisjunctions = true, noOfUnfolds = 0)
    else
      DIMACPlainSparser.parseDIMACS(inputData.spanningProgramAspifOrDIMACSOpt.get, generatePseudoRulesForNogoods = generatePseudoRulesForNogoodsForSATMode)

    log("inittimer after Parse: " + (System.nanoTime() - timerInitNs) / 1000000 + " ms")

    val prep: Preparation = new solving.Preparation(aspifOrDIMACSParserResult, inputData.costsOpt, satMode = satMode,
      omitAtomNogoods = false /*aspifOrDIMACSParserResult.directClauseNogoodsOpt.isDefined*/)

    log("inittimer after Preparation: " + (System.nanoTime() - timerInitNs) / 1000000 + " ms")

    var res = mutable.Seq[Array[Pred]]()

    val trialDurations = (1 to noOfBenchmarkTrials).map(trial => {

      println("Solving... (trial " + trial + ")")

      val startTrialTimeNs = System.nanoTime()

      val solver = new SolverMulti(prep)

      res = solver.sampleMulti(inputData.costsOpt, requestedNoOfModelsBelowThresholdOrAuto = noOfModels, satMode = satMode, prep = prep,
        requestedNumberOfModels = noOfModels, threshold = thresholdOpt.getOrElse(0.001d), maxIt = 100000)

      System.nanoTime() - startTrialTimeNs

    })

    val avgDuration = ((trialDurations.sum.toDouble / noOfBenchmarkTrials.toDouble) / 1000000).toInt

    if (noOfBenchmarkTrials > 1) /*println("\nOverall duration solving and sampling: " + avgDuration + " ms\n") else*/
      println("\n@@@@@@@@ Average overall duration solver.sampleMulti: " + avgDuration + " ms\n")

    (res, aspifOrDIMACSParserResult)

  }

  def main(args: Array[String]): Unit = {

    //scala.io.StdIn.readLine()

    val timerOverallNs = System.nanoTime()

    val unsafeRefl = classOf[Unsafe].getDeclaredField("theUnsafe")

    unsafeRefl.setAccessible(true)

    IntArrayUnsafe.UNSAFE = unsafeRefl.get(null).asInstanceOf[Unsafe]

    LongArrayUnsafe.UNSAFE = IntArrayUnsafe.UNSAFE

    IntArrayUnsafe.init()

    LongArrayUnsafe.init()

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

        case ("--version" | "-v") :: tail => {

          println(copyrightAndversionText)

          sys.exit(0)

        }

        case ("--help" | "-h") :: tail => {

          println(copyrightAndversionText + "\n\n" + helpText)

          sys.exit(0)

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

    log("\notime args: " + (System.nanoTime() - timerOverallNs) / 1000000 + " ms")

    val noOfModels = parsedArgsMap.getOrElse('n, List(defaultNoOfModelsStr)).head.toInt

    val thresholdOpt: Option[Double] = parsedArgsMap.get('t).map(_.head.toDouble)

    //val sampleConfOverrideJsonStrOpt: Option[String] = parsedArgsMap.get('samplconf).map(_.head)

    val showaux = parsedArgsMap.get('showaux).isDefined

    val inputData = if (parsedArgs.exists(_._1 == 'enforceReadingFromSTDIN) || !parsedArgs.exists(_._1 == 'inputFile))
      readInputData(None).get // we read from STDIN
    else {

      val fileName = parsedArgsMap.get('inputFile).get.head

      val inputDataOpt: Option[InputData] = readInputData(Some(fileName))

      inputDataOpt.get

    }

    log("\notimer inputData: " + (System.nanoTime() - timerOverallNs) / 1000000 + " ms")

    val satMode = !inputData.spanningProgramAspifOrDIMACSOpt.get.startsWith("asp")

    var (sampledModelsWithSymbols: mutable.Seq[Array[Pred]], parserResult: AspifOrDIMACSPlainParserResult) =
      invokeSampler(inputData, noOfModels, thresholdOpt, showaux = showaux,
        satMode = satMode, additionalSolverArgs = additionalSolverArgs)

    if(!sampledModelsWithSymbols.isEmpty) {

      val hideAuxPreds: Int = 4 // TODO

      val sampledModelsWithSymbolsCleanedR: mutable.Seq[Array[Pred]] = if (hideAuxPreds == 4)
        sampledModelsWithSymbols.map(_.filterNot(isLatentSymbolAuxAtom(_)))
      else if (hideAuxPreds == 1) sampledModelsWithSymbols.map(_.filterNot(a => isAuxAtom(a) && !isSpanAuxAtom(a)))
      else if (hideAuxPreds == 2) sampledModelsWithSymbols.map(_.filterNot(isAuxAtom(_)))
      else if (hideAuxPreds == 3) sampledModelsWithSymbols.map(_.filterNot(isSpanAuxAtom(_)))
      else
        sampledModelsWithSymbols

      val symbolsSeq = parserResult.symbols.toSeq

      val sampledModelsWithSymbolsCleaned: mutable.Seq[Array[Pred]] = if (!satMode) sampledModelsWithSymbolsCleanedR else
        sampledModelsWithSymbolsCleanedR.map((model: Array[Pred]) => {

          symbolsSeq.map(symbol => if (model.contains(symbol)) symbol else "-" + symbol).toArray

        })

      if (printAnswers)
        sampledModelsWithSymbolsCleaned.zipWithIndex.foreach { case (model, index) =>
          System.out.println("Answer: " + (index + 1) + "\n" + model.mkString(" ") /*+ (if(satMode) " 0" else "")*/)
        }

      System.out.println("\nSATISFIABLE")  // this MUST be printed directly after the list of answers!

    }

    println("\nOverall time incl parsing/pre-/post-processing: " + (System.nanoTime() - timerOverallNs) / 1000000 + " ms")

    if (!omitSysExit0)  // we need exit if jar isn't loaded dynamically into the current JVM. Otherwise, we need return
      sys.exit(0)
    else
      return

  }

}
