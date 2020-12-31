/**
  * diff-SAT
  *
  * Copyright (c) 2018,2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package input

import java.io.PrintWriter
import java.util

import aspIOutils.Pred

import com.accelad.math.nilgiri.{DoubleReal, autodiff}
import com.accelad.math.nilgiri.autodiff.{DifferentialFunction, Variable}

import diffSAT.{stomp}

import diff.UncertainAtomsSeprt

import org.scijava.parse.ExpressionParser

import sharedDefs._
import utils.Various._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object ParseOptimizationTerms {

  @inline def generateMeasuredAtomVariableInCost(weightedAtomStr: String, dFFactory: diff.DifferentialFunctionFactoryStasp,
                                                 aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult,
                                                 eliToVariableInCostFunctions: mutable.HashMap[Int, Variable[DoubleReal]]): Variable[DoubleReal] = {

    val eli = aspifOrDIMACSParserResult.symbolToEliOpt.map(_ (weightedAtomStr)).getOrElse(weightedAtomStr.toInt /*- 1*/)

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

        case dArg: DifferentialFunction[DoubleReal]@unchecked => Some(dArg)

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
                  else if (fnName == "subtr") // we need this because the diff-SAT caller might use prefix notation instead of operators +,-,*,/ etc
                  tokenStack.push(dArgs(1).minus(dArgs(0)))
                    else if (fnName == "add") // we need this because the diff-SAT caller might use prefix notation instead of operators +,-,*,/ etc
                  tokenStack.push(dArgs(1).plus(dArgs(0)))
                    else if (fnName == "mult") // we need this because the diff-SAT caller might use prefix notation instead of operators +,-,*,/ etc
                  tokenStack.push(dArgs(1).mul(dArgs(0)))
                    else if (fnName == "div") // we need this because the diff-SAT caller might use prefix notation instead of operators +,-,*,/ etc
                  tokenStack.push(dArgs(1).div(dArgs(0)))
                    else if (fnName == "pow") // we need this because the diff-SAT caller might use prefix notation instead of operators +,-,*,/ etc
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

      case dF: DifferentialFunction[DoubleReal]@unchecked => dF

      case _ => {

        stomp(-202)

        null

      }

    }

  }


  def parseOptimizationTerms(mse: Boolean, paramAtomsAndInnerCostsStrOpt: Option[String],
                             satMode: Boolean, aspifOrDIMACSParserResult: AspifOrDIMACSPlainParserResult): (InputData, Boolean) = {

    def parseTermToPostfixTokens(innerCostFunStr: Pred): util.LinkedList[Object] = {

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

    val timerInputBNs = System.nanoTime()

    lazy val symbolsSet: Set[Pred] = aspifOrDIMACSParserResult.symbols.toSet

    if (showIntermediateTimers)
      println("\notimer timerInputBNs: " + timerToElapsedMs(timerInputBNs) + " ms")

    val paramAtomsAndInnerCostsStr = paramAtomsAndInnerCostsStrOpt.getOrElse("")

    /*;;;*/ val paramAtomsAndInnerCostsLines: Array[String] = if (paramAtomsAndInnerCostsStrOpt.isDefined) paramAtomsAndInnerCostsStr.split("\\R")/*.lines*/ else Array[String]()

    val parameterAtomsSeq: Array[Pred] = (paramAtomsAndInnerCostsLines.take(1).mkString.trim.split("\\s+").drop(1) ++
      aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._1).distinct.filter(pa => { // TODO: optimize

      val r = symbolsSet.contains(pa)

      if (!r)
        stomp(-204, pa)

      r

    })

    val eliToVariableInCostFunctions = mutable.HashMap[Nogi, Variable[DoubleReal]]()

    val costLinesLocal: ArrayBuffer[String] = paramAtomsAndInnerCostsLines.filter(_.trim.startsWith("cost ")).to(ArrayBuffer)

    val costLines: ArrayBuffer[String] = costLinesLocal.map(_.trim.stripPrefix("cost ").replaceAllLiterally(" ", "")) ++
      aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._2

    val evalLines = aspifOrDIMACSParserResult.additionalUncertainAtomsInnerCostsStrs._3 // from _eval_("term","?") facts. ASP mode only.

    // (Remark: we can also process deprecated .opt files produced by prasp2 which contain [?] query lines, simply by
    // ignoring these lines.)

    // We now obtain the measured atoms from the cost function expressions. Note that not all measured atoms are necessarily also
    // parameter atoms (pats), the two sets can even be disjoint.

    // NB: in satMode, we require that each propositional variable in cost expressions (but not in the CNF clauses) is prefixed by letter "v". We keep this prefix only
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

    if (!hypothesisParamAtoms.isEmpty && sharedDefs.autoGenerateCostLinesForHypotheses) { // deprecated

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

    if (showIntermediateTimers)
      println("\notimer timerInputBNs A: " + timerToElapsedMs(timerInputBNs) + " ms")

    val innerCostExpressionInstancesPerUncertainAtom: Array[DifferentialFunction[DoubleReal]] = {

      costLines.toArray.map(costLine => {

        val innerCostFunStr = costLine.stripPrefix("cost ").trim

        if (!mse) {

          val postfixTokens: util.LinkedList[Object] = parseTermToPostfixTokens(innerCostFunStr)

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

        val postfixTokens: util.LinkedList[Object] = parseTermToPostfixTokens(evalTermStr)

        val dfEvalExpression = convertToDfNEW(postfixTokens, measuredAtomsSet, aspifOrDIMACSParserResult, eliToVariableInCostFunctions, satMode = satMode)

        (evalTermStr, dfEvalExpression)

      }).toMap

    }

    if (showIntermediateTimers)
      println("\notimer timerInputBNs B: " + timerToElapsedMs(timerInputBNs) + " ms")

    (InputData(aspifOrDIMACSParserResult,
      Some(new UncertainAtomsSeprt(parameterAtomsSeq, measuredAtomsSeq,
        innerCostExpressionInstancesPerUncertainAtom, eliToVariableInCostFunctions, evalExpressionToFct))), satMode)

  }

}
