/*
 * Parser for a subset of the DIMACS-CNF format.
 *
 * Not a general-purpose DIMACS-CNF parser - for internal use in the DelSAT project only.
 *
 * Copyright (c) 2018 Matthias Nickles
 *
 * THIS CODE IS PROVIDED WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
 *
 */

package parsing

import commandline.delSAT
import parsing.AspifPlainParser.{AspifRule, aspifRulesToEliRules}

import aspIOutils._

import sharedDefs._

import scala.collection.mutable.ArrayBuffer

object DIMACPlainSparser {

  // Remark: sometimes, "DIMACS-CNF" includes extra \n's with 0 in separate lines. Preprocess by replacing regex "(?<!\ )\n" with "" (empty string).

  def parseDIMACS(dimacs_CNF_Pr: String, generatePseudoRulesForNogoods: Boolean): AspifOrDIMACSPlainParserResult = {

    val dimacsLinesStripped: Array[String] = dimacs_CNF_Pr.split("\\r?\\n").filterNot(_.startsWith("c")) /*.distinct*/ .map(_.trim)

    val hStr = dimacsLinesStripped(0).stripPrefix("p cnf ").trim

    val noOfVars = hStr.takeWhile(_.isDigit).toInt

    val noOfClauses = hStr.reverse.takeWhile(_.isDigit).reverse.toInt

    val symbols = (1 to noOfVars).map(_.toString).to[ArrayBuffer]

    val noOfPosAtomElis = symbols.length

    val noOfBodyExtraNogoods = Int.MaxValue //50000

    var rmNoOfBodyExtraNogoods = noOfBodyExtraNogoods

    val newFalseAspifElisBoundaryForDIMACS = noOfPosAtomElis + 1

    val generatedAspifRules = ArrayBuffer[AspifRule]()

    val clauseTokensStr = ArrayBuffer[ArrayBuffer[String]](ArrayBuffer[String]())

    dimacsLinesStripped.tail.foreach(line => {

      val tokensLocal: Array[String] = splitByRepChar(line)

      if (line.startsWith("."))
        delSAT.stomp(-103)

      clauseTokensStr.last.appendAll(tokensLocal)  // we use this iterative foldLeft-emulation because clauses can range over multiple lines

      if (tokensLocal.last == "0") {

        clauseTokensStr.append(ArrayBuffer[String]())

      }

    })

    val clauseTokens = clauseTokensStr.dropRight(1).map(ct => {

      assert(ct.last == "0", "Error: unsupported syntax in DIMACS input: " + ct.mkString(" "))

      val clauseNumTokens: Array[Int] = {

        try {
          ct.map(_.toInt)
        } catch {

          case e => {

            println("Error: " + e + "\n" + ct.map(t => "\"" + t + "\"").mkString(","))

            sys.exit(-1)

          }

            ArrayBuffer[Int]()

        }

      }.dropRight(1).toArray

      if (generatePseudoRulesForNogoods && clauseNumTokens.length > 1) {

        // we "fake2 aspif rules, so that we can later generate body nogoods from it.

        val headAspifElis = clauseNumTokens //.filter(_ > 0)

        headAspifElis.foreach(headAspifEli => {

          if (rngGlobal.nextFloat() <= 1f) { // NB: if < 1f, we'd need to disable generation of { head, Fblit1, Fblit2, ...} nogoods

            val (bodyPosAspifElis, bodyNegAspifElis) = clauseNumTokens.filterNot(_ == headAspifEli).map(-_).partition(_ >= 0)

            val aspifRule = AspifRule(headPosAtomsAspifElis = if (headAspifEli > 0) Set(headAspifEli) else Set(),
              headNegAtomsAspifElis = if (headAspifEli < 0) Set(headAspifEli) else Set(),
              bodyPosAtomsAspifElis = bodyPosAspifElis.toSet,
              bodyNegAtomsAspifElis = bodyNegAspifElis.toSet)

            //println("Aspif pseudo-rule for body nogood generation: " + aspifRule.toString)

            generatedAspifRules.append(aspifRule)

          }

        })

      }

      clauseNumTokens

    }).toArray

    assert(clauseTokens.length == noOfClauses, "Error: Invalid input (number of clauses does not match declared number of clauses)")

    val noOfBlits = generatedAspifRules.groupBy(rule => (rule.bodyPosAtomsAspifElis, rule.bodyNegAtomsAspifElis)).keys.size // only different bodies get their own blit

    val posNegEliBoundary = noOfPosAtomElis + noOfBlits

    @inline def isPosEli(eli: Eli) = eli < posNegEliBoundary

    @inline def negateEli(eli: Eli): Eli = {

      if (isPosEli(eli))
        eli + posNegEliBoundary
      else
        eli - posNegEliBoundary

    }

    @inline def varToEli(v: Int) = if (v < 0) negateEli(-v - 1) else v - 1

    val directClauseNogoods: ArrayBuffer[Array[Eli]] = clauseTokens.map(clauseNumTokens => {

      // We translate clauses directly into nogoods...

      val nogoodPosAtomsElis: Array[Eli] = clauseNumTokens.filter(_ < 0).map(negVariable => (-negVariable) - 1)

      val nogoodNegAtomsElis: Array[Eli] = clauseNumTokens.filter(_ > 0).map(posVariable => negateEli(posVariable - 1))

      nogoodPosAtomsElis ++ nogoodNegAtomsElis

    }).to[ArrayBuffer]

    assert(noOfClauses == directClauseNogoods.length)

    if (!generatePseudoRulesForNogoods)
      AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
        rulesOrClauseNogoods = Right(/*if (generatePseudoRulesForNogoodsForSATMode)bodyNogoods ++ directClauseNogoods else*/ directClauseNogoods),
        noOfPosBlits = 0 /*noOfPosBlits*/ , externalAtomElis = Seq(), directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
        clauseTokensOpt = Some(clauseTokens) /*we retain these just for debugging (cross-check) purposes*/)
    else {

      val (rules, noOfPosBlits, emptyBodyBlit) = aspifRulesToEliRules(symbols.toArray, generatedAspifRules, aspifEliToSymbolOpt = None)

      AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
        rulesOrClauseNogoods = Left(rules),
        noOfPosBlits = noOfPosBlits, externalAtomElis = Seq(), directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
        clauseTokensOpt = Some(clauseTokens) /*we retain these just for debugging (cross-check) purposes*/)

    }

  }

}
