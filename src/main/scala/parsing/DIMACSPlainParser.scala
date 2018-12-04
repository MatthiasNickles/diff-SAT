/*
 * Parser for DIMACS-CNF in DelSAT. NOT a general-purpose DIMACS-CNF parser - for use in the DelSAT project only.
 *
 * Copyright (c) 2018 Matthias Nickles
 *
 * THIS CODE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
 *
 */

package parsing

import commandline.delSAT

import parsing.AspifPlainParser.AspifRule

import it.unimi.dsi.fastutil.ints.IntArrayList

import sharedDefs._

import sun.misc.Contended

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * @author Matthias Nickles
  */
object DIMACPlainSparser {

  def parseDIMACS(dimacs_CNF_Pr: String): AspifOrDIMACSPlainParserResult = {

    val dimacsParseTimerNs = System.nanoTime()

    val headerStartIt: Option[Eli] = "(\\A|\\n)\\s*p\\s+cnf\\s+".r.findFirstMatchIn(dimacs_CNF_Pr).map(_.start)

    if (headerStartIt.isEmpty)
      delSAT.stomp(-100)

    val headerStart: Int = headerStartIt.get

    val hStr0 = dimacs_CNF_Pr.substring(headerStart)

    val hStr = hStr0.dropWhile(!_.isDigit).trim

    val noOfVars = hStr.takeWhile(_.isDigit).toInt

    val noOfClauses = hStr.dropWhile(_.isDigit).trim.takeWhile(_.isDigit).toInt

    val headerEnd = dimacs_CNF_Pr.indexOf("\n", headerStart + 1)

    val s = /*Example: """
12 345 -5  -76 0
  -40  33 -2  1   0
8 0
 1 2 77
-234 9  0
0
    """*/ if (headerEnd == -1) "" else dimacs_CNF_Pr.substring(headerEnd)

    val symbols = (1 to noOfVars).map(_.toString).to[ArrayBuffer]

    val noOfPosAtomElis = symbols.length

    @Contended
    val clauses = Array.ofDim[Array[Int]](noOfClauses)

    val extraNogoods = ArrayBuffer[ArrayEliUnsafe]()

    @deprecated val generatedAspifRules = ArrayBuffer[AspifRule]() // for experimental blit generation

    val headTokensForExtraNogoods: mutable.Set[Int] = if (genBodyLitsFromSATClauses == 1d)
      ((-noOfVars to -1) ++ (1 to noOfVars)).to[mutable.Set]
    else if (genBodyLitsFromSATClauses > 0d)
      Seq.fill((noOfVars.toDouble * genBodyLitsFromSATClauses).toInt)({

        val rvar = rngGlobal.nextInt(noOfVars) + 1

        if (rngGlobal.nextBoolean())
          rvar
        else
          -rvar

      }).to[mutable.HashSet]
    else
      mutable.HashSet[Int]()

    val minClauseLengthForExtraNogoods = 0

    var noOfBlits = 0 // unfortunately we need to determine this value before we can start generating nogoods

    val directClauseNogoods = Array.ofDim[ArrayEliUnsafe](noOfClauses) // for debugging purposes only

    var clauseInc = 0

    delSAT.log("dimacsParseTimerNs 0: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    val llc = new IntArrayList(128)

    var i = 0

    val sl = s.length

    while (i < sl && (s(i) <= ' '))
      i += 1

    var index = i

    @inline def negateEliWithoutBlis(eli: Eli): Eli = if (eli < noOfPosAtomElis)
      eli + noOfPosAtomElis
    else
      eli - noOfPosAtomElis

    while (i < sl) {

      while (i < sl && s(i) > ' ')
        i += 1

      var intVal = 0

      var mult = if (s(index) == '-') {

        index += 1

        -1

      } else 1

      var il = i

      do {

        il -= 1

        intVal += (s(il) - '0') * mult

        mult *= 10

      } while (il > index)

      if (intVal == 0) {

        if (genBodyLitsFromSATClauses > 0d || delSAT.enforceSanityChecks) {

          clauses(clauseInc) = llc.toIntArray

          lazy val noOfHeadsForPseudoRule = clauses(clauseInc).count(headTokensForExtraNogoods.contains(_))

          if (genBodyLitsFromSATClauses > 0d && clauses(clauseInc).length >= minClauseLengthForExtraNogoods &&
            noOfHeadsForPseudoRule > 0)
            noOfBlits += noOfHeadsForPseudoRule

        }

        if (genBodyLitsFromSATClauses == 0d) { // this branch works only if there are not blits:

          directClauseNogoods(clauseInc) = new ArrayEliUnsafe(llc.size())

          var i = 0

          while (i < llc.size) {

            val token = llc.getInt(i)

            directClauseNogoods(clauseInc).update(i, if (token < 0) (-token) - 1 else negateEliWithoutBlis(token - 1))

            i += 1

          }

        }

        clauseInc += 1

        llc.clear()

      } else
        llc.add(intVal)

      while (i < sl && (s(i) <= ' '))
        i += 1

      index = i

    }

    if (genBodyLitsFromSATClauses > 0d) { // in case we generate body literals (blits, experimental) we need a second pass:

      val posNegEliBoundary = noOfPosAtomElis + noOfBlits

      @inline def isPosEli(eli: Eli) = eli < posNegEliBoundary

      @inline def negateEli(eli: Eli): Eli = if (isPosEli(eli))
        eli + posNegEliBoundary
      else
        eli - posNegEliBoundary

      @inline def tokenToEli(intVal: Int): Eli = if (intVal < 0) negateEli((-intVal) - 1) else intVal - 1

      @inline def tokenToNegEli(intVal: Int): Eli = if (intVal < 0) (-intVal) - 1 else negateEli(intVal - 1)

      var currentBlit = noOfPosAtomElis

      i = 0

      while (i < clauseInc) {

        val clauseWithElis = clauses(i).map(tokenToNegEli(_))

        directClauseNogoods(i) = new ArrayEliUnsafe(clauseWithElis)

        if (clauseWithElis.length >= minClauseLengthForExtraNogoods) { // experimentally and optionally (inactive by default), we generate further nogoods
          // (besides the directClauseNogoods) which define or contain body literals. For
          // approach to nogoods with body literals see Gebser et al: Conflict-Driven Answer Set Solving (and also see
          // analogous code in Preparation.scala for nogood generation from real (ASP) rules)

          val headTokensForPseudoRules = clauses(i).filter(headTokensForExtraNogoods.contains(_))

          headTokensForPseudoRules.map(headToken => {

            val headEli: Eli = tokenToEli(headToken)

            val bodyElisNegated: Array[Eli] = clauses(i).filterNot(_ == headEli).map(token => negateEli(tokenToEli(token)))

            val blitEli = currentBlit

            currentBlit += 1

            // we firstly generate nogoods which define the blit (\Delta(ß))

            val bigDeltaBeta = bodyElisNegated.map(bodyEli => new ArrayEliUnsafe(Array(blitEli, negateEli(bodyEli))))

            val deltaBeta = new ArrayEliUnsafe(bodyElisNegated.:+(negateEli(blitEli)))

            extraNogoods ++= bigDeltaBeta

            extraNogoods += deltaBeta

            extraNogoods += new ArrayEliUnsafe(Array(negateEli(headEli), blitEli))

          })

        }

        i += 1

      }

      assert(currentBlit - noOfPosAtomElis == noOfBlits)

    }

    assert(noOfClauses == directClauseNogoods.length)

    assert(noOfClauses == clauses.length)

    if (delSAT.verbose)
      println("Parsing time: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    {

      if (extraNogoods.isEmpty)
        AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
          rulesOrClauseNogoods = Right(directClauseNogoods),
          noOfPosBlits = noOfBlits,
          externalAtomElis = Seq() /*TODO*/ ,
          directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
          clauseTokensOpt = if (delSAT.enforceSanityChecks) Some(clauses) else None /* we retain these just for debugging (cross-check) purposes */)
      else {

        if (delSAT.verbose)
          println("#extra nogoods with blits generated: " + extraNogoods.length)

        val fullClauseNogoods = if (genBodyLitsFromSATClauses == 1d) extraNogoods.toArray else (extraNogoods ++ directClauseNogoods).toArray

        AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
          rulesOrClauseNogoods = Right(fullClauseNogoods),
          noOfPosBlits = noOfBlits,
          externalAtomElis = Seq() /*TODO*/ ,
          directClauseNogoodsOpt = Some(fullClauseNogoods.clone() /*otherwise this would get modified in-place*/),
          clauseTokensOpt = if (delSAT.enforceSanityChecks) Some(clauses) else None /*we retain these just for debugging (cross-check) purposes*/)

      }

    } /*else { // the following approach to combine clause nogoods with synthetic ASP rules is supported by Preparation.scala
     // but not currently used:

      val (rules, noOfPosBlits, _) = aspifRulesToEliRules(symbols.toArray, generatedAspifRules, aspifEliToSymbolOpt = None)

      if (delSAT.verbose)
        println("Generated " + rules.length + " additional rules with " + noOfPosBlits + " blits")

      AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
        rulesOrClauseNogoods = Left(rules),
        noOfPosBlits = noOfPosBlits,
        externalAtomElis = Seq() /*TODO*/ ,
        directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
        clauseTokensOpt = Some(clauses) /* we retain these just for debugging (cross-check) purposes */)

    } */

  }

}
