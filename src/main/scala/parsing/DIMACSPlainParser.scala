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

package parsing

import aspIOutils.Pred
import commandlineDelSAT.delSAT
import it.unimi.dsi.fastutil.ints.IntArrayList
import sharedDefs._
import utils.IntArrayUnsafeS

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * Parser for DIMACS-CNF and PCNF (probabilistic CNF). Not a general-purpose DIMACS-CNF parser - designed for use within delSAT only. Work in progress.
  *
  * @author Matthias Nickles
  *
  */
object DIMACPlainSparser {

  def parseDIMACS(dimacs_CNF_Pr: String): AspifOrDIMACSPlainParserResult = {

    val dimacsParseTimerNs = System.nanoTime()

    val headerStartIt: Option[Eli] = "(\\A|\\n)\\s*p\\s+p?cnf\\s+".r.findFirstMatchIn(dimacs_CNF_Pr).map(_.start)

    if (headerStartIt.isEmpty)
      delSAT.stomp(-100)

    val headerStart: Int = headerStartIt.get

    val hStr0 = dimacs_CNF_Pr.substring(headerStart)

    val hStr = hStr0.dropWhile(!_.isDigit).trim

    val probabilisticCNF = hStr0.contains("pcnf")

    val noOfVarsR = hStr.takeWhile(_.isDigit).toInt

    var noOfVars = noOfVarsR // TODO: we might simplify some operation if we would use next2Pow(noOfVarsR) or next2Pow(noOfVarsR * 2) / 2, but
    // this would not necessarily be faster.

    var noOfClauses = hStr.dropWhile(_.isDigit).trim.takeWhile(_.isDigit).toInt // not considering yet probabilistic clauses as these will be replaced by extra clauses

    val headerEnd = dimacs_CNF_Pr.indexOf("\n", headerStart + 1)

    val genBodyLitsFromSATClauses: Double = 0d // TODO; must leave 0d for now. Experimentally generates pseudo-"body literals" (blits) in SAT mode, for x% of all
    // variables. If 1d, we completely replace the original clause nogoods with an equivalent theory using blits.
    // Can easily blow up space.

    var s = if (headerEnd == -1) "" else dimacs_CNF_Pr.substring(headerEnd)

    var i = 0

    var sl = s.length

    val llc = new IntArrayList(1024)

    @inline def skipSpaceAndComment = {

      while (i < sl && (s(i) <= ' '))
        i += 1

      while (i < sl && s(i) == 'c') { // skip comment

        while (i < sl && s(i) != '\r' && s(i) != '\n')
          i += 1

        while (i < sl && (s(i) <= ' '))
          i += 1

      }

    }

    val extraClausesFromProbClauses = ArrayBuffer[IntArrayList]() // generated clauses from desugared probabilistically weighted clauses.
    // Observe that these extra clauses replace the weighted clauses.

    val patsFromProbabilisticClauses = ArrayBuffer[Pred]()

    val costsFromProbabilisticClauses = ArrayBuffer[String]()  // format cost (probability-f(vx))^2

    if (probabilisticCNF) { // first pass desugars any probabilistic clauses ------------------------------------------

      assert(genBodyLitsFromSATClauses == 0d)

      // we need to amend s (removal of weighted clauses), noOfClauses, noOfVars.
      // Later, add nogoods from generated clauses and add generated clauses to directClauseNogoods. Also, _pat_ and _cost_.

      skipSpaceAndComment

      var index = i

      var isWeightedClause = false

      var weight = ""

      while (i < sl) {

        var isWeight = false

        while (i < sl && s(i) > ' ') {

          if (s(i) == '.')
            isWeight = true

          i += 1

        }

        var intVal = 0

        if (isWeight) {

          isWeightedClause = true

          weight = s.substring(index, i)

          if(weight(0) == '.')
            weight = "0" + weight  // (otherwise the resulting cost function couldn't be parsed)

        } else {

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

        }

        if (intVal == 0 && !isWeight) { // end of clause

          if (isWeightedClause) {

            noOfVars += 1

            val clauseHandleVar = noOfVars

            patsFromProbabilisticClauses.append(noOfVars.toString)

            costsFromProbabilisticClauses.append("(" + weight + "-f(v" + noOfVars + "))^2")

            val extraClauseA = llc.clone  // first value is 0 (the intValue 0 which was added instead of the weight)

            extraClauseA.set(0, -clauseHandleVar)

            val extraClausesB = Array.ofDim[IntArrayList](llc.size - 1)

            var k = 1

            while (k < llc.size) {

              val extraClauseB = new IntArrayList(2)

              extraClauseB.add(clauseHandleVar)

              extraClauseB.add(-llc.getInt(k))

              extraClausesB(k - 1) = extraClauseB

              k += 1

            }

            extraClausesFromProbClauses.append(extraClauseA)

            extraClausesFromProbClauses.appendAll(extraClausesB)

            noOfClauses += extraClausesB.length + 1/*extraClauseA*/ - 1/*the annotated clause*/

            isWeightedClause = false

            weight = ""

          }

          llc.clear()

        } else
          llc.add(intVal)

        skipSpaceAndComment

        index = i

      }

    } // -------------------------------------------------------------------------------------------------------------

    val symbols = (1 to noOfVars).map(_.toString).to[ArrayBuffer]

    var noOfPosAtomElis = symbols.length

    val clausesForChecks = Array.ofDim[Array[Int]](noOfClauses) // for debugging purposes and the optional blit generation only

    val extraNogoodsForBlits = ArrayBuffer[IntArrayUnsafeS]()

    val headTokensForExtraNogoods: mutable.Set[Int] /*for genBodyLitsFromSATClauses only*/ = if (genBodyLitsFromSATClauses == 1d)
      ((-noOfVars to -1) ++ (1 to noOfVars)).to[mutable.Set]
    else if (genBodyLitsFromSATClauses > 0d) { // TODO: genBodyLitsFromSATClauses > 0 not properly working yet (test e.g. with 0.5 and hanoi5)

      assert(false, "Internal error")

      Seq.fill((noOfVars.toDouble * genBodyLitsFromSATClauses).toInt)({

        val rvar = rngGlobal.nextInt(noOfVars) + 1

        if (rngGlobal.nextBoolean())
          rvar
        else
          -rvar

      }).to[mutable.HashSet]

    } else
      mutable.HashSet[Int]()

    val minClauseLengthForExtraNogoods = 0 // for genBodyLitsFromSATClauses only*

    var noOfBlits = 0 // for genBodyLitsFromSATClauses only; unfortunately we need to determine this value before we can start generating nogoods

    val directClauseNogoods = Array.ofDim[IntArrayUnsafeS](noOfClauses)

    var clauseInc = 0

    delSAT.log("dimacsParseTimerNs 0: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    i = 0

    sl = s.length

    skipSpaceAndComment

    var index = i

    @inline def negateEliWithoutBlis(eli: Eli): Eli = if (eli < noOfPosAtomElis)
      eli + noOfPosAtomElis
    else
      eli - noOfPosAtomElis

    @inline def generateClauseNogood(llc: IntArrayList, clauseNogoodIndex: Int) = {

      if(clauseInc >= noOfClauses)
        delSAT.stomp(-100, "Wrong number of clauses specified in header")

      directClauseNogoods(clauseInc) = new IntArrayUnsafeS(llc.size(), aligned = false)

      var i = 0

      while (i < llc.size) {

        val token = llc.getInt(i)

        directClauseNogoods(clauseNogoodIndex).update(i, if (token < 0) (-token) - 1 else negateEliWithoutBlis(token - 1))

        i += 1

      }

    }

    var ignoreClause = false

    // Second pass (or first pass in case there have been no weighted clauses):

    while (i < sl) {

      while (i < sl && s(i) > ' ') {

        if(s(i) == '.') {  // we are inside a weighted clause. Ignore.

          ignoreClause = true

          while(i < sl-1 && !(s(i) == '0' && s(i-1).isWhitespace && s(i+1).isWhitespace))
            i += 1

        }

        i += 1

      }

      if(!ignoreClause) {

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

        if (intVal == 0) { // end of clause

          {

            if (genBodyLitsFromSATClauses > 0d || delSAT.enforceSanityChecks) {

              clausesForChecks(clauseInc) = llc.toIntArray // we use this just for a debugging-related check after solving

              lazy val noOfHeadsForPseudoRule = clausesForChecks(clauseInc).count(headTokensForExtraNogoods.contains(_))

              if (genBodyLitsFromSATClauses > 0d && clausesForChecks(clauseInc).length >= minClauseLengthForExtraNogoods &&
                noOfHeadsForPseudoRule > 0) // TODO: genBodyLitsFromSATClauses is experimental; not fully tested yet
                noOfBlits += noOfHeadsForPseudoRule

            }

            if (genBodyLitsFromSATClauses == 0d) { // this branch works only if there aren't any blits:

              generateClauseNogood(llc = llc, clauseNogoodIndex = clauseInc)

            }

            clauseInc += 1

          }

          llc.clear()

        } else
          llc.add(intVal)

      } else
        ignoreClause = false

      skipSpaceAndComment

      index = i

    }

    extraClausesFromProbClauses.foreach((clause: IntArrayList) => {

      generateClauseNogood(llc = clause, clauseNogoodIndex = clauseInc)

      if(delSAT.enforceSanityChecks)
        clausesForChecks(clauseInc) = clause.toIntArray // we use this just for a debugging-related check after solving

      clauseInc += 1

    })

    if (!directClauseNogoods.isEmpty && directClauseNogoods.last == null)
      delSAT.stomp(-100, "Fewer than the specified number of clauses found in DIMACS file")

    if (genBodyLitsFromSATClauses > 0d) { // in case we generate body literals (blits, experimental) we need a second pass:

      assert(!probabilisticCNF)

      // TODO: genBodyLitsFromSATClauses is experimental; not fully tested yet

      val posNegEliBoundary = noOfPosAtomElis + noOfBlits // not necessarily the final boundary

      @inline def isPosEli(eli: Eli) = eli < posNegEliBoundary

      @inline def negateEli(eli: Eli): Eli = if (isPosEli(eli))
        eli + posNegEliBoundary
      else
        eli - posNegEliBoundary

      @inline def tokenToEli(intVal: Int): Eli = if (intVal < 0) negateEli((-intVal) - 1) else intVal - 1

      @inline def tokenToNegatedEli(intVal: Int): Eli = if (intVal < 0) (-intVal) - 1 else negateEli(intVal - 1)

      var currentBlit = noOfPosAtomElis

      i = 0

      while (i < clauseInc) {

        val nogood = clausesForChecks(i).map(tokenToNegatedEli(_))

        directClauseNogoods(i) = new IntArrayUnsafeS(nogood, aligned = false)

        if (nogood.length >= minClauseLengthForExtraNogoods) { // Experimentally and optionally (inactive by default), we generate further nogoods
          // (besides the directClauseNogoods) which define or contain body literals. For
          // approach to nogoods with body literals see Gebser et al: Conflict-Driven Answer Set Solving (and also see
          // analogous code in Preparation.scala for nogood generation from ASP rules)

          val headTokensForPseudoRules = clausesForChecks(i).filter(headTokensForExtraNogoods.contains(_))

          headTokensForPseudoRules.map(headToken => {

            val headEli: Eli = tokenToEli(headToken)

            val bodyElisNegated: Array[Eli] = clausesForChecks(i).filterNot(_ == headEli).map(token => negateEli(tokenToEli(token)))

            val blitEli = currentBlit

            currentBlit += 1

            // we firstly generate nogoods which define the blit (\Delta(ß))

            val bigDeltaBeta = bodyElisNegated.map(bodyEli => new IntArrayUnsafeS(Array(blitEli, negateEli(bodyEli)), aligned = false))

            val deltaBeta = new IntArrayUnsafeS(bodyElisNegated.:+(negateEli(blitEli)), aligned = false)

            extraNogoodsForBlits ++= bigDeltaBeta

            extraNogoodsForBlits += deltaBeta

            extraNogoodsForBlits += new IntArrayUnsafeS(Array(negateEli(headEli), blitEli), aligned = false)

          })

        }

        i += 1

      }

      assert(currentBlit - noOfPosAtomElis == noOfBlits)

    }

    assert(noOfClauses == directClauseNogoods.length)

    assert(noOfClauses == clausesForChecks.length)

    if (delSAT.verbose)
      println("Parsing time: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    {

      if (extraNogoodsForBlits.isEmpty)
        AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
          rulesOrClauseNogoods = Right(directClauseNogoods),
          noOfPosBlits = noOfBlits,
          externalAtomElis = Seq(),
          assumptionElis = Seq(),
          directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
          clauseTokensOpt = if (delSAT.enforceSanityChecks) Some(clausesForChecks) else None /* we retain these just for debugging (cross-check) purposes */ ,
          symbolToEliOpt = None,
          additionalUncertainAtomsInnerCostsStrs = (patsFromProbabilisticClauses.toArray, costsFromProbabilisticClauses.toArray, Array[String]()))
      else {

        if (delSAT.verbose)
          println("#extra nogoods with blits generated: " + extraNogoodsForBlits.length)

        val fullClauseNogoods = if (genBodyLitsFromSATClauses == 1d) extraNogoodsForBlits.toArray else (extraNogoodsForBlits ++ directClauseNogoods).toArray

        AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
          rulesOrClauseNogoods = Right(fullClauseNogoods),
          noOfPosBlits = noOfBlits,
          externalAtomElis = Seq(),
          assumptionElis = Seq(),
          directClauseNogoodsOpt = Some(fullClauseNogoods.clone() /*otherwise this would get modified in-place*/),
          clauseTokensOpt = if (delSAT.enforceSanityChecks) Some(clausesForChecks) else None /*we retain these just for debugging (cross-check) purposes*/ ,
          symbolToEliOpt = None,
          additionalUncertainAtomsInnerCostsStrs = (patsFromProbabilisticClauses.toArray, costsFromProbabilisticClauses.toArray, Array[String]()))

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
