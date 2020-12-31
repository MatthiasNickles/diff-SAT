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

import aspIOutils.Pred
import sharedDefs._
import utils.IntArrayUnsafeS

import utils.ArrayValExtensibleIntUnsafe
import utils.Various._

import scala.collection.mutable.ArrayBuffer

/**
  * Parser for DIMACS-CNF and PCNF (probabilistic CNF). !! Not a general-purpose DIMACS-CNF parser - designed for use within diff-SAT only! 
  *
  * @author Matthias Nickles
  *
  */
object DIMACPlainSparser {

  def parseDIMACS(dimacs_CNF_Pr: String): AspifOrDIMACSPlainParserResult = {

    val dimacsParseTimerNs = System.nanoTime()

    val headerStartIt: Option[Eli] = "(\\A|\\n)\\s*p\\s+p?cnf\\s+".r.findFirstMatchIn(dimacs_CNF_Pr).map(_.start)

    if (headerStartIt.isEmpty)
      diffSAT.stomp(-100)

    val headerStart: Int = headerStartIt.get

    val hStr0 = dimacs_CNF_Pr.substring(headerStart)

    val hStr = hStr0.dropWhile(!_.isDigit).trim

    val probabilisticCNF = hStr0.contains("pcnf")

    val noOfVarsR = hStr.takeWhile(_.isDigit).toInt // this actually is the largest variable as an integer. Gaps are allowed (e.g.,
    // if noOfVars=555, a file with only a single clause CNF 1 555 0 would be syntactically ok and would indirectly
    // define variables 2,3,4,...,554 with v|-v).

    var (noOfVars, noOfDummySymbols) = {

      if (padSymbolsToPow2) { // TODO: remove

        // TODO: next2Pow(noOfVarsR * 2) / 2  ??

        val p2 = next2Pow(noOfVarsR)

        val deficit = p2 - noOfVarsR

        (noOfVarsR + deficit, deficit)

      } else
        (noOfVarsR, 0)

    }

    var noOfClauses = hStr.dropWhile(_.isDigit).trim.takeWhile(_.isDigit).toInt // not considering yet probabilistic clauses as these will be replaced by extra clauses

    val headerEnd = dimacs_CNF_Pr.indexOf("\n", headerStart + 1)

    @deprecated val genBodyLitsFromSATClauses: Double = 0d // TODO: REMOVE; must leave 0d for now! Experimentally generates pseudo-"body literals" (blits) in SAT mode, for x% of all
    // variables. If 1d, we completely replace the original clause nogoods with an equivalent theory using blits.
    // Can easily blow up space.

    var s = if (headerEnd == -1) "" else dimacs_CNF_Pr.substring(headerEnd)

    var i = 0

    var sl = s.length

    val llcnA = new ArrayValExtensibleIntUnsafe(new IntArrayUnsafeS(1024))

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

    val extraClausesNogoodsFromProbClauses = ArrayBuffer[ArrayValExtensibleIntUnsafe]() // generated clauses from desugared probabilistically weighted clauses.
    // Observe that these extra clauses replace the weighted clauses.

    val patsFromProbabilisticClauses = ArrayBuffer[Pred]()

    val costsFromProbabilisticClauses = ArrayBuffer[String]() // format of an inner cost term obtained from a probabilistic
    // clause is "(probability-f(vx))^2"

    if (probabilisticCNF) { // first pass desugars any probabilistic clauses ------------------------------------------
      // TODO: we currently use two passes if there are any probabilistic clauses, mainly to find out the actual number
      // of clauses first (probabilistic clauses get desugared into several new clauses). This is most likely not useful  -
      // use a single pass only.

      assert(genBodyLitsFromSATClauses == 0d)

      // we need to amend s (removal of weighted clauses), noOfClauses, noOfVars.
      // Later, add nogoods from generated clauses and add generated clauses to directClauseNogoods. Also, _pat_ and _cost_.

      skipSpaceAndComment

      var index: Int = i

      var isWeightedClause = false

      var weightStr = ""

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

          weightStr = s.substring(index, i)

          if (weightStr(0) == '.')
            weightStr = "0" + weightStr // (otherwise the resulting cost function couldn't be parsed)

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

            patsFromProbabilisticClauses.append(noOfVars.toString)

            val (extraClauseA: ArrayValExtensibleIntUnsafe, extraClausesB: Array[ArrayValExtensibleIntUnsafe],
            costTermForProbClause: String) =
              createExtraClausesNogoodsFromProbabilisticClauseNogood(llcnA, clauseHandleVar = noOfVars, weightStr = weightStr)

            costsFromProbabilisticClauses.append(costTermForProbClause)

            extraClausesNogoodsFromProbClauses.append(extraClauseA)

            extraClausesNogoodsFromProbClauses.appendAll(extraClausesB)

            noOfClauses += extraClausesB.length + 1 /*extraClauseA*/ - 1 /*the annotated clause*/

            isWeightedClause = false

            weightStr = ""

          }

          llcnA.clear()

        } else {

          if (intVal > noOfVars) // some solvers allow this case, but we (and clasp) don't
            diffSAT.stomp(-100, "Variable in CNF file out of range: " + intVal)

          llcnA.append(-intVal) //***

        }

        skipSpaceAndComment

        index = i

      }

    } // -------------------------------------------------------------------------------------------------------------

    val symbols = Array.ofDim[Pred](noOfVars)

    var vi = 0

    while (vi < noOfVars)
      symbols.update(vi, {
        vi += 1;
        vi.toString
      })

    val noOfPosAtomElis = symbols.length

    val clausesForChecks = Array.ofDim[Array[Int]](noOfClauses) // for debugging purposes and the optional blit generation only

    @deprecated val minClauseLengthForExtraNogoods = 0 // for genBodyLitsFromSATClauses only*

    @deprecated var noOfBlits = 0 // TODO: remove! For genBodyLitsFromSATClauses only; unfortunately we need to determine this value before we can start generating nogoods

    val directClauseNogoods: Array[IntArrayUnsafeS] = Array.ofDim[IntArrayUnsafeS](noOfClauses)

    var clauseInc = 0

    if (showIntermediateTimers)
      println("dimacsParseTimerNs 0: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    val llcnB = new ArrayValExtensibleIntUnsafe(new IntArrayUnsafeS(1024)) //new IntArrayList(1024)

    i = 0

    sl = s.length

    skipSpaceAndComment

    var index = i

    @inline def generateClauseNogood(llcn: ArrayValExtensibleIntUnsafe, clauseNogoodIndex: Int): Unit = {

      if (clauseInc >= noOfClauses)
        diffSAT.stomp(-100, "Wrong number of clauses specified in DIMACS header")

      if (extraChecks)
        assert(llcn.size() >= 1)

      directClauseNogoods(clauseNogoodIndex) = llcn.buffer.cloneToNew(padding = 0, keep = llcn.contentLen, cutOff = true)

    }

    var ignoreClause = false

    // Second pass (or first pass in case there weren't any weighted clauses):

    while (i < sl) {

      while (i < sl && s(i) > ' ') {

        if (s(i) == '.') { // we are inside a weighted clause. Ignore.

          ignoreClause = true

          while (i < sl - 1 && !(s(i) == '0' && s(i - 1).isWhitespace && s(i + 1).isWhitespace))
            i += 1

        }

        i += 1

      }

      if (!ignoreClause) {

        var intVal = 0

        var mult = if (s(index) == '-') {

          index += 1

          -1

        } else 1

        var il = i

        do {

          il -= 1

          intVal += (s(il) - '0') * mult

          mult *= 10 // TODO: optimize (*= only where needed for next iteration)

        } while (il > index)

        if (intVal == 0) { // end of clause

          if (genBodyLitsFromSATClauses > 0d || performSanityChecks) {

            clausesForChecks(clauseInc) = { //***  // TODO: move into generateClauseNogood()

              val clauseForCheck = Array.ofDim[Int](llcnB.size)

              var i = 0

              while (i < llcnB.size) {

                clauseForCheck(i) = -llcnB.get(i)

                i += 1

              }

              clauseForCheck

            }

          }

          generateClauseNogood(llcn = llcnB, clauseNogoodIndex = clauseInc)

          clauseInc += 1

          llcnB.clear()

        } else {

          if (intVal > noOfVars) // some solvers allow this case, but we (and clasp) don't
          diffSAT.stomp(-100, "Variable number in CNF file out of range: " + intVal)

          llcnB.append(-intVal)

        }

      } else
        ignoreClause = false

      skipSpaceAndComment

      index = i

    }

    var ei = 0

    while (ei < extraClausesNogoodsFromProbClauses.size) {

      val clauseNogood: ArrayValExtensibleIntUnsafe = extraClausesNogoodsFromProbClauses(ei)

      generateClauseNogood(llcn = clauseNogood, clauseNogoodIndex = clauseInc)

      if (performSanityChecks)
        clausesForChecks(clauseInc) = { // TODO: move into generateClauseNogood()

          //clauseNogood.toIntArray.clone() // just for debugging (check models against original clauses after solving)

          val clauseForCheck = Array.ofDim[Int](clauseNogood.size)

          var i = 0

          while (i < clauseNogood.size) {

            clauseForCheck(i) = -clauseNogood.get(i)

            i += 1

          }

          clauseForCheck

        }

      clauseInc += 1

      ei += 1

    }

    if (!directClauseNogoods.isEmpty && directClauseNogoods.last == null)
      diffSAT.stomp(-100, "Fewer than the specified number of clauses found in DIMACS file")

    assert(noOfClauses == directClauseNogoods.length)

    assert(noOfClauses == clausesForChecks.length)

    assert(noOfBlits == 0)

    if (showIntermediateTimers)
      println("Parsing time: " + timerToElapsedMs(dimacsParseTimerNs) + " ms")

    {

      //println(directClauseNogoods.mkString("\n"))

      AspifOrDIMACSPlainParserResult(symbols = symbols /*.toArray*/ ,
        rulesOrClauseNogoods = Right(directClauseNogoods),
        noOfPosBlits = noOfBlits,
        noOfDummySymbols = noOfDummySymbols,
        externalAtomElis = Seq(),
        assumptionElis = Seq(),
        clausesForChecksOpt = if (performSanityChecks) Some(clausesForChecks) else None /* we retain these just for debugging (cross-check) purposes */ ,
        symbolToEliOpt = None,
        additionalUncertainAtomsInnerCostsStrs = (patsFromProbabilisticClauses.toArray,
          costsFromProbabilisticClauses.toArray,
          Array[String]()))


    } /*else { // the following approach to combine clause nogoods with synthetic ASP rules is supported by Preparation.scala
     // but not currently used:

      val (rules, noOfPosBlits, _) = aspifRulesToEliRules(symbols.toArray, generatedAspifRules, aspifEliToSymbolOpt = None)

      if (diffSAT.verbose)
        println("Generated " + rules.length + " additional rules with " + noOfPosBlits + " blits")

      AspifOrDIMACSPlainParserResult(symbols = symbols.toArray,
        rulesOrClauseNogoods = Left(rules),
        noOfPosBlits = noOfPosBlits,
        externalAtomElis = Seq() /*TODO*/ ,
        directClauseNogoodsOpt = Some(directClauseNogoods.clone() /*otherwise this would get modified in-place*/),
        clauseTokensOpt = Some(clauses) /* we retain these just for debugging (cross-check) purposes */)

    } */

  }

  def createExtraClausesNogoodsFromProbabilisticClauseNogood(llcn /*the probabilistically annotated nogood with additional preceding 0 */ : ArrayValExtensibleIntUnsafe,
                                                             clauseHandleVar: Int, weightStr: String):
  (ArrayValExtensibleIntUnsafe, Array[ArrayValExtensibleIntUnsafe], String) = {

    val extraClauseNogoodA = new ArrayValExtensibleIntUnsafe(buffer = llcn.buffer.clone(0, 0),
      initiallyOccupiedInBuffer = llcn.size) // first value is 0 (the intValue 0 which was added instead of the weight)

    extraClauseNogoodA.update(0, clauseHandleVar)

    val extraClausesNogoodsB = Array.ofDim[ArrayValExtensibleIntUnsafe](llcn.size - 1)

    var k = 1

    while (k < llcn.size) {

      val extraClauseNogoodB = new ArrayValExtensibleIntUnsafe(new IntArrayUnsafeS(2))

      extraClauseNogoodB.append(-clauseHandleVar)

      extraClauseNogoodB.append(-llcn.get(k))

      extraClausesNogoodsB(k - 1) = extraClauseNogoodB

      k += 1

    }

    (extraClauseNogoodA, extraClausesNogoodsB, "(" + weightStr + "-f(v" + clauseHandleVar + "))^2")

  }

}
