/**
  * Parser for a subset of the ASP Intermediate Format (aspif) in DelSAT. NOT a general-purpose aspif parser -
  * for internal use in the DelSAT project only.
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  * THIS CODE IS PROVIDED WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
  *
  * Plain aspif file format (of which we support a subset): see "A Tutorial on Hybrid Answer Set Solving with clingo",
  * https://link.springer.com/chapter/10.1007/978-3-319-61033-7_6
  *
  * Currently directly supported by DelSAT: Normal rules, #show entries (partially), disjunctions in heads via unfold/shift.  *
  * Use a preprocessor such as Clingo 5 (options --trans-ext=all --pre=aspif) or lp2normal to translate extended rules
  * (e.g., choice rules, weight rules...) to normal rules.
  *
  */

package parsing

import commandline.delSAT
import commandline.delSAT.{debug, log}

import sharedDefs._

import aspIOutils._

import scala.collection.mutable.ArrayBuffer
import scala.collection.{Map, Set, mutable}

/**
  * @author Matthias Nickles
  */
object AspifPlainParser {

  type AspifEli = Int

  final case class AspifRule(headPosAtomsAspifElis: Set[AspifEli],
                             headNegAtomsAspifElis: Set[AspifEli] /* for future extensions */ ,
                             bodyPosAtomsAspifElis: Set[AspifEli],
                             bodyNegAtomsAspifElis: Set[AspifEli],
                             var blit: Int = -1,
                             var spanAuxAspifEli: AspifEli = -1) {

    override def toString = "with Aspif lits:\n  headPosAtomsAspifElis: " + headPosAtomsAspifElis.mkString(",") + "\n" +
      "  headNegAtomsAspifElis: " + headNegAtomsAspifElis.mkString(",") + "\n" +
      "    bodyPosAtomsAspifElis: " + bodyPosAtomsAspifElis.mkString(",") + "\n" +
      "    bodyNegAtomsAspifElis: " + bodyNegAtomsAspifElis.mkString(",")

  }

  val timerParserNs = System.nanoTime()

  val pseudoBlitOffs = 666660000

  def parseAspif(aspifStr: String,
                 shiftAndUnfoldForDisjunctions: Boolean /* <- translate away disjunctions in the head; sound, but only complete for large
     enough noOfUnfolds ->*/ , noOfUnfolds: Int): AspifOrDIMACSPlainParserResult = {

    // NB: There are two sorts of elis used in this method: 1) aspif elis (the literal indices as found in the aspif file) and 2) delSAT elis. The main difference is
    // that the former can be negative numbers whereas delSAT elis are always positive.

    parserInstanceCount.incrementAndGet()

    val aspifLines = splitByRepChar(aspifStr, '\n')

    log("parsetimer 0: " + (System.nanoTime() - timerParserNs) / 1000000 + " ms")

    val acll = aspifLines.length

    val aspifRulesStrLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifNamedSymbolsLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifExternalLinesB = new mutable.ArrayBuilder.ofRef[String]

    var l = 1

    while (l < acll) {

      val line = aspifLines(l)

      if (line.length >= 2 && line(1) == ' ') {

        if (line(0) == '1')
          aspifRulesStrLinesB.+=(line)
        else if (line(0) == '4')
          aspifNamedSymbolsLinesB.+=(line)
        else if (line(0) == '5')
          aspifExternalLinesB.+=(line)
      }

      l += 1

    }

    val aspifRulesStrLines = aspifRulesStrLinesB.result()

    val aspifNamedSymbolsLines = aspifNamedSymbolsLinesB.result()

    val aspifExternalLines = aspifExternalLinesB.result()

    log("parsetimer 1: " + timerToElapsedMs(timerParserNs) + " ms")

    if (aspifExternalLines.length + aspifRulesStrLines.length + aspifNamedSymbolsLines.length + 1 /*<- for the 0 at the end*/ + 1 /*first line*/ !=
      aspifLines.length)
      delSAT.stomp(-102, "Unsupported line type(s) in aspif input data:\n " +
        aspifLines.filter(line => !line.startsWith(" 1") && !line.startsWith("4 ") /*&& !line.startsWith("20")*/ && line.trim != "0").take(5).mkString("\n ") + "\n...")

    val aspifEliToSymbol = mutable.HashMap[AspifEli, String]()

    var aspifRules: ArrayBuffer[AspifRule] = ArrayBuffer[AspifRule]()

    aspifRules.sizeHint(aspifRulesStrLines.length)

    log("parsetimer 2: " + timerToElapsedMs(timerParserNs) + " ms")

    var si = 0

    val ansll = aspifNamedSymbolsLines.length

    while (si < ansll) {

      val aspifNamedSymbolsLineTokens = splitByRepChar(aspifNamedSymbolsLines(si).trim)

      val v3 = Integer.parseInt(aspifNamedSymbolsLineTokens(3))

      if (v3 > 1)
        delSAT.stomp(-102, "Unsupported conditional #show statement\n encoded in line " + aspifNamedSymbolsLines(si))

      val newSymbol = aspifNamedSymbolsLineTokens(2)

      val newSymbolAspifEli: AspifEli = if (v3 == 0) {
        // from an unconditioned (bodyless) #show statement; we currently need to add an auxiliar fact to "undo" this simplification:

        val aspifExtraShowEli = aspifExtraShowEliBoundary + extraShowAspifElitCount.getAndIncrement()

        aspifRules.append(AspifRule(headPosAtomsAspifElis = Set(aspifExtraShowEli),
          headNegAtomsAspifElis = Set(),
          bodyPosAtomsAspifElis = Set(),
          bodyNegAtomsAspifElis = Set()))

        aspifExtraShowEli

      } else
        Integer.parseInt(aspifNamedSymbolsLineTokens(4))

      /* Shouldn't occur, but we also check for possibly ambiguity cases like
            4 1 x 1 21
            4 1 x 1 22
         from #show x:y. (where y = literal 21)
       */

      if (aspifEliToSymbol.get(newSymbolAspifEli) != None)
        delSAT.stomp(-102, "Unsupported line in aspif input. Ambiguous #show for predicate " + newSymbolAspifEli)

      aspifEliToSymbol.update(newSymbolAspifEli, newSymbol)

      si += 1

    }

    log("parsetimer 3: " + timerToElapsedMs(timerParserNs) + " ms")

    var disjWarningShow = false

    var ri = 0

    val arsll = aspifRulesStrLines.length

    while (ri < arsll) {

      val aspifRuleTokens = splitByRepChar(aspifRulesStrLines(ri).trim)

      val aspifRuleTokens2 = Integer.parseInt(aspifRuleTokens(2))

      val bodyStart = 3 + aspifRuleTokens2

      if (aspifRuleTokens(bodyStart) != "0" /*normal body indicator*/ )
        delSAT.stomp(-102, "Non-normal rule detected. Consider preprocessing your program with, e.g., clingo --trans-ext=all or lp2normal.\n Unsupported encoding: " + aspifRulesStrLines(ri))

      if (!disjWarningShow && aspifRuleTokens2 > 1) {

        delSAT.stomp(-104)

        disjWarningShow = true

      }

      val noOfGivenBodyAspifLits = Integer.parseInt(aspifRuleTokens(bodyStart + 1))

      val (bodyGivenPosAspifLits, bodyGivenNegAspifLits) = aspifRuleTokens.drop(bodyStart + 2).take(noOfGivenBodyAspifLits).map(Integer.parseInt(_)).partition(_ >= 0)

      val newAspifRule = if (aspifRuleTokens2 == 0) { // integrity constraint

        val falsPosAspifEli = newFalseAspifElisBoundary + newFalsePredsCounter.getAndIncrement()

        AspifRule(headPosAtomsAspifElis = Set(falsPosAspifEli),
          headNegAtomsAspifElis = Set(),
          bodyPosAtomsAspifElis = bodyGivenPosAspifLits.toSet,
          bodyNegAtomsAspifElis = bodyGivenNegAspifLits.toSet.+(-falsPosAspifEli))

      } else {

        AspifRule(headPosAtomsAspifElis = aspifRuleTokens.drop(3).take(aspifRuleTokens2).map(Integer.parseInt(_)).toSet,
          headNegAtomsAspifElis = Set(),
          bodyPosAtomsAspifElis = bodyGivenPosAspifLits.toSet,
          bodyNegAtomsAspifElis = bodyGivenNegAspifLits.toSet)

      }

      aspifRules.append(newAspifRule)

      Array(bodyGivenPosAspifLits, bodyGivenNegAspifLits.map(-_), newAspifRule.headPosAtomsAspifElis.toArray).foreach(lits => {

        lits.foreach(aspifEli => {

          assert(aspifEli >= 0, "Error: Negative head literal found. Only normal rules are supported by DelSAT: " + newAspifRule)

          if (!aspifEliToSymbol.contains(aspifEli)) {

            val r = if (isNewFalsePosAspifEli(aspifEli))
              auxAtomSymbol(newFalsePredsPrefix, aspifEli - newFalseAspifElisBoundary)
            else {
              auxAtomSymbol(newLatentSymbolAuxAtomPrefix, aspifEli)
              // ^ this way, all newly introduced symbols (eli.e., those which weren't already present in the input program) get either an "L" or an "F" auxiliary atom name.

            }

            aspifEliToSymbol.update(aspifEli, r)

          }

          // Literals without a given symbol (NB: in aspifs generated by Clingo, it was not always clear what the
          // purpose of all unnamed literals in rule lines was.)

        }

        )

      })

      ri += 1

    }

    log("parsetimer E1: " + timerToElapsedMs(timerParserNs) + " ms")

    assert(shiftAndUnfoldForDisjunctions) // because we've disabled the non-disjunctive head checks in the aspif parser

    if (shiftAndUnfoldForDisjunctions) {

      // We shift disjunctions into the bodies of the aspif-rules. Since this alone might not result in the full set of answer sets,
      // we also apply the specified number of unfolds (ideally until the program becomes closed under unfolding, which makes the transformation complete):

      // Reference: Yi Zhou. From disjunctive to normal logic programs via unfolding and shifting. In Proceedings of ECAI'14, 2014.
      //  https://pdfs.semanticscholar.org/ae2c/27f76c260b0d6de056cf260688f929381b09.pdf
      // TODO: We could consider restricting unfolding to unfolding over atoms in certain cycles (e.g., elementary cycles), see
      //  https://www.ijcai.org/Proceedings/16/Papers/164.pdf
      //  However, for disjunctive programs, finding the elementary cycles is intractable (unless the program is already
      //  head-cycle free), and unfolding might introduce new cycles.
      // TODO: An anytime algorithm which incrementally adds unfolds in case of non-convergence. https://www.ijcai.org/Proceedings/16/Papers/164.pdf
      //  But might be difficult to find a good non-convergence criterion besides the current heuristics.

      /*log("aspif rules before unfolding/shifting:\n")

      if (debug)
        aspifRules.foreach(rule => log(rule))

      log("---------------------------------\n") */

      for (i <- 1 to noOfUnfolds) { // TODO: optionally repeat until closed under unfold? But might take a very long time, as number of unfolds grows exponentially

        log("Unfold iteration " + i)

        val aspifRulePairs: mutable.Seq[(AspifRule, AspifRule)] = for (x <- aspifRules; y <- aspifRules) yield (x, y)

        val unfoldRules: Seq[AspifRule] = aspifRulePairs.flatMap { case (rule1, rule2) => {

          //assert(rule1.weight == (1d, 1d) && rule2.weight == (1d, 1d))

          val as = rule1.headPosAtomsAspifElis.intersect(rule2.bodyPosAtomsAspifElis)

          as.map(a => AspifRule(headPosAtomsAspifElis = rule1.headPosAtomsAspifElis.filterNot(_ == a).union(rule2.headPosAtomsAspifElis),
            headNegAtomsAspifElis = Set(),
            bodyPosAtomsAspifElis = rule2.bodyPosAtomsAspifElis.filterNot(_ == a).union(rule1.bodyPosAtomsAspifElis),
            bodyNegAtomsAspifElis = rule1.bodyNegAtomsAspifElis ++ rule2.bodyNegAtomsAspifElis))

        }

        }

        log("Unfold rules:\n")

        if (debug)
          unfoldRules.foreach(rule => log(rule))

        log("---------------------------------\n")

        aspifRules.appendAll(unfoldRules)

      }

      val nonDisjAndDisjAspifRules = aspifRules.partition(_.headPosAtomsAspifElis.size <= 1)

      val shiftedAspifRules = nonDisjAndDisjAspifRules._2.flatMap(rule => { // note that some shifting might already have been applied before calling delSAT (e.g., for head-cycle free programs with clingo/gringo preprocessing)

        //assert(rule.weight == (1d, 1d))

        rule.headPosAtomsAspifElis.map(headAtomi => {

          AspifRule(headPosAtomsAspifElis = Set(headAtomi),
            headNegAtomsAspifElis = Set(),
            bodyPosAtomsAspifElis = rule.bodyPosAtomsAspifElis,
            bodyNegAtomsAspifElis = rule.bodyNegAtomsAspifElis ++ (rule.headPosAtomsAspifElis.filterNot(_ == headAtomi).map(-_)))

        })

      })

      val updatedAspifRules = nonDisjAndDisjAspifRules._1 ++ shiftedAspifRules

      /*log("Aspif rules after folding/shifting:\n")

      if (debug)
        updatedAspifRules.foreach(rule => log(rule))

      log("---------------------------------\n")*/

      aspifRules = updatedAspifRules

    }

    val symbols: Array[String] = aspifEliToSymbol.values.toArray // needs to be the complete set of all symbols (before we can assign blits to rule bodies below)

    val (rules, noOfPosBlits, emptyBodyBlit) = aspifRulesToEliRules(symbols, aspifRules, Some(aspifEliToSymbol))

    AspifOrDIMACSPlainParserResult(symbols, Left(rules), noOfPosBlits, externalAtomElis = Seq() /*aspifExternalsElis*/ ,
      emptyBodyBlit = emptyBodyBlit, directClauseNogoodsOpt = None, clauseTokensOpt = None)

  }

  def aspifRulesToEliRules(symbols: Array[String], aspifRules: ArrayBuffer[AspifRule],
                           aspifEliToSymbolOpt: Option[mutable.HashMap[AspifEli, String]]): (ArrayBuffer[Rule], Int, Int) = {

    val rules = ArrayBuffer[Rule]()

    //rules.sizeHint(aspifRulesStrLines.length)

    val noOfPosAtomElis = symbols.length

    val firstPosBlit = noOfPosAtomElis

    @deprecated var emptyBodyBlit = -1

    // we assume blits (body elis) only for distinct bodies

    val aspifRulesDistinctByBody0: Predef.Map[(Set[AspifEli], Set[AspifEli]), ArrayBuffer[AspifRule]] =
      aspifRules.groupBy(aspifRule => (aspifRule.bodyPosAtomsAspifElis /*NB: we must work with sets here to compare bodies correctly*/ ,
        aspifRule.bodyNegAtomsAspifElis))

    val aspifRulesDistinctByBody = aspifRulesDistinctByBody0.filter((tuple: ((Set[AspifEli], Set[AspifEli]), ArrayBuffer[AspifRule])) =>
      !omitSingletonBlits || tuple._1._1.size + tuple._1._2.size > 1 || tuple._1._1.size + tuple._1._2.size == 0 /*TODO: part == 0 is deprecated, remove after more tests*/)

    val distinctBodiesWithIndex = aspifRulesDistinctByBody.keySet.toArray.zipWithIndex

    val distinctBodiesToIndex: Map[(Set[AspifEli], Set[AspifEli]), Int] = distinctBodiesWithIndex.toMap

    var noOfRealBlits = distinctBodiesWithIndex.length

    var i = 0

    val arlll = aspifRules.length

    while (i < arlll) {

      val aspifRule = aspifRules(i)

      if (omitSingletonBlits && aspifRule.bodyPosAtomsAspifElis.size + aspifRule.bodyNegAtomsAspifElis.size == 1) {

        val pseudoBlit = if (aspifRule.bodyPosAtomsAspifElis.isEmpty) aspifRule.bodyNegAtomsAspifElis.head else aspifRule.bodyPosAtomsAspifElis.head

        aspifRule.blit = if (pseudoBlit < 0) pseudoBlit else pseudoBlit + pseudoBlitOffs // in contrast to the real blits set below, this is not an eli yet!

      } else {

        val body = (aspifRule.bodyPosAtomsAspifElis, aspifRule.bodyNegAtomsAspifElis)

        val blit = firstPosBlit + distinctBodiesToIndex(body)

        if (body._1.isEmpty && body._2.isEmpty) {

          if (emptyBodyBlit == -1)
            emptyBodyBlit = blit // we memorize this just to simplify nogoods later

          aspifRule.blit = emptyBodyBlit // note: this is already a body eli, not an aspif-eli

        } else
          aspifRule.blit = blit // note: this is already a body eli, not an aspif-eli

      }

      i += 1

    }

    log("parsetimer E2: " + timerToElapsedMs(timerParserNs) + " ms")

    // Finally, we translate the rules with aspif-elis into rules with elis: (note: aspif-elis of negative literals are negative numbers, whereas elis of negative literals are positive numbers
    // (differently from, e.g., clingo/clasp and most other solvers))

    val posNegEliBoundary = symbols.length + noOfRealBlits //+ auxSymbolsForSpanningCount.get /*per each given uncertain rule/fact, we later generate two rules*/

    @inline def isPosEli(eli: Eli) = eli < posNegEliBoundary

    @inline def isNegEli(eli: Eli) = eli >= posNegEliBoundary

    @inline def negateEli(eli: Eli): Eli = {

      if (isPosEli(eli))
        eli + posNegEliBoundary
      else
        eli - posNegEliBoundary

    }

    val symbolToEli: Map[String, Eli] = symbols.zipWithIndex.toMap // TODO: costly, but we need this again later anyway

    @inline def positiveAspifEliToPositiveEli(aspifEli: AspifEli): Eli = if (aspifEliToSymbolOpt.isDefined)
      symbolToEli(aspifEliToSymbolOpt.get.get(aspifEli).get)
    else
      aspifEli - 1

    var aspifRulei = 0

    val arl = aspifRules.length

    while (aspifRulei < arl) {

      val aspifRule: AspifRule = aspifRules(aspifRulei)

      //log("aspifRule: " + aspifRule.toString)

      val rule = Rule(headAtomsElis = (aspifRule.headPosAtomsAspifElis.map(posAspifEli => {

        assert(posAspifEli > 0)

        positiveAspifEliToPositiveEli(posAspifEli)

      }) ++
        aspifRule.headNegAtomsAspifElis.map(negAspifEli => {

          assert(negAspifEli < 0)

          negateEli(positiveAspifEliToPositiveEli(-negAspifEli))

        })).toArray,

        bodyPosAtomsElis = aspifRule.bodyPosAtomsAspifElis.map(bpaeli => {

          assert(bpaeli > 0)

          positiveAspifEliToPositiveEli(bpaeli)


        }).toArray,

        bodyNegAtomsElis = aspifRule.bodyNegAtomsAspifElis.map(negativeAspifEli => {

          assert(negativeAspifEli < 0)

          negateEli(positiveAspifEliToPositiveEli(-negativeAspifEli))

        }).toArray,

        blit = {

          if (aspifRule.blit < 0) {

            assert(omitSingletonBlits)

            val eli = negateEli(positiveAspifEliToPositiveEli(-aspifRule.blit))

            assert(negateEli(eli) < symbols.length)

            eli

          } else if (aspifRule.blit >= pseudoBlitOffs) {

            assert(omitSingletonBlits)

            val eli = positiveAspifEliToPositiveEli(aspifRule.blit - pseudoBlitOffs)

            assert(eli < symbols.length)

            eli

          } else
            aspifRule.blit

        })

      assert(rule.headAtomsElis.length <= 1)

      rules.append(rule)

      aspifRulei += 1

    }

    if (delSAT.verbose)
      println("Parsing time: " + timerToElapsedMs(timerParserNs) + " ms")

    (rules, noOfRealBlits, emptyBodyBlit)

  }

}
