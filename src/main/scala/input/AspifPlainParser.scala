/**
  * delSAT
  *
  * Copyright (c) 2018,2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package input

import aspIOutils._
import sharedDefs._

import utils.Various._

import scala.collection.mutable.ArrayBuffer
import scala.collection.{Map, Set, mutable}

/**
  * Parser for a subset of the ASP Intermediate Format (aspif), enhanced with support for probabilistic rules.
  * Not a general-purpose aspif parser; designed for use in delSAT only.
  *
  * Probabilistic rules have the form
  * 1000 p 1 0 1 h B
  * (p either being -1 (undefined probability) or a probability 0<=p<=1. h being a single atom (the only literal in the head)
  * and B being a normal rule body). If p = -1, only the spanning formula [Nickles, Mileo 2015] is being generated but no _pr_ fact,
  * which informally means "rule v not rule".
  *
  * Observe that the above isn't the only way to specify probabilities with delSAT - see README.md for other supported input formats.
  *
  * For a description of the aspif file format see Appendix A in "A Tutorial on Hybrid Answer Set Solving with clingo",
  * https://link.springer.com/chapter/10.1007/978-3-319-61033-7_6, Appendix A.
  *
  * All aspif 1 rule types are supported (including choice, disjunctions in head, weight bodies), however statements
  * of type >= 2 (e.g.., minimize statements or #external) are currently not implemented. Output statements (#show) are partially supported.
  *
  * If some aspif file still cannot be processed it is recommended to try with a preprocessor such as Clingo 5 using options
  * --trans-ext=all --pre=aspif) or lp2normal to translate extended rules. But observe that delSAT cannot be used for finding
  * an optimal model (e.g., using ~| or #minimize).
  *
  * @author Matthias Nickles
  */
object AspifPlainParser {

  type AspifEli = Int

  // Class AspifRule is an intermediate format between the input (either from the aspif file or the user API (DisjunctiveAnswerSetProgramWithCosts))
  // which is afterwards translated into the actual rules ("eli rules"), which are then translated into nogoods.
  // Observe that there is no probability annotation in AspifRule. Parameter atoms, weights and costs are expressed by the user either using
  // special facts _pat_ and _cost_ or translated away into
  final case class AspifRule(headPosAtomsAspifElis: Set[AspifEli], // (if you are tempted to replace Set with Array here: Don't!)
                             headNegAtomsAspifElis: Set[AspifEli], // Must be empty (negation in heads eliminated already when constructing AspifRule)
                             bodyPosAtomsAspifElis: Set[AspifEli],
                             bodyNegAtomsAspifElis: Set[AspifEli], // Observe that apifElis in bodyNegAtomsAspifElis are always negative integers
                             var blit: Int = -1,
                             var spanAuxAspifEli: AspifEli = -1,
                             aspifElisFromDoubleNegationsInBody: Set[AspifEli] = Set[AspifEli]() /* <-- only used when creating rules via API, not via aspif file*/) {

    override def toString = "with Aspif lits:\n  headPosAtomsAspifElis: {" + headPosAtomsAspifElis.mkString(",") + "}\n" +
      "  headNegAtomsAspifElis: {" + headNegAtomsAspifElis.mkString(",") + "}\n" +
      "    bodyPosAtomsAspifElis: {" + bodyPosAtomsAspifElis.mkString(",") + "}\n" +
      "    bodyNegAtomsAspifElis: {" + bodyNegAtomsAspifElis.mkString(",") + "}\n" +
      "    aspifElisFromDoubleNegationsInBody: {" + aspifElisFromDoubleNegationsInBody.mkString(",") + "}"

  }

  val timerParserNs = System.nanoTime()

  val pseudoBlitOffs = 666660000 // for omitSingletonBlits (for omitting the generation of body literals ("blits") in case there is only one literal in the body)

  def parseAspif(aspifStr: String,
                 shiftAndUnfoldForDisjunctions: Boolean /* <- translate away disjunctions in the head; sound, but only complete for large
     enough noOfUnfolds ->*/ , maxNoOfUnfolds: Int): AspifOrDIMACSPlainParserResult = {

    // NB: There are two sorts of elis used in this method: 1) aspif elis (the literal indices as found in the aspif file) and 2) delSAT elis. The main difference is
    // that the former can be negative numbers whereas delSAT elis are always positive.

    parserInstanceCount.incrementAndGet()

    val aspifLines = splitByRepChar(aspifStr, '\n')

    if (showIntermediateTimers)
      println("parsetimer 0: " + (System.nanoTime() - timerParserNs) / 1000000 + " ms")

    val acll = aspifLines.length

    val aspifRulesStrLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifProbRulesStrLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifNamedSymbolsLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifExternalLinesB = new mutable.ArrayBuilder.ofRef[String]

    val aspifFilteringAssumptionLinesB = new mutable.ArrayBuilder.ofRef[String]

    var assumptionAspifLits = Seq[AspifEli]()

    var commentLines = 0

    var l = 1

    while (l < acll) {

      val line = aspifLines(l)

      if (line.length >= 5 && line(4) == ' ' && line(0) == '1' && line(1) == '0' && line(2) == '0' && line(3) == '0')
        aspifProbRulesStrLinesB.+=(line)
      else if (line.length >= 2 && line(1) == ' ') {

        if (line(0) == '1')
          aspifRulesStrLinesB.+=(line)
        else if (line(0) == '4')
          aspifNamedSymbolsLinesB.+=(line)
        else if (line(0) == '5')
          aspifExternalLinesB.+=(line) // NB: support for #external isn't implemented yet (TODO)
        else if (line(0) == '6')
          aspifFilteringAssumptionLinesB.+=(line)

      } else if (line(0) == '1' && line(1) == '0')
        commentLines += 1

      l += 1

    }

    val aspifRulesStrLines = aspifRulesStrLinesB.result()

    val aspifProbRulesStrLines = aspifProbRulesStrLinesB.result()

    val aspifNamedSymbolsLines = aspifNamedSymbolsLinesB.result()

    val aspifExternalLines = aspifExternalLinesB.result()

    val aspifFilteringAssumptionLines = aspifFilteringAssumptionLinesB.result()

    if (commentLines + aspifExternalLines.length + aspifRulesStrLines.length + aspifProbRulesStrLines.length + aspifNamedSymbolsLines.length +
      aspifFilteringAssumptionLines.length + 1 /*<- for the 0 at the end*/ + 1 /*first line*/ !=
      aspifLines.length)
      delSAT.stomp(-102, "Unsupported line type(s) in aspif input data:\n " +
        aspifLines.mkString("\n ") + "\n...")

    val aspifEliToSymbol: mutable.HashMap[AspifEli, Pred] = mutable.HashMap[AspifEli, Pred]()

    if (showIntermediateTimers)
      println("parsetimer 1: " + timerToElapsedMs(timerParserNs) + " ms")

    var aspifRules = mutable.ArrayBuffer[AspifRule]() // creating an empty mutable.ArrayBuffer is suprisingly costly, but faster alternatives like var List don't seem to pay off

    //aspifRules.sizeHint(aspifRulesStrLines.length)

    if (showIntermediateTimers)
      println("parsetimer 2: " + timerToElapsedMs(timerParserNs) + " ms")

    var si = 0

    val ansll = aspifNamedSymbolsLines.length

    while (si < ansll) {

      val aspifNamedSymbolsLineTokens = splitByRepChar(aspifNamedSymbolsLines(si).trim)

      val v3 = Integer.parseInt(aspifNamedSymbolsLineTokens(3))

      if (v3 > 1)
        delSAT.stomp(-102, "Unsupported conditional #show statement\n encoded in line " + aspifNamedSymbolsLines(si))

      val newSymbol = aspifNamedSymbolsLineTokens(2)

      val newSymbolAspifEli: AspifEli = if (v3 == 0) {
        // from an unconditioned (bodyless) #show statement (a way to write a symbolic fact); we currently need to add an auxiliar fact to "undo" this simplification:

        val aspifExtraShowEli = aspifExtraShowEliBoundary + extraShowAspifElitCount.getAndIncrement()

        aspifRules.append(AspifRule(headPosAtomsAspifElis = Set(aspifExtraShowEli),
          headNegAtomsAspifElis = Set(),
          bodyPosAtomsAspifElis = Set(),
          bodyNegAtomsAspifElis = Set()))

        aspifExtraShowEli

      } else
        Integer.parseInt(aspifNamedSymbolsLineTokens(4))

      /* Shouldn't occur, but we also check for possibly ambiguous cases like
            4 1 x 1 21
            4 1 x 1 22
         from #show x:y. (where y = literal 21)
       */

      if (aspifEliToSymbol.get(newSymbolAspifEli) != None)
        delSAT.stomp(-102, "Unsupported line in aspif input. Ambiguous #show for predicate " + newSymbolAspifEli)

      aspifEliToSymbol.update(newSymbolAspifEli, newSymbol)

      si += 1

    }

    if (showIntermediateTimers)
      println("parsetimer 3: " + timerToElapsedMs(timerParserNs) + " ms")

    var disjWarningShow = false

    def parseRules(ruleLines: Array[String], probabilistic: Boolean): Unit = {

      var ri = 0

      val arsll = ruleLines.length

      while (ri < arsll) {

        val ruleLine = ruleLines(ri).trim

        val probability = if (probabilistic) ruleLine.drop(5).takeWhile(_ != ' ').toDouble else 1d // pr=1 is strictly speaking not making a definite rule, but the sampling algo couldn't use that fact anyway...

        val aspifRuleTokens = if (probabilistic) splitByRepChar(ruleLine).drop(2) else splitByRepChar(ruleLine)

        val aspifRuleTokens2 = Integer.parseInt(aspifRuleTokens(2)) // number of literals in the head (semantics:
        // disjunction or {choice}, depending on aspifRuleTokens(1))

        val bodyStart = 3 + aspifRuleTokens2

        val choiceHead = aspifRuleTokens(1) == "1"

        if (aspifRuleTokens(1) != "0" && !choiceHead)
          delSAT.stomp(-102, "Unsupported type of rule in aspif format detected. Consider grounding your program with, e.g., clingo --trans-ext=all --pre=aspif or preprocessing it using lp2normal.\n Unsupported encoding: " + aspifRulesStrLines(ri))

        if (!disjWarningShow && aspifRuleTokens2 > 1 && maxNoOfUnfolds < Int.MaxValue) {

          delSAT.stomp(-104) // not an error, just a warning

          disjWarningShow = true

        }

        val headSet = if (aspifRuleTokens2 != 0) aspifRuleTokens.drop(3).take(aspifRuleTokens2).map(headLit => {

          if (headLit(0) == '-')
            delSAT.stomp(-5020, "Negative head literal in aspif input in rule: " + ruleLines(ri))

          // delSAT "accidentially" understands negative literals in heads in aspif files although these aren't allowed
          // by the standard. The reason is that delSAT eliminates such head literals in addAspifRules which is called during aspif parsing.

          Integer.parseInt(headLit)

        })
        else Array[AspifEli]()

        val (headGivenPosAspifLits, headGivenNegAspifLits) = headSet.partition(_ >= 0)

        if (choiceHead && !headGivenNegAspifLits.isEmpty)
          delSAT.stomp(-102, "In choice rule heads, only positive literals are allowed: " + ruleLines(ri))

        if (aspifRuleTokens(bodyStart) == "0") { // normal rule body

          val noOfGivenBodyAspifLits = Integer.parseInt(aspifRuleTokens(bodyStart + 1))

          val (bodyGivenPosAspifLits, bodyGivenNegAspifLits) = aspifRuleTokens.slice(bodyStart + 2, bodyStart + 2 + noOfGivenBodyAspifLits)
            .map(Integer.parseInt(_)).partition(_ >= 0)

          addAspifRules(bodyGivenPosAspifLits = bodyGivenPosAspifLits, bodyGivenNegAspifLits = bodyGivenNegAspifLits,
            headGivenPosAspifLits = if (choiceHead) Array() else headGivenPosAspifLits,
            headGivenNegAspifLits = headGivenNegAspifLits,
            aspifRulesBuffer = aspifRules, aspifEliToSymbol = aspifEliToSymbol,
            weightBodyOpt = None,
            choiceHeadOpt = if (choiceHead) Some(headGivenPosAspifLits) else None,
            probabilityOpt = if (probabilistic) Some(probability) else None)

        } else if (aspifRuleTokens(bodyStart) == "1") { // body is a weight rule body L{w1=lit1, w2=lit2, ...}

          if (probabilistic)
            delSAT.stomp(-10000, "Weight body not allowed in probabilistic rule in aspif (rule must be normal):\n " + ruleLine)

          val lowerBound = Integer.parseInt(aspifRuleTokens(bodyStart + 1))

          val n = Integer.parseInt(aspifRuleTokens(bodyStart + 2)) // number of <space>literal<space>weight pairs following

          val litWeightPairs: Seq[(Int /*weight*/ , AspifEli)] = aspifRuleTokens.slice(bodyStart + 3, bodyStart + 3 + n * 2).grouped(2).map((litWeightStr: Array[String]) => (Integer.parseInt(litWeightStr(1)), Integer.parseInt(litWeightStr(0)))).toSeq

          addAspifRules(bodyGivenPosAspifLits = Array(), bodyGivenNegAspifLits = Array(),
            headGivenPosAspifLits = if (choiceHead) Array() else headGivenPosAspifLits,
            headGivenNegAspifLits = headGivenNegAspifLits,
            aspifRulesBuffer = aspifRules, aspifEliToSymbol = aspifEliToSymbol,
            weightBodyOpt = Some((lowerBound, litWeightPairs)),
            choiceHeadOpt = if (choiceHead) Some(headGivenPosAspifLits) else None,
            probabilityOpt = None)

        } else
          delSAT.stomp(-102, "Unsupported type of rule detected. Consider grounding your program with, e.g., clingo --trans-ext=all --pre=aspif or preprocessing it using lp2normal.\n Unsupported encoding: " + aspifRulesStrLines(ri))

        ri += 1

      }
    }

    parseRules(aspifRulesStrLines, probabilistic = false)

    parseRules(aspifProbRulesStrLines, probabilistic = true)

    /*if(generateIntegrityRulesForAPIdefinedClassicNegation == 2) {  // not supported and tested (and wouldn't make much sense anyway
      // since all contemporary grounders add those constraints anyway). But see API-defined rules where we actually add integrity constraints for classical negation.

      aspifEliToSymbol.foreach((aspifEliAndSymbol: (AspifEli, String)) => {

        if(aspifEliAndSymbol._2.startsWith("-")) {  // we generate an integrity rule :- x, -x.

          val bodyGivenPosAspifLits: Set[AspifEli] = Set(aspifEliAndSymbol._1)

          val bodyGivenNegAspifLits: Set[AspifEli] = Set(aspifEliToSymbol.find(_._2 == aspifEliAndSymbol._2.stripPrefix("-")).getOrElse({

            delSAT.stomp(-5019, "Classically negated atom " + aspifEliAndSymbol._2 + " found but there is no " + aspifEliAndSymbol._2.stripPrefix("-"))

            (0, "")

          })._1)

          if(bodyGivenNegAspifLits.head != 0) {

            val falsPosAspifEli = newFalseAspifElisBoundary + newFalsePredsCounter.getAndIncrement()

            val integConstrForClassicalNeg = AspifRule(headPosAtomsAspifElis = Set(falsPosAspifEli),
              headNegAtomsAspifElis = Set(),
              bodyPosAtomsAspifElis = bodyGivenPosAspifLits,
              bodyNegAtomsAspifElis = bodyGivenNegAspifLits.+(-falsPosAspifEli))

            addAspifRule(bodyGivenPosAspifLits.toArray, bodyGivenNegAspifLits.toArray, integConstrForClassicalNeg)

          }

        }

      })

    } */

    if (showIntermediateTimers)
      println("parsetimer E1: " + timerToElapsedMs(timerParserNs) + " ms")

    var ai = 0

    val assll = aspifFilteringAssumptionLines.length

    while (ai < assll) {

      val assumptionLineToken = splitByRepChar(aspifFilteringAssumptionLines(ai).trim)

      val assumptionLitsInLine = assumptionLineToken.drop(2).map(Integer.parseInt(_))

      assumptionAspifLits ++= assumptionLitsInLine

      ai += 1

    }

    assert(shiftAndUnfoldForDisjunctions) // because we've disabled the non-disjunctive head checks in the aspif parser

    if (shiftAndUnfoldForDisjunctions) {

      val updatedAspifRules = resolveDisjunctiveHead(maxNoOfUnfolds, aspifRules)

      /*if(debug) println("Aspif rules after folding/shifting:\n")

      if (debug)
        updatedAspifRules.foreach(rule => if(debug) println(rule))

      if(debug) println("---------------------------------\n")*/

      aspifRules = updatedAspifRules

    }

    val symbols: Array[String] = aspifEliToSymbol.values.toArray // needs to be the complete set of all symbols (before we can assign blits to rule bodies below)

    val (rules, noOfPosBlits, emptyBodyBlit, symbolToEli, additionalUncertainAtomsInnerCostsStrs, assumptionElis) =
      aspifRulesToEliRules(symbols, aspifRules, Some(aspifEliToSymbol), assumptionAspifLits)

    AspifOrDIMACSPlainParserResult(symbols = symbols,
      rulesOrClauseNogoods = Left(rules),
      noOfPosBlits = noOfPosBlits,
      noOfDummySymbols = 0,
      externalAtomElis = Seq(),
      assumptionElis = assumptionElis,
      emptyBodyBlit = emptyBodyBlit,
      clausesForChecksOpt = None, symbolToEliOpt = Some(symbolToEli),
      additionalUncertainAtomsInnerCostsStrs = additionalUncertainAtomsInnerCostsStrs,
      aspifEliToSymbolOpt = Some(aspifEliToSymbol),
      aspifRulesOpt = Some(aspifRules))

  }

  def resolveDisjunctiveHead(maxNoOfUnfolds: Int /* >= 1 */ , aspifRules: ArrayBuffer[AspifRule]): ArrayBuffer[AspifRule] = {
    // We shift disjunctions into the bodies of the aspif-rules. Since this alone might not result in the full set of answer sets,
    // we also apply the specified number of unfolds (ideally until the program becomes closed under unfolding, which makes the transformation complete):

    // Reference: Yi Zhou. From disjunctive to normal logic programs via unfolding and shifting. In Procs. ECAI'14, 2014.
    //  https://pdfs.semanticscholar.org/ae2c/27f76c260b0d6de056cf260688f929381b09.pdf

    // TODO: Optimize. E.g., we could consider restricting unfolding to unfolding over atoms in certain cycles (e.g., elementary cycles), see
    //  https://www.ijcai.org/Proceedings/16/Papers/164.pdf
    //  However, for disjunctive programs, finding the elementary cycles is intractable (unless the program is already
    //  head-cycle free), and unfolding might introduce new cycles.
    // TODO: An anytime algorithm which incrementally adds unfolds in case of non-convergence. https://www.ijcai.org/Proceedings/16/Papers/164.pdf
    //  But might be difficult to find a good non-convergence criterion besides the current heuristics.

    val hasDisjunctiveHead = aspifRules.exists(rule => rule.headPosAtomsAspifElis.size > 1 || rule.headNegAtomsAspifElis.size > 1)

    if (hasDisjunctiveHead) {

      if (debug) {

        println("Program has disjunctive heads; aspif rules before unfolding/shifting:\n")

        aspifRules.foreach(println(_))

        println("---------------------------------\nmaxNoOfUnfolds: " + maxNoOfUnfolds)

      }

      def unfoldUntilClosureOrMax(maxNoOfUnfolds: Int): Unit = { // with default settings (maxNoOfUnfolds = Int.MaxValue), we effectively
        // apply unfolds until the program is closed under unfolding.

        var i = 0

        var closedUnderUnfold = false

        val rulesWithUnfoldedRules = mutable.HashSet[AspifRule]()

        rulesWithUnfoldedRules.addAll(aspifRules)

        var noOfRules = rulesWithUnfoldedRules.size

        do {

          if (debug) println("###Unfold iteration " + i)

          val aspifRulePairs: mutable.Seq[(AspifRule, AspifRule)] = for (x <- aspifRules; y <- aspifRules) yield (x, y)

          val unfoldRules: mutable.Seq[AspifRule] = aspifRulePairs.flatMap { case (rule1, rule2) => {

            //assert(rule1.weight == (1d, 1d) && rule2.weight == (1d, 1d))

            val as = rule1.headPosAtomsAspifElis.intersect(rule2.bodyPosAtomsAspifElis)

            as.map(a => AspifRule(headPosAtomsAspifElis = rule1.headPosAtomsAspifElis.filterNot(_ == a).union(rule2.headPosAtomsAspifElis),
              headNegAtomsAspifElis = Set(),
              bodyPosAtomsAspifElis = rule2.bodyPosAtomsAspifElis.filterNot(_ == a).union(rule1.bodyPosAtomsAspifElis),
              bodyNegAtomsAspifElis = rule1.bodyNegAtomsAspifElis ++ rule2.bodyNegAtomsAspifElis))

          }

          }

          if (debug) println("  Unfold rules:\n")

          if (debug)
            unfoldRules.foreach(rule => println("  " + rule))

          if (debug) println("---------------------------------\n")

          rulesWithUnfoldedRules.addAll(unfoldRules)

          val newNoOfRules = rulesWithUnfoldedRules.size

          closedUnderUnfold = newNoOfRules == noOfRules

          noOfRules = newNoOfRules

          i += 1

        } while (!closedUnderUnfold && i < maxNoOfUnfolds)

        aspifRules.clear

        aspifRules.addAll(rulesWithUnfoldedRules)

      }

      unfoldUntilClosureOrMax(maxNoOfUnfolds)

      val nonDisjAndDisjAspifRules = aspifRules.partition(_.headPosAtomsAspifElis.size <= 1)

      //println("\n============\nnonDisjAndDisjAspifRules_1:\n" + nonDisjAndDisjAspifRules._1.map(_.toString).mkString("\n"))

      //println("\n----------\nnonDisjAndDisjAspifRules_2:\n" + nonDisjAndDisjAspifRules._2.map(_.toString).mkString("\n"))

      val shiftedAspifRules = nonDisjAndDisjAspifRules._2.flatMap(rule => { // note that some shifting might already have been applied before calling delSAT (e.g., for head-cycle free programs with clingo/gringo preprocessing)

        rule.headPosAtomsAspifElis.map(headAtomi => {

          AspifRule(headPosAtomsAspifElis = Set(headAtomi),
            headNegAtomsAspifElis = Set(),
            bodyPosAtomsAspifElis = rule.bodyPosAtomsAspifElis,
            bodyNegAtomsAspifElis = rule.bodyNegAtomsAspifElis ++ (rule.headPosAtomsAspifElis.filterNot(_ == headAtomi).map(-_)))

        })

      })

      //println("\nshiftedAspifRules:\n" + shiftedAspifRules.map(_.toString).mkString("\n"))

      //println("\n=========================================================\n")

      val updatedAspifRules = nonDisjAndDisjAspifRules._1 ++ shiftedAspifRules

      updatedAspifRules

    } else
      aspifRules

  }

  /**
    * Constructs and inserts into a buffer one or more regular or probabilistically weighted ASPIF rules.
    * Arguments specify a single ASP rule which might be transformed into one or more ASPIF rules (e.g.,
    * a single weight rule (NB: "weight rule" is a term in ASP which is unrelated to probabilistic weights) is
    * turned into several ASPIF rules).
    *
    * Allows to specify simple default negation in (multiple) head and body literals,
    * but not any double negation ("not not") anywhere. Double negation must have been eliminated (and traced in case of
    * body literals, using litsFromDoubleNegatedInBody) already before calling this method.
    *
    * This method performs further eliminations:
    * Negative head literals are shifted in the body as double negated literals.
    *
    * If a weight rule body is given (weightBodyOpt), bodyGivenPosAspifLits and bodyGivenNegAspifLits must be empty.
    * If a choice rule head is given (choiceHeadOpt), headGivenPosAspifLits and headGivenNegAspifLits must be empty.
    *
    * If a probability is given (probabilityOpt), the rule must be a normal rule and aspifElisFromDoubleNegatedInBody must be empty.
    *
    * @param bodyGivenPosAspifLits
    * @param bodyGivenNegAspifLits            Must all be negative integers
    * @param aspifElisFromDoubleNegatedInBody (positive) aspif elis within bodyGivenPosAspifLits which stem from eliminated double negation in bodies
    * @param headGivenPosAspifLits
    * @param headGivenNegAspifLits            Must all be negative integers
    * @param weightBodyOpt                    Cannot be combined with nonempty set of body elis. Note: the term "weight rule" has
    *                                         nothing to do with probabilistic weights, it means a plain ASP rule of form h :- L{w1:l1,...,wn:ln}.
    * @param choiceHeadOpt                    Positive aspif literals only. Cannot be combined with nonempty set of head elis.
    * @param aspifRulesBuffer                 Where the new aspif rule gets added
    * @param aspifEliToSymbol
    * @param probabilityOpt                   The optional probability of the entire rule. For normal rules only.
    *                                         Value between 0 and 1. Also allowed -1, which just generates the spanning rule but doesn't
    *                                         add a _pr_ fact (corresponding to "[.] rule" in PrASP).
    */
  def addAspifRules( // NB: Double default negation ("not not") can only stem from using the delSAT API, not from aspif files (where gringo/clingo has already replaced it with something else).
                     // Double negation in the body needs already to be eliminated AND traced (see doubleNegationIndicesInBodyPosAtomsElis),
                     // double negation in the head needs already be to be entirely eliminated with no tracing required (see class DisjunctiveAnswerSetProgramWithCosts).
                     bodyGivenPosAspifLits: Array[AspifEli],
                     bodyGivenNegAspifLits: Array[AspifEli] /*these are always negative integers representing "... :- ..., not a".
                           bodyGivenNegAspifLits thus cannot be used to encode "... :- ..., not not a". Thus, before calling this function,
                           we put "not not a" as "a" in the bodyGivenPosAspifLits (i.e., treat it like double classic negation temporarily)
                           and keep track of these body literals using litsFromDoubleNegatedInBody so that we can do a special stable model test after SAT solving */ ,
                     aspifElisFromDoubleNegatedInBody: Set[AspifEli] = Set[AspifEli]() /* <-- only used when creating rules via API, not via aspif file*/ ,
                     headGivenPosAspifLits: Array[AspifEli],
                     headGivenNegAspifLits: Array[AspifEli] /*like bodyGivenNegAspifLits, these are always negative, so
                           this cannot be used to encode "not not" in the head. Before calling this function, the grounder or
                           symbolic API must have already eliminated double negation entirely (by shifting "not not" to a "not" in the body)*/ ,
                     weightBodyOpt: Option[(Int /*lower bound*/ , Seq[(Int /*weight*/ , AspifEli)])],
                     choiceHeadOpt: Option[Seq[AspifEli /*must be positive*/ ]],
                     aspifRulesBuffer: ArrayBuffer[AspifRule],
                     aspifEliToSymbol: mutable.HashMap[AspifEli, Pred],
                     probabilityOpt: Option[Double]): Unit = {

    if (choiceHeadOpt.isDefined) {

      if (!headGivenPosAspifLits.isEmpty || !headGivenNegAspifLits.isEmpty)
        delSAT.stomp(-10000, "Choice rule head doesn't allow specification of head literals in addAspifRules()")

      if (probabilityOpt.isDefined)
        delSAT.stomp(-10000, "Choice rule cannot be combined with rule probability in addAspifRules()")

      val choiceHead = choiceHeadOpt.get

      choiceHead.foreach((choiceLit: AspifEli) => {

        addAspifRules(bodyGivenPosAspifLits = bodyGivenPosAspifLits,
          bodyGivenNegAspifLits = bodyGivenNegAspifLits,
          headGivenPosAspifLits = Array(if (choiceLit > 0) choiceLit else -choiceLit), //Array(choiceLit),
          headGivenNegAspifLits = Array(if (choiceLit < 0) choiceLit else -choiceLit), //Array(-choiceLit),
          weightBodyOpt = weightBodyOpt,
          aspifRulesBuffer = aspifRulesBuffer,
          aspifEliToSymbol = aspifEliToSymbol,
          choiceHeadOpt = None,
          probabilityOpt = None)

      })

    } else if (probabilityOpt.isDefined) {

      if (headGivenPosAspifLits.length != 1 || !headGivenNegAspifLits.isEmpty)
        delSAT.stomp(-10000, "Probabilistic rule head needs to consist of exactly one positive literal (normal rule head) in addAspifRules()")

      if (!aspifElisFromDoubleNegatedInBody.isEmpty)
        delSAT.stomp(-10000, "Probabilistic rule body literals must not stem from double negation (normal rules only) in addAspifRules()")

      /* We transform the probabilistic rule into this form:
          aux:- l1, l2, ..., not h.
          h :- l1, l2, ..., not aux.
          _pr_(aux, floor(10000-pr*10000)).
       */

      // the new aux atom (seen as a "spanning" atom, i.e., which is used in encoding a degree of freedom "rule or not rule"):

      val auxAspifEliForProbRule = aspiEliForAuxSymbolForOtherPurposesBoundary + newAuxForOtherPurposesPredsCounter.getAndIncrement()

      val auxAspifEliForProbRuleSymbol = auxAtomSymbol(newSpanSymbolAuxAtomPrefix, auxAspifEliForProbRule - aspiEliForAuxSymbolForOtherPurposesBoundary)

      aspifEliToSymbol.update(auxAspifEliForProbRule, auxAspifEliForProbRuleSymbol)

      // the new _pr_ symbol (unless probabilityOpt = Some(-1)):

      val auxPrFactAspifEliForProbRule: AspifEli = if (probabilityOpt.get >= 0d) {

        val auxPrFactAspifEliForProbRule = aspiEliForAuxSymbolForOtherPurposesBoundary + newAuxForOtherPurposesPredsCounter.getAndIncrement()

        val auxPrFactAspifEliForProbRuleSymbol = "_pr_(" + auxAspifEliForProbRuleSymbol +
          "," + (Math.floor(10000d - probabilityOpt.get * 10000d).toInt) + ")"

        aspifEliToSymbol.update(auxPrFactAspifEliForProbRule, auxPrFactAspifEliForProbRuleSymbol)

        auxPrFactAspifEliForProbRule

      } else 0

      // the three new rules:

      addAspifRules(
        headGivenPosAspifLits = Array(auxAspifEliForProbRule),
        headGivenNegAspifLits = Array(),
        bodyGivenPosAspifLits = bodyGivenPosAspifLits,
        bodyGivenNegAspifLits = bodyGivenNegAspifLits.toSet.+(-headGivenPosAspifLits.head).toArray,
        weightBodyOpt = None,
        aspifRulesBuffer = aspifRulesBuffer,
        aspifEliToSymbol = aspifEliToSymbol,
        choiceHeadOpt = None,
        probabilityOpt = None)

      addAspifRules(
        headGivenPosAspifLits = headGivenPosAspifLits,
        headGivenNegAspifLits = Array(),
        bodyGivenPosAspifLits = bodyGivenPosAspifLits,
        bodyGivenNegAspifLits = bodyGivenNegAspifLits.toSet.+(-auxAspifEliForProbRule).toArray,
        weightBodyOpt = None,
        aspifRulesBuffer = aspifRulesBuffer,
        aspifEliToSymbol = aspifEliToSymbol,
        choiceHeadOpt = None,
        probabilityOpt = None)

      if (probabilityOpt.get >= 0d)
        addAspifRules(
          headGivenPosAspifLits = Array(auxPrFactAspifEliForProbRule),
          headGivenNegAspifLits = Array(),
          bodyGivenPosAspifLits = Array(),
          bodyGivenNegAspifLits = Array(),
          weightBodyOpt = None,
          aspifRulesBuffer = aspifRulesBuffer,
          aspifEliToSymbol = aspifEliToSymbol,
          choiceHeadOpt = None,
          probabilityOpt = None)

    } else if (weightBodyOpt.isDefined) {

      if (!bodyGivenPosAspifLits.isEmpty || !bodyGivenNegAspifLits.isEmpty)
        delSAT.stomp(-10000, "Weight rule body doesn't allow specification of body literals in addAspifRules()")

      val weightBody = weightBodyOpt.get

      // we use the simple equivalence proposed in Ferraris&Lifschitz [2005]. TODO: use linear number of rules approach? Is it actually faster?

      val n = weightBody._2.length

      val l = weightBody._1

      val x = (0 until n).toSet.subsets.toSeq.filter((subSet: Predef.Set[Int]) => {

        val yy = subSet.toSeq /*so that we count the same weight multiple times: */ .map { index => {

          val weight = weightBody._2(index)._1

          weight

        }
        }

        yy.sum

      } >= l).toSeq

      val disj: Seq[Predef.Set[AspifEli]] = x.map(setOfIndices => setOfIndices.map(index => weightBody._2(index)._2)).toSeq

      //println(disj.map(_.map(aspifEliToSymbol(_).mkString(" ^ "))).mkString("\n"))

      disj.foreach(conjSetOfAspifElis => {

        val (bodyPosAspifElis, bodyNegAspifElis) = conjSetOfAspifElis.partition(_ >= 0)

        addAspifRules(bodyGivenPosAspifLits = bodyPosAspifElis.toArray,
          bodyGivenNegAspifLits = bodyNegAspifElis.toArray,
          headGivenPosAspifLits = headGivenPosAspifLits,
          headGivenNegAspifLits = headGivenNegAspifLits,
          weightBodyOpt = None,
          aspifRulesBuffer = aspifRulesBuffer,
          aspifEliToSymbol = aspifEliToSymbol,
          choiceHeadOpt = choiceHeadOpt,
          probabilityOpt = None)

      })

    } else {

      val newAspifRule = if (headGivenPosAspifLits.isEmpty && headGivenNegAspifLits.isEmpty) { // integrity constraint (":- ...")

        assert(headGivenPosAspifLits.isEmpty && headGivenNegAspifLits.isEmpty)

        val falsPosAspifEli = newFalseAspifElisBoundary + newFalsePredsCounter.getAndIncrement()

        AspifRule(headPosAtomsAspifElis = Set(falsPosAspifEli), // we encode integrity constraints as newFalseAtom :- ..., not newFalseAtom
          headNegAtomsAspifElis = Set[AspifEli](),
          bodyPosAtomsAspifElis = bodyGivenPosAspifLits.toSet,
          bodyNegAtomsAspifElis = bodyGivenNegAspifLits.toSet.+(-falsPosAspifEli),
          aspifElisFromDoubleNegationsInBody = aspifElisFromDoubleNegatedInBody)

      } else {

        if (headGivenPosAspifLits.isEmpty && headGivenNegAspifLits.isEmpty)
          delSAT.stomp(-10000, "Empty aspif rule head but no integrity constraint rule type specified in addAspifRules()")

        if (headGivenPosAspifLits.isEmpty) { // since we eliminate negative head literals here, we get an integrity constraint in this case:

          val falsPosAspifEli = newFalseAspifElisBoundary + newFalsePredsCounter.getAndIncrement()

          AspifRule(headPosAtomsAspifElis = Set(falsPosAspifEli), // we encode integrity constraints as newFalseAtom :- ..., not newFalseAtom
            headNegAtomsAspifElis = Set[AspifEli](),
            bodyPosAtomsAspifElis = bodyGivenPosAspifLits.toSet ++ headGivenNegAspifLits.map(-_),
            bodyNegAtomsAspifElis = bodyGivenNegAspifLits.toSet.+(-falsPosAspifEli),
            aspifElisFromDoubleNegationsInBody = aspifElisFromDoubleNegatedInBody ++ headGivenNegAspifLits.map(-_))

          // (a symbol for falsPosAspifEli is created further below)

        } else {

          AspifRule(
            headPosAtomsAspifElis = headGivenPosAspifLits.toSet,
            headNegAtomsAspifElis = Set[AspifEli](),
            bodyPosAtomsAspifElis = bodyGivenPosAspifLits.toSet ++ headGivenNegAspifLits.map(-_),
            bodyNegAtomsAspifElis = bodyGivenNegAspifLits.toSet,
            aspifElisFromDoubleNegationsInBody = aspifElisFromDoubleNegatedInBody ++ headGivenNegAspifLits.map(-_))

        }

      }

      if (debug) println("newAspifRule: " + newAspifRule)

      aspifRulesBuffer.append(newAspifRule)

      // We create symbols for any remaining aspif elis where a symbol doesn't exist yet in aspifEliToSymbol:

      Array(bodyGivenPosAspifLits,
        bodyGivenNegAspifLits.map(-_),
        newAspifRule.headPosAtomsAspifElis.toArray).foreach(lits => {

        lits.foreach(aspifEli => {

          //assert(aspifEli >= 0, "Error: Negative head literal found (not yet supported by delSAT): " + newAspifRule)
          //if (aspifEli < 0)
          // delSAT.stomp(-102, "Negative head literal found in aspif rule (not supported): " + newAspifRule)

          if (!aspifEliToSymbol.contains(aspifEli)) {

            val r = if (isNewFalsePosAspifEli(aspifEli))
              auxAtomSymbol(newFalsePredsPrefix, aspifEli - newFalseAspifElisBoundary)
            else {
              auxAtomSymbol(newLatentSymbolAuxAtomPrefix, aspifEli)
              // ^ this way, all newly introduced symbols (i.e., those which weren't already present in the input program)
              // get either an "L" or an "F" auxiliary atom name.

            }

            aspifEliToSymbol.update(aspifEli, r)

          }

          // Literals without a given symbol (NB: in aspifs generated by Clingo, it was not always clear what the
          // purpose of all unnamed literals in rule statements was. This doesn't affect correctness.)

        }

        )

      })

    }

  }

  def aspifRulesToEliRules(symbols: Array[String], aspifRules: ArrayBuffer[AspifRule],
                           aspifEliToSymbolOpt: Option[mutable.HashMap[AspifEli, String]],
                           assumptionAspifElis: Seq[AspifEli]): (ArrayBuffer[Rule], Int, Int, Predef.Map[String, AspifEli], (Array[String], Array[String], Array[String]), Seq[Eli]) = {

    val rules = ArrayBuffer[Rule]()

    val probFactBPrefix = probabilisticFactPrefix + "("

    val patFactBPrefix = patFactPrefix + "("

    val costFactBPrefix = costFactPrefix + "("

    val evalFactBPrefix = evalFactPrefix + "("

    val probabilisticFacts = ArrayBuffer[(String, Double)]() // can be used as an alternative to declaring inner MSE costs. From these we'll generate MSE inner costs

    val patsFromFacts = ArrayBuffer[String]() // can be used as an alternative to declaring parameter atoms using a "pats" line

    val costsFromFacts = ArrayBuffer[String]() // can be used as an alternative to declaring an inner cost using a "cost" line

    val evalsFromFacts = ArrayBuffer[String]()

    //rules.sizeHint(aspifRulesStrLines.length)

    val noOfPosAtomElis = symbols.length

    val firstPosBlit = noOfPosAtomElis + 1 // ("blit" = eli of a literal which represents an entire rule body)

    @deprecated var emptyBodyBlit = 0

    // we assume blits (body elis) only for distinct bodies

    if (showIntermediateTimers)
      println("parsetimer E2: " + timerToElapsedMs(timerParserNs) + " ms")

    val aspifRulesDistinctByBody0: Predef.Map[(Set[AspifEli], Set[AspifEli]), ArrayBuffer[AspifRule]] =
      aspifRules.groupBy(aspifRule => (aspifRule.bodyPosAtomsAspifElis /*NB: we must work with sets here to compare bodies correctly*/ ,
        aspifRule.bodyNegAtomsAspifElis))

    if (showIntermediateTimers)
      println("parsetimer E2a: " + timerToElapsedMs(timerParserNs) + " ms")

    val aspifRulesDistinctByBody = aspifRulesDistinctByBody0.filter((tuple: ((Set[AspifEli], Set[AspifEli]), ArrayBuffer[AspifRule])) =>
      !omitSingletonBlits || tuple._1._1.size + tuple._1._2.size > 1 || tuple._1._1.size + tuple._1._2.size == 0 /*TODO: part == 0 is deprecated, remove after more tests*/)

    if (showIntermediateTimers)
      println("parsetimer E2b: " + timerToElapsedMs(timerParserNs) + " ms")

    val distinctBodiesWithIndex = aspifRulesDistinctByBody.keySet.toArray.zipWithIndex

    if (showIntermediateTimers)
      println("parsetimer E2c: " + timerToElapsedMs(timerParserNs) + " ms")

    val distinctBodiesToIndex: Map[(Set[AspifEli], Set[AspifEli]), Int] = distinctBodiesWithIndex.toMap

    if (showIntermediateTimers)
      println("parsetimer E2d: " + timerToElapsedMs(timerParserNs) + " ms")

    val noOfRealBlits = distinctBodiesWithIndex.length

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

          if (emptyBodyBlit == 0)
            emptyBodyBlit = blit // so that we can reuse this blit later

          aspifRule.blit = emptyBodyBlit // note: this is already a body eli, not an aspif-eli (original literal number)

        } else
          aspifRule.blit = blit // note: this is already a body eli, not an aspif-eli

      }

      i += 1

    }

    if (showIntermediateTimers)
      println("parsetimer E3: " + timerToElapsedMs(timerParserNs) + " ms")

    @inline def negateEli(eli: Eli): Eli = -eli

    val symbolToEli: Predef.Map[String, AspifEli] = (Array("000" /*dummy, since eli 0 doesn't exist*/) ++ symbols).zipWithIndex.toMap // *** //symbols.zipWithIndex.toMap // TODO: optimize this
    // Remark: for eli->symbol, simply use symbols(eli - 1)

    @inline def positiveAspifEliToPositiveEli(aspifEli: AspifEli): Eli = if (aspifEliToSymbolOpt.isDefined)
      symbolToEli(aspifEliToSymbolOpt.get.get(aspifEli).get) // observe that we couldn't use eli = aspifEli, as the sequence of aspif elis might not be consecutive
    else {

      assert(false, "Please check and remove assertion")

      aspifEli // *** - 1

    }

    @inline def negativeAspifEliToNegativeEli(negAspifEli: AspifEli): Eli = negateEli(positiveAspifEliToPositiveEli(-negAspifEli))

    /*
    @inline def enhAspifArrayBy(elis: Array[Eli], eli: Eli) = {

      val copied = new Array[Eli](elis.length + 1)

      System.arraycopy(elis, 0, copied, 1, elis.length)

      copied(elis.length) = eli

      copied

    }*/

    var aspifRulei = 0

    val arl = aspifRules.length

    while (aspifRulei < arl) {

      val aspifRule: AspifRule = aspifRules(aspifRulei)

      //if(debug) println("aspifRule: " + aspifRule.toString)

      if (!aspifRule.headNegAtomsAspifElis.isEmpty) // we eliminate negative head literals already earlier (when creating the AspifRule),
      // so this should not happen
      delSAT.stomp(-10000, "Aspif rule head with negative literals found in aspifRulesToEliRules()")

      val rule = Rule(headAtomsElis = (aspifRule.headPosAtomsAspifElis.map(posAspifEli => {

        assert(posAspifEli > 0)

        positiveAspifEliToPositiveEli(posAspifEli)

      }) ++
        aspifRule.headNegAtomsAspifElis.map(negAspifEli => { // these are eliminated already when constructing the AspifRule

          delSAT.stomp(-10000, "Negative literals in aspif rule must not occur anymore at this point")

          assert(negAspifEli < 0)

          negativeAspifEliToNegativeEli(negAspifEli)

        })).toArray,

        bodyPosAtomsElis = aspifRule.bodyPosAtomsAspifElis.map(bpaeli => {

          assert(bpaeli > 0)

          positiveAspifEliToPositiveEli(bpaeli)

        }).toArray,

        elisFromDoubleNegationsInBodyPosAtomsElis = aspifRule.aspifElisFromDoubleNegationsInBody.map(bpaeli => {

          assert(bpaeli > 0)

          positiveAspifEliToPositiveEli(bpaeli)

        }).toArray,

        bodyNegAtomsElis = aspifRule.bodyNegAtomsAspifElis.map(negativeAspifEli => {

          assert(negativeAspifEli < 0)

          negativeAspifEliToNegativeEli(negativeAspifEli)

        }).toArray,

        blit = {

          if (aspifRule.blit < 0) {

            assert(omitSingletonBlits)

            val eli = negateEli(positiveAspifEliToPositiveEli(-aspifRule.blit))

            assert(negateEli(eli) <= symbols.length)

            eli

          } else if (aspifRule.blit >= pseudoBlitOffs) {

            assert(omitSingletonBlits)

            val eli = positiveAspifEliToPositiveEli(aspifRule.blit - pseudoBlitOffs)

            assert(eli <= symbols.length)

            eli

          } else
            aspifRule.blit

        })

      //if(debug) println("parsetimer E4: " + timerToElapsedMs(timerParserNs) + " ms")

      assert(rule.headAtomsElis.length <= 1) // we've eliminated choice and disjunctions in head already

      lazy val isPr = symbols(rule.headAtomsElis.head - 1).startsWith(probFactBPrefix)

      lazy val isPat = symbols(rule.headAtomsElis.head - 1).startsWith(patFactBPrefix)

      lazy val isCost = symbols(rule.headAtomsElis.head - 1).startsWith(costFactBPrefix)

      lazy val isEval = symbols(rule.headAtomsElis.head - 1).startsWith(evalFactBPrefix)

      if (rule.bodyNegAtomsElis.length == 0 && rule.bodyPosAtomsElis.length == 0 && rule.headAtomsElis.length == 1) {

        if (isPr) {

          val probFact = symbols(rule.headAtomsElis.head - 1)

          //println("Encountered probability definition fact in aspif input: " + probFact)

          var pfs = probFact.stripPrefix(probFactBPrefix)

          val givenProbabilityStr = pfs.reverse.takeWhile(_ != ',').reverse.stripSuffix(")")

          if (givenProbabilityStr != "\"?\"") {

            val reifiedFact = pfs.dropRight(givenProbabilityStr.length + 2).trim

            val givenProbability = givenProbabilityStr.toDouble / probabilisticFactProbDivider

            //println("   parsed as Pr(" + reifiedFact + ") = " + givenProbability)

            probabilisticFacts.append((reifiedFact, givenProbability))

          }

        } else if (isPat) {

          val patFact = symbols(rule.headAtomsElis.head - 1)

          //println("Encountered parameter atom definition fact in aspif input: " + patFact)

          var pat = patFact.stripPrefix(patFactBPrefix).stripSuffix(")").trim.stripPrefix("\"").stripSuffix("\"").trim

          patsFromFacts.append(pat)

        } else if (isCost) {

          val costFact = symbols(rule.headAtomsElis.head - 1)

          //println("Encountered cost definition fact in aspif input: " + costFact)

          var cost = costFact.stripPrefix(costFactBPrefix).stripSuffix(")").trim.stripPrefix("\"").stripSuffix("\"").replaceAllLiterally(" ", "")

          costsFromFacts.append(cost)

        } else if (isEval) {

          val evalFact = symbols(rule.headAtomsElis.head - 1)

          //println("Encountered cost definition fact in aspif input: " + costFact)

          if (evalFact.contains("\"?\"")) { // in case there is an _eval_ without "?", we just ignore it (treat it as a plain atom). This is important in case
            // a resolved _eval_ (i.e., where the "?" had been replaced with a number) is part of the input logic program.

            val (evalTerm, _) = aspIOutils.splitEvalSymbol(evalFact)

            evalsFromFacts.append(evalTerm)

          }

        }

      } else if (isPr || isPat || isCost || isEval)
        delSAT.stomp(-5004, symbols(rule.headAtomsElis.head - 1) + " found in rule head but body is not empty:\n " + rule.toString(symbols))

      rules.append(rule)

      aspifRulei += 1

    }

    if (showIntermediateTimers)
      println("parsetimer E5: " + timerToElapsedMs(timerParserNs) + " ms")

    val assumptionElis = assumptionAspifElis.map(aspifEli =>
      if (aspifEli >= 0)
        positiveAspifEliToPositiveEli(aspifEli)
      else
        negativeAspifEliToNegativeEli(aspifEli))

    if (verbose)
      println("aspif parsing time: " + timerToElapsedMs(timerParserNs) + " ms")

    val additionalUncertainAtomsInnerCostsStrs: (Array[String], Array[String], Array[String]) = if (ignoreParamVariablesR) (Array[String](), Array[String](), Array[String]()) else {

      import java.text.DecimalFormat
      import java.text.DecimalFormatSymbols
      import java.util.Locale

      val dFormat = new DecimalFormat("0", DecimalFormatSymbols.getInstance(Locale.ENGLISH)) // we need this to avoid unparsable scientific notation in double string literals

      dFormat.setMaximumFractionDigits(340)

      (probabilisticFacts.toArray.unzip._1 ++ patsFromFacts, probabilisticFacts.toArray.map((atomAndWeight: (String, Double)) => {

        //  we generate inner costs of the MSE type per each uncertain atom fact, e.g., (0.4-f(atom))^2

        "(" + dFormat.format(atomAndWeight._2) + "-f(" + atomAndWeight._1 + "))^2"

      }) ++ costsFromFacts, evalsFromFacts.toArray)

    }

    if (verbose) {

      println("Parameter atoms defined using _pr_ or _pat_ facts:\n" + additionalUncertainAtomsInnerCostsStrs._1.mkString(" "))

      println("Costs defined using _pr_ or _pat_ or _cost_ facts:\n" + additionalUncertainAtomsInnerCostsStrs._2.mkString("\n"))

    }

    (rules, noOfRealBlits, emptyBodyBlit, symbolToEli, additionalUncertainAtomsInnerCostsStrs, assumptionElis)

  }

}
