/**
  * diff-SAT
  *
  * Copyright (c) 2018, 2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

import java.io._

import sharedDefs.evalFactPrefix

import scala.collection.{Set, mutable}
import scala.language.postfixOps

package object aspIOutils {

  type Pred = String

  type Model = Array[String]

  val parserInstanceCount = new java.util.concurrent.atomic.AtomicInteger(0)

  val auxPredPrefixBase = "__aux_" // prefixes for newly introduced atom symbols

  def isAuxAtom(pred: String) = pred.contains /*startsWith*/ (auxPredPrefixBase) // "contains" as pred could also be param(__aux...)

  /* The following kinds of auxiliary symbols are currently reserved:

      - auxiliary atoms used to desugar :- constraints (symbol contains _F_)
      - helper atoms in automatically generated spanning formulas (symbol contains _R_)
      - for other purposes (symbol contains _O_)

   */

  def auxPredPrefix(kind: String) = auxPredPrefixBase + kind + "_" + parserInstanceCount.get() + "_"

  def newFalsePredsPrefix = auxPredPrefix("F") // prefixes for newly introduced auxiliary atoms for
  // desugaring :- integrity constraints (see aspif parser).

  def isFalsAuxAtom(pred: String) = pred.startsWith(auxPredPrefixBase) && pred.contains("F")

  def isSpanAuxAtom(pred: String) = isAuxAtom(pred) && pred.contains("R")

  def newLatentSymbolAuxAtomPrefix = auxPredPrefix("L") // prefixes for newly introduced auxiliary atom symbols for (re-)introduced atoms from certain #show aspif rules (see aspif parser).

  def newSpanSymbolAuxAtomPrefix = auxPredPrefix("R") // prefixes for newly introduced auxiliary atom symbols for (re-)introduced atoms from certain #show aspif rules (see aspif parser).

  def isLatentSymbolAuxAtom(pred: String) = pred.startsWith(auxPredPrefixBase) && pred.contains("L")

  // TODO(?): ^ these don't consider auxiliar variables introduced by the PCNF parser (probabilistic SAT)

  @inline def auxAtomSymbol(prefix: String, index: Int, encloseUncertainAuxWithParam: Boolean = false) = if (encloseUncertainAuxWithParam)
    "param_" + prefix + index else prefix + index

  def slurpFromInputStream(in: InputStream): String = {

    val byteArray = new Array[Byte](4096)

    val strBuf: StringBuilder = new StringBuilder()

    var bytesRead = 0

    while ( {

      bytesRead = in.read(byteArray, 0, byteArray.length)

      bytesRead != -1

    }) strBuf.append(new String(byteArray, 0, bytesRead))

    strBuf.toString()

  }

  case class DisjRule(headPosAtoms: Set[Pred] = Set[Pred](), headNegAtoms: Set[Pred] = Set[Pred](),
                      bodyPosAtoms: Set[Pred] = Set[Pred](), bodyNegAtoms: Set[Pred] = Set[Pred](),
                      // ^ Which rule types are actually supported depends of course on solver and its preprocessor.
                      // If multiple distinct head atoms are given, their semantics is disjunction.
                      weight: (Double, Double) = (1d, 1d),
                      var blit: Int = -1) {

    @deprecated override def toString = {

      val endDot = if (headPosAtoms.isEmpty || !headPosAtoms.head.contains('[')) "." else ""
      // ^ hack to allow for Clingo softconstraint weights within formulas (which have [weight ...] after the dot).

      val r = headPosAtoms.mkString(",") + headNegAtoms.map("not " + _).mkString(",") + (if (bodyPosAtoms.isEmpty && bodyNegAtoms.isEmpty) "" else " :- " + (bodyPosAtoms ++ bodyNegAtoms.map("not " + _)).mkString(",")) + endDot

      val rr = (if (weight != (1d, 1d))
        "[" + weight._1 + ";" + weight._2 + "] "
      else
        "") + r

      rr.trim

    }

  }

  @inline def splitByRepChar(s: String, delim1: Char = ' ', delim2: Char = '\t'): Array[String] = {

    val ll = new mutable.ArrayBuilder.ofRef[String]

    var index = 0

    var i = 0

    val sl = s.length

    var inStr = false

    while (i < sl) {

      if(s.charAt(i) == '\"' && (i == 0 || s.charAt(i - 1) != '\\' || (i > 1 && s.charAt(i - 2) == '\\'))) {

        inStr = !inStr

        i += 1

      } else if (!inStr && s.charAt(i) == delim1 || s.charAt(i) == delim2) {

        ll.+=(s.substring(index, i))

        i += 1

        while (s.charAt(i) == delim1 || s.charAt(i) == delim2) { // e.g., "token1  token2" gives ["token1", "token2"], not ["token1", " ", "token2"]

          i += 1

        }

        index = i

      }

      i += 1

    }

    if (s.last != delim1 && s.last != delim2)
      ll.+=(s.substring(index))

    val r = ll.result()

    r

  }

  def splitEvalSymbol(sym: Pred) = {

    //val isTermQuoted = sym.startsWith(evalFactPrefix + "(\"")

    val endOfTermIndex = sym.indexOf(",\"?\"")

    // note that the term can be quoted or not

    val term = sym.take(endOfTermIndex).stripPrefix(evalFactPrefix).dropWhile(c => c == '(' || c == '\"').stripSuffix("\"").replaceAll("\\s", "")

    val remainder = sym.drop(endOfTermIndex + 4)

    (term, remainder)

  }

}
