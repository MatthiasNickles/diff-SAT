/**
  * ASPIOutils
  *
  * Copyright (c) 2017-2018 Matthias Nickles
  *
  * THIS CODE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
  *
  */

import java.io._
import java.net.{URL, URLClassLoader}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, InvalidPathException, Paths}
import java.text.MessageFormat
import java.util.UUID
import java.util.jar.JarFile

import scala.collection.{Set, mutable}
import scala.collection.mutable.ArrayBuffer
import scala.io.BufferedSource
import scala.sys.process._
import scala.language.postfixOps
import scala.util.matching.Regex

// for asynchronous stream writing:
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future


package object ASPIOutils {

  type Pred = String

  type Model = Array[String]

  val parserInstanceCount = new java.util.concurrent.atomic.AtomicInteger(0)

  val auxPredPrefixBase = "__aux_" // prefixes for newly introduced atom symbols

  def isAuxAtom(pred: String) = pred.contains/*startsWith*/(auxPredPrefixBase)   // "contains" as pred could also be param(__aux...)

  /* The following kinds of auxiliary symbols are currently used in DelSAT, prasp2 and staspquery:

      - auxiliary atoms used to desugar :- constraints (symbol contains _F_)
      - helper atoms in automatically generated spanning formulas (symbol contains _R_)
      - for other purposes (symbol contains _O_)

      Also see hideAuxPreds in stasp_pkg.SampleOptimizeConfig !

   */

  def auxPredPrefix(kind: String) = ASPIOutils.auxPredPrefixBase + kind + "_" + parserInstanceCount.get() + "_"

  def newFalsePredsPrefix = auxPredPrefix("F")  // prefixes for newly introduced auxiliary atoms for desugaring :- constraints (see aspif parser).

  def isFalsAuxAtom(pred: String) = pred.startsWith(auxPredPrefixBase) && pred.contains("F")

  def newSpanAuxAtomPrefix = auxPredPrefix("R") // prefixes for newly introduced uncertain auxiliary atom symbols in spanning formulas

  def isSpanAuxAtom(pred: String) = isAuxAtom(pred) && pred.contains("R")

  def newLatentSymbolAuxAtomPrefix = auxPredPrefix("L") // prefixes for newly introduced auxiliary atom symbols for (re-)introduced atoms from certain #show aspif rules (see aspif parser).

  def isLatentSymbolAuxAtom(pred: String) = pred.startsWith(auxPredPrefixBase) && pred.contains("L")

  def newOtherAuxAtomPrefix = auxPredPrefix("O") // for all other newly introduced auxiliary atoms

  @inline def auxAtomSymbol(prefix: String, index: Int, encloseUncertainAuxWithParam: Boolean = false) = if(encloseUncertainAuxWithParam)
    "param_" + prefix + index else prefix + index

  def externalCmdWithInput(cmd: String,
                           sendToStdinOpt: Option[Either[String, Array[Byte]]],
                           redirectOutputToFileOpt: Option[File] = None):
  Option[(Seq[String] /*<- stdout from process*/ , Seq[String] /*<- captured stderr*/ )] = {

    val errLines = ArrayBuffer[String]()

    def pipe2external(cmd: String): Object = if(sendToStdinOpt.isEmpty && redirectOutputToFileOpt.isEmpty)
      cmd lineStream_! ProcessLogger(line => errLines.append(line))
    else if (sendToStdinOpt.isEmpty)
      (cmd lineStream_! ProcessLogger(line => errLines.append(line))) #> redirectOutputToFileOpt.get
    else if (redirectOutputToFileOpt.isDefined)
      (cmd #< iterator2inputStream(sendToStdinOpt) lineStream_! ProcessLogger(line => errLines.append(line))) #> redirectOutputToFileOpt.get
    else
      cmd #< iterator2inputStream(sendToStdinOpt) lineStream_! ProcessLogger(line => errLines.append(line))
    // note that some programs (such as Clingo) return non-zero codes
    // even when completing correctly; we use lineStream_! to prevent the process to throw an exception in these cases.

    def iterator2inputStream(sendToStdinOpt: Option[Either[String, Array[Byte]]]): InputStream = {

      val pos = new PipedOutputStream

      val pis = new PipedInputStream(pos)

      sendToStdinOpt.foreach(toStdin => {

        val ba: Array[Byte] = (toStdin.right.getOrElse(toStdin.left.get.getBytes()))

        Future { // we must do this asynchronously to avoid blocking for larger amounts of data

          pos.write(ba)

          pos.close

        }

      })

      /*Future { // we must do this asynchronously to avoid blocking for larger amounts of data

        /*inputLines.foreach { l => {

          pw.println(l)

          pw.flush()

        }
        } */

      }*/

      pis

    }

    val r = pipe2external(cmd)

    if (r.isInstanceOf[Seq[String]])
      Some((r.asInstanceOf[Seq[String]], errLines /*extStderr.toString("UTF-8").split('\n')*/ ))
    else
      None

  }

  def splitCommandLineStr(cmdStr: String): Seq[String] = {

    val regex = new Regex("\"(.*?)\"|([^\\s]+)")

    val matches = regex.findAllMatchIn(cmdStr).toList

    matches.map {
      _.subgroups.flatMap(Option(_)).fold("")(_ ++ _)
    }

  }

  /**
    * Dynamically adds jar and calls main-method.
    *
    */
  def externalJarMainCall(jarURL: URL, mainClassName: String, args: Array[String], sendToStdinOpt: Option[Either[String, Array[Byte]]]):
  Option[(Any /*return object of method called unless with a main from Java code, then we return 0 (from original null) */ ,
    String /*captured stdout*/ , String /*captured stderr*/ )] = {

    val systemStdin = System.in

    val systemStdout = System.out

    val extStdout = new ByteArrayOutputStream()

    System.setOut(new PrintStream(extStdout))

    val systemStderr = System.err

    val extStderr = new ByteArrayOutputStream()

    System.setErr(new PrintStream(extStderr))

    try {

      val loader: ClassLoader = URLClassLoader.newInstance(Array(jarURL), /*this.getClass <- no, since we want that DelSAT's
      diff.DifferentialFunctionFactoryStasp overrides the class with the same name in prasp2, we need to use an unrelated
       class loader*/ "".getClass.getClassLoader)

      val mainClass = Class.forName(mainClassName, true, loader)

      val mainMethod = mainClass.getDeclaredMethod("main", classOf[Array[String]])

      mainMethod.setAccessible(true)

      sendToStdinOpt.foreach(toStdin => System.setIn(new ByteArrayInputStream(toStdin.right.getOrElse(toStdin.left.get.getBytes()))))

      val r = mainMethod.invoke(loader, args)

      Some((if (r == null) 0 else r, extStdout.toString("UTF-8"), extStderr.toString("UTF-8")))

    } catch {

      case ite: java.lang.reflect.InvocationTargetException => {

        System.setErr(systemStderr)

        System.err.println("Error: Could not invoke method in external jar " + jarURL + ":\n " + {

          ite.getCause match {

            case c: java.util.concurrent.ExecutionException => c.getCause  //...

            case x => x

          }

          ite.getCause.printStackTrace

        })

        None

      }

      case t: Throwable => {

        System.setErr(systemStderr)

        System.err.println("Error: Could not add jar " + jarURL + " via classloader:\n " + t)

        None

      }

    } finally {

      System.setIn(systemStdin)

      System.setOut(systemStdout)

      System.setErr(systemStderr)

    }

  }

  def quoteCmdArgs(args: Seq[String]): Seq[String] = {

    args.map(arg => {

      val parg = arg.replaceAll("\"", "\\\\\"").replaceAll("'", "\\\\'")

      "\"" + parg + "\""

    }) // covers simple cases. NB: under Windows, single quotes cannot be used to protect args with double quotes.

  }

  def externalCallAsProcOrJar(toolR: String,
                              mainClassNameOpt: Option[String],
                              args: Array[String],
                              sendToStdinOpt: Option[Either[String, Array[Byte]]],
                              addArgForSysExitOmission: Boolean /* see below */):
  Option[(Any /*<- Should be ignored; returns object of method called unless with a main from Java code,
  then we return 0 (from original null) */ ,
    String /*captured stdout*/ , String /*captured stderr*/ )] = {

    if (isJarFileNameWithoutJava(toolR)) {

      val tool = toolR.trim.stripPrefix("\"").stripSuffix("\"").trim

      val mainClassName = mainClassNameOpt.getOrElse({

        val jf = new JarFile(new File(tool))

        val mncn = jf.getManifest().getMainAttributes().getValue("Main-Class")

        mncn

      })

      val url = if (tool.contains("file://")) tool else "file://" + tool

      val r = externalJarMainCall(new URL(url),
        mainClassName, (if (addArgForSysExitOmission) args :+ ("--omitSysExit0") else args), sendToStdinOpt)
      // omitSysExit0 because the tool must finish without an exit code (at least not in case of regular exits), as
      // otherwise the sys.exit would terminate the entire software.

      r


    } else {

      val r: (Seq[String], Seq[String]) = externalCmdWithInput(toolR + " " + quoteCmdArgs(args).mkString(" "),
        sendToStdinOpt = sendToStdinOpt,
        redirectOutputToFileOpt = None).getOrElse((Seq(), Seq())) // must finish with an exit code!

      Some((0, r._1.mkString("\n"), r._2.mkString("\n")))

    }

  }


  def getUniqueFileName(directory: String, extension: String): String = {

    Paths.get(directory, MessageFormat.format("{0}.{1}", UUID.randomUUID(), extension.trim())).toString()

  }

  def isFileName(n: String): Boolean = {

    if (n.endsWith("/") || n.endsWith("\\"))
      false
    else {

      try {

        Paths.get(n)

        true

      } catch {

        case _: InvalidPathException => false

      }

    }

  }

  def isJarFileNameWithoutJava(n: String): Boolean = {

    val stripped = n.trim.stripPrefix("\"").stripSuffix("\"").trim

    val r = stripped.endsWith(".jar") && (!stripped.contains("java ") || stripped.contains("file:/"))

    r

  }

  def readAllLinesFromStdIn: Iterator[String] = {

    scala.io.Source.stdin.getLines

  }

  def slurpBytesFromInputStream(in: InputStream, maxLen: Int = Int.MaxValue): ArrayBuffer[Byte] = {

    val byteArrayStep = new Array[Byte](4096)

    val byteBuf = ArrayBuffer[Byte]()

    byteBuf.sizeHint(4096)

    var bytesRead = 0

    while (byteBuf.length < maxLen && {

      bytesRead = in.read(byteArrayStep, 0, byteArrayStep.length.min(maxLen - byteBuf.length))

      bytesRead != -1

    }) {

      var i = 0

      while (i < bytesRead && byteBuf.length < maxLen) {

        byteBuf.append(byteArrayStep(i))

        i += 1

      }

    }

    byteBuf

  }

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

  def slurpLinesFromFile(fileName: String): Iterator[String] = {

    val source = scala.io.Source.fromFile(fileName)

    source.getLines()

    //try source.getLines() finally source.close()

  }

  def slurpFromFile(fileName: String): String = {

    new String(Files.readAllBytes(Paths.get(fileName)), StandardCharsets.UTF_8)

  }

  def writeStrToFile(fileName: String, contents: String) = {

    Files.write(Paths.get(fileName), contents.getBytes(StandardCharsets.UTF_8))

  }

  def concatenateFiles(fileNames: List[String]): Seq[String] = {

    fileNames.foldLeft({

      val b = ArrayBuffer[String]()

      b.sizeHint(5000)

      b

    }) { case (lines: ArrayBuffer[String], fileName: String) => {

      val fileSource: BufferedSource = scala.io.Source.fromFile(fileName)

      lines ++ fileSource.getLines()

    }
    }

  }

  def readLineFromInputStream(is: InputStream, encoding: String = "UTF8"): Option[String] = {

    val buffer = new ByteArrayOutputStream()

    var r = 0

    r = is.read

    while (r != '\n' && r != -1) {

      buffer.write(r)

      r = is.read

    }

    if (r == -1 && buffer.size == 0)
      None
    else
      Some(buffer.toString(encoding))

  }

  /**
    * Parses lines with answer sets or propositional assignments.
    *
    * @param lines the lines emitted by the solver
    * @return      an indexed sequence of models (either answer sets or propositional assignments (SAT-mode))
    */
  def extractModels(lines: IndexedSeq[String]): IndexedSeq[Model] = {

    var claspSATmode = false

    val modelsStrs: IndexedSeq[String] = lines.zipWithIndex.filter { case (line: String, index: Int) => {

      // (Notice that we couldn't use the numbers behind "Answer:" for anything, as with the clingo-python-based sampling backend, they are always "1")

      val lt = line.trim

      val sa = lt.startsWith("c Answer:")

      if(sa)
        claspSATmode = true

      sa || lt.startsWith("Answer:")

    }
    }.unzip._2.map(_ + 1).collect(lines)

    val x: IndexedSeq[Array[String]] = modelsStrs.map(_.trim.split(' '))  // TODO: replace split (slow!)

    val y = if (!claspSATmode)
      x
    else
      x.map(_.drop(1).dropRight(1))  // with clasp in SAT-mode, the output lines have form v a1 -a2 a3 ... 0
                                     // (whereas with DelSAT in SAT-mode, output lines have form a1 -a2 a3 ..., so we parse them just like answer sets)
    y

  }

  def extractNonNumSymbolsFromAspifLine(aspifLine: String): Set[Pred] = {

    var syms = Set[Pred]()

    if (aspifLine.startsWith("9 ") || aspifLine.startsWith("10 ") || aspifLine.startsWith("asp"))
      syms
    else {

      var i = 0

      var sym = ""

      var nesting = 0

      while (i < aspifLine.length) {

        val c: Char = aspifLine(i)

        if (c == '(')
          nesting += 1
        else if (c == ')')
          nesting -= 1

        if (nesting > 0 || c.isLetter || sym.length > 0 && c.isLetterOrDigit || c == '_' || c == '(' || c == ')')
          sym += c

        if (nesting == 0 && (!(c.isLetterOrDigit || c == '_') || i >= aspifLine.length - 1) && sym.length > 0) {

          syms = syms.+(sym.filterNot(_.isWhitespace))

          sym = ""

        }

        i += 1

      }

      syms.-("not")

    }

  }

  case class DisjRule(headPosAtoms: Set[Pred] = Set[Pred](), headNegAtoms: Set[Pred] = Set[Pred](),
                      bodyPosAtoms: Set[Pred] = Set[Pred](), bodyNegAtoms: Set[Pred] = Set[Pred](),
                      // ^ Not all possible combinations allowed by all sampling and querying approaches (most accept normal rules only!).
                      // If multiple head atoms, there semantics is disjunction.
                      weight: (Double, Double) = (1d, 1d),
                      var blit: Int = -1) {

    override def toString = {

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

  @inline def cleanupFormulaStr(formulaStr: String, keepNotProt: Boolean = false): String = {

    val formulaRemovedWs = if (!formulaStr.contains(' '))
      formulaStr
    else {

      val l = formulaStr.length

      val fn = new StringBuilder(l)

      var i = 0

      while (i < l) {

        val c = formulaStr(i)

        val space = c.isWhitespace

        if (!space)
          fn.append(c)
        else {

          val not = i >= 3 && formulaStr(i - 1) == 't' && formulaStr(i - 2) == 'o' && formulaStr(i - 3) == 'n' && (i <= 3 || !formulaStr(i - 4).isLetterOrDigit && formulaStr(i - 4) != '_') //&& space

          if (not) {

            if (keepNotProt)
              fn.append('§') // relict but still used somewhere
            else
              fn.append(' ')

          }
        }

        i += 1

      }

      fn.toString

    }

    val l = formulaRemovedWs.length

    if (l > 0 && formulaRemovedWs(l - 1) == '.')
      formulaRemovedWs.substring(0, l - 1) // tad faster than stripSuffix
    else
      formulaRemovedWs

  }

  /**
    * Callers of this function should expect false positives (e.g., for Gringo 3 ASP rules with disjunction in head).
    * However, for Gringo >=4, it should do.
    *
    */
  @inline def likelyFOL(f: String): Boolean = {

    !f.contains(":-") && ((f.contains("&") || f.contains("![") || f.contains("?[")
      || f.contains("->") || f.contains("<-") || f.contains("|") || f.trim.startsWith("not ") || f.trim.startsWith("(")))

  }

  @inline def containsSpecialASPconstructs(fASP: String): Boolean = {

    fASP.contains("{") || (fASP.contains("[") || fASP.replaceAllLiterally(":-", "").contains(":")) && !fASP.contains("]:") || fASP.contains("#") ||
      fASP.contains("..") || fASP.contains(";") || fASP.contains("|")

  }

  val varPattern = """\W(_*[A-Z][A-Za-z0-9_]*)""".r

  @inline def containsVars(f: String): Boolean = {

    // Gringo-style variable names (additional allows _ at pos>0)

    varPattern.findFirstIn(f).isDefined

  }

  @inline def isGround(f: String) = !containsVars(f)

  /**
    * Parses ASP rule into head and tail-literals. Literals can be aggregates or ranges, these are not touched.
    */
  @inline def headTailLitsASPrule(ruleASPstr: String, ruleOp: String, andOp: String = ",", addFalse: Boolean = false): (String, List[String]) = {

    val ff = cleanupFormulaStr(ruleASPstr)

    if (!ff.contains(ruleOp))
      (ff, Nil)
    else {

      val headTail = ff.split(ruleOp) // TODO: replace split (slow!)

      val head = if (addFalse && headTail(0).trim == "") "false" else headTail(0)

      val tail = headTail(1)

      val tLits = tail.foldLeft((0, List[String](""))) {
        case ((level, h :: t), c) => {

          if (c == '(' || c == '{' || c == '[')
            (level + 1, (h + c) :: t)
          else if (c == ')' || c == '}' || c == ']')
            (level - 1, (h + c) :: t)
          else if (level == 0 && c == andOp(0))
            (level, "" :: h :: t)
          else
            (level, (h + c) :: t)

        }
      }._2

      (head, tLits)

    }

  }

  @inline def getQueryCondition(wStr: String): Option[String] = {

    val x: Array[String] = wStr.trim.split("""\?+(\s*)\|""") // we split at ?| or ??| but not at FOL disjunction symbol |

    assert(x.length <= 2 && x.length >= 1, "Error: Invalid weight: " + wStr)

    if (x.length <= 1) None else Some(x(1))

  }


  def isDIMACS(lines: Seq[String]): Boolean = {

    val firstLine = lines.find(!_.trim.isEmpty).getOrElse("").trim

    firstLine.startsWith("p cnf") || firstLine.startsWith("c ")

  }

  def aspParseGroundNormalRule(ruleASPgroundNormalStr: String): DisjRule = {

    val x: (String, List[String]) = headTailLitsASPrule(ruleASPgroundNormalStr, ":-")

    val rule: (String /*head*/ , List[String]) = x

    val (bodyPosAtoms, bodyNegLits) = rule._2.partition(!_.startsWith("not "))

    DisjRule(if (rule._1.trim.isEmpty) Set() else Set(rule._1.filterNot(_.isWhitespace)),
      Set[Pred]() /*we currently don't yet support negation in head*/ ,
      Set[Pred]().++(bodyPosAtoms.map(_.filterNot(_.isWhitespace))),
      Set[Pred]().++(bodyNegLits.map(_.stripPrefix("not").filterNot(_.isWhitespace))))

  }

  @inline def linesTrimmed(s: String): List[String] = {

    s.linesWithSeparators.map(_.trim).toList  // because of name clash of Scala's lines with JDK 11 lines method

  }

  @inline def arrayFilter(a: Array[Int], pred: (Int => Boolean)): Array[Int] = {

    val b = new mutable.ArrayBuilder.ofInt

    var i = 0

    while(i < a.length) {

      val e = a(i)

      if(pred(e))
        b += e

      i += 1

    }

    b.result()

  }

  @inline def arrayMaxBy(a: Array[Int], by: (Int => Double), shuffle: Boolean = false, rdg: java.util.Random = null): Int = {

    var max = Double.MinValue

    var maxI = -1

    var i = 0

    while(i < a.length) {

      val b = by(a(i)) - (if(shuffle && rdg.nextBoolean) Double.MinPositiveValue else 0d)

      if(b > max) {

        max = b

        maxI = i

      }

      i += 1

    }

    maxI

  }

  @inline def splitByRepChar(s: String, delim: Char = ' ') = {

    val ll = new mutable.ArrayBuilder.ofRef[String]

    var index = 0

    var i = 0

    val sl = s.length

    while (i < sl) {

      if (s.charAt(i) == delim) {

        ll.+=(s.substring(index, i))

        i = i + 1

        while(s.charAt(i) == delim) { // e.g., "token1  token2" gives ["token1", "token2"], not ["token1", " ", "token2"]

          i += 1

        }

        index = i

      }

      i += 1

    }

    if(s.last != delim)
      ll.+=(s.substring(index))

    ll.result()

  }

}