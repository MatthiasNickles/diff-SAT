/**
  * DelSAT
  *
  * A tool for differentiable satisfiability and differentiable answer set programming
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  */

import utils.{IntArrayUnsafe, XORShift32}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ArrayBuilder}

import scala.reflect.ClassTag

package object sharedDefs {

  // Solver settings ------------------------------------------------------------------------------------------------------

  // Important: given the primary use case of DelSAT (sampling and multi-model optimisation), the following settings are
  // geared towards fast solving of small or medium satisfiable problems. UNSAT and many larger problems can also be solved but
  // might require different settings (e.g., recAssg = false, higher amount of removed nogoods, other freeEliSearchApproachesR, ...).

  val specialConstrRuleNogoods: Boolean = false // TODO: must be false (true doesn't work yet); if true, we create an alternative form of nogoods for :- constraints (see code)

  val generatePseudoRulesForNogoodsForSATMode = false // Experimental. Generates blits in SAT mode

  val initShuffleCleanUpClarkNogoods: Boolean = false

  val variableElimConfig = (false /*on/off*/ , 0d /*amount #resolvents can be larger than original nogood set for candidate variable, in % of nogis */ ,
    0d /*#literals in original nogood set can be larger than literals in resolvents, in % of literals */ ,
    0.05f /*maximum product of literals with positive or negative occurrence of variable candidate, in % of all literals*/ ,
    false /*true actually removes eliminated variables (instead of just ignoring them). Only for SAT mode, not fully working yet*/ )

  assert(!generatePseudoRulesForNogoodsForSATMode || !variableElimConfig._5 || !variableElimConfig._1)

  val prearrangeEliPoolR: Boolean = false // true arranges branching eli pool initially by number of nogoods with eli. For freeEliSearchApproachesR = 0, 2, 4, 5

  val restartTriggerConf = (true /*Geometric seq on/off*/ , -1 /*initial cutoff. -1: auto, -2: no restarts*/ ,
    -1.5d /*base (if geometric) or cutoff as #conflicts since prev restart as % of learned nogoods. Negative: normally distributed closely around -x*/ )

  val removeLearnedNogoods: Double = 0.1d // factor, per restart. 0d: no removal of learned nogoods

  val freeEliSearchApproachesR = Seq(3) //Seq(4,0,3,6,4,2,4,5) // 0<= item <=6, except 1(not implemented); parallel approaches if maxNumberOfCompetingModelSearchThreads>0. If there is
  // just one portfolio solver thread (see below), head is used. Duplicates allowed.
  // Recommendations: For larger problems, try with approaches 4, 3 and 2 first. For small problems, try with 0, 5 and 6 first.

  val maxNumberOfCompetingModelSearchThreads = 1 // for portfolio solving with competing solver instances (number of threads not guaranteed)

  var diversify: Boolean = false // if true, solver aims at generating diverse models (might slow down solver)

  var recAssg = false // true (experimental) omits the intermediate heap data structure for unit props and makes assignments directly and recursively. You
  // might have to increase stack size for that when calling java, e.g., -Xss5m ...
  // true is often much faster for small or medium problems, whereas false scales better for larger problems.

  var candEliCheckCapFacR: Double = 1d // caps number of checks at x% with freeEliSearchApproaches 0, 1, 4. 1d = no capping

  val sortRemainderPoolProb = 0f

  val initialActivUpdateValue: Int = 1

  val incActivUpdateValueOnNewNogoodFactor: Int = 2 // 1 = no activUpdateVal increases (activUpdateVal remains always initialActivUpdateValue).

  val reviseActivFreq = 1 // every x conflicts

  val reviseActivDiv = 4 // 1 = no updates

  val arrangeParamElisInEliPool = false

  val shuffleNogoodsOnRestart = false

  val nogoodExchangeProbability = 0f // exchange of nogoods between solver threads. 0f = no exchange

  val nogoodExchangeSizeThresh = 4 // only nogoods with size below that threshold are copied to other threads

  val beliThR: Float = -1f //-1: auto

  val parallelThresh = 400 // used as number of items threshold for loop parallelization in various places (TODO: auto)

  var partDerivComplete = false // false: variant of ILP'18 approach (less general, use with MSE-style inner cost expressions),
  // true: variant of PLP'18 approach (more general)

  val ignoreParamVariables = false // true ignores cost function and parameter/measured atoms. Cost is always assumed to be
  // negative infinity. Not required as such for non-probabilistic problems (you could simply set threshold = Double.MaxValue
  // and use -1 as number of models), but useful for debugging.

  assert(maxNumberOfCompetingModelSearchThreads == 1 || ignoreParamVariables, "Error: competing solving currently not usable in uncertainty sampling mode")
  // (^ restriction planned to be dropped in a future version)

  // ------------------------------------------------------------------------------------------------------------------------

  var omitSysExit0 = false // If this .jar is dynamically included in prasp2 using classloader, we must not sys.exit in case of successful termination (except -v/-h), as this
  // would quit the overall program. We could prevent this issue using some additional wrapper method, but we want to keep prasp2 compatible with Java tools other than this.
  // If on the other hand the tool is invoked as an external process, sys.exit(0) is required.

  def overrideSolverArgs(additionalSolverArgsR: mutable.HashMap[String, String]) = { // preliminary, TODO

    val additionalSolverArgs = additionalSolverArgsR.map((tuple: (String, String)) => (tuple._1.replaceAllLiterally("\"", "").trim, tuple._2.replaceAllLiterally("\"", "").trim))

    additionalSolverArgs.foreach {

      case ("partDerivComplete", value: String) => partDerivComplete = value.toBoolean

      case ("recAssg", value: String) => recAssg = value.toBoolean

      case ("diversify", value: String) => {

        diversify = value.toBoolean
      }

      // ...

      case (arg: String, value: String) => System.err.println("Invalid --solverarg " + arg + " " + value)

    }

  }


  // --------------------------------------------------------------

  type Eli = Int

  type Nogi = Int

  final case class Rule(headAtomsElis: Array[Eli],
                        bodyPosAtomsElis: Array[Eli],
                        bodyNegAtomsElis: Array[Eli],
                        posBodyEli: Eli) {}

  val newAspifEliOffsets = 5000000

  val newAspifEliBoundary = Int.MaxValue - newAspifEliOffsets * 3

  val aspifExtraShowEliBoundary = newAspifEliBoundary

  val extraShowAspifElitCount = new java.util.concurrent.atomic.AtomicInteger(0)

  val aspiEliForAuxSymbolForSpanningBoundary = aspifExtraShowEliBoundary + newAspifEliOffsets

  val newFalseAspifElisBoundary = aspiEliForAuxSymbolForSpanningBoundary + newAspifEliOffsets

  val newFalsePredsCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  def isNewFalsePosAspifEli(aspifEli: Int) = aspifEli >= newFalseAspifElisBoundary

  final case class AspifOrDIMACSPlainParserResult(symbols: Array[String],
                                                  rulesOrClauseNogoods: Either[
                                                    /*from aspif:*/ ArrayBuffer[Rule],
                                                    /*from DIMACS:*/ ArrayBuffer[Array[Eli]]],
                                                  noOfPosBlits: Int,
                                                  externalAtomElis: Seq[Eli], // for aspif only
                                                  emptyBodyBlit: Int = -1,
                                                  directClauseNogoodsOpt: Option[ArrayBuffer[Array[Eli]]] = None /*for debugging/crosschecks*/ ,
                                                  clauseTokensOpt: Option[Array[Array[Int]]]
                                                 ) {}

  val rngGlobal: java.util.Random = new XORShift32() // not thread-safe

  @inline def shuffleArrayBlocked[A](arr: mutable.Seq[A], rg: java.util.Random): Unit = { // Blocked Fisher-Yates shuffle
    // (based on public domain code from https://github.com/lemire/Code-used-on-Daniel-Lemire-s-blog)

    def swap(i: Int, j: Int) = {

      val tmp = arr(i)

      arr(i) = arr(j)

      arr(j) = tmp

    }

    val size = arr.length

    val block = 1024

    val buffer = Array.ofDim[Int](block)

    var i = size

    while (i > block + 1) {

      var k = 0

      while (k < block) {

        buffer(k) = rg.nextInt(i - k)

        k += 1

      }

      k = 0

      while (k < block) {

        swap(i - 1 - k, buffer(k))

        k += 1

      }

      i -= block

    }

    while (i > 1) {

      swap(i - 1, rg.nextInt(i))

      i -= 1

    }

  }

  @inline def shuffleArray[A](array: mutable.Seq[A], rg: java.util.Random, to: Int = -1): Unit = { // plain Fisher-Yates shuffle

    if (to < 0 && array.length >= 16384)
      shuffleArrayBlocked[A](array, rg)
    else {

      val l = if (to < 0) array.length - 1 else to

      var i = l

      while (i > 0) {

        val j = rg.nextInt(i + 1)

        val temp = array(j)

        array(j) = array(i)

        array(i) = temp

        i -= 1

      }

    }

  }

  @inline def shuffleArray[A](array: IntArrayUnsafe, rg: java.util.Random): Unit = { // plain Fisher-Yates shuffle

    var i: Long = array.size - 1

    while (i > 0l) {

      val j = rg.nextInt(i.toInt + 1)

      val temp = array.get(j)

      array.update(j, array.get(i))

      array.update(i, temp)

      i -= 1

    }

  }

  type ArrayEliUnsafe = IntArrayUnsafe

  class ArrayValExtensible[T: Numeric : ClassTag](var buffer: Array[T]) { // our low-level non-boxing replacement for
    // a growable-only ArrayBuffer. Similar to ArrayBuilder, but with random access and traversal.
    // NB: buffer may be modified, so before calling constructor, clone if necessary.

    var l = buffer.length // generally, buffer contains items only up to index l-1, which might be less than buffer.length-1

    var incSize = l / 4

    @inline def setContent(content: Array[T]) = {

      buffer = content

      l = buffer.length

    }

    @inline def getContent = {

      buffer.take(l)

    }

    @inline def getContentExceptInt(except: Int) = {

      val ab = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val item = buffer(i).asInstanceOf[Int]

        if (item != except)
          ab += item

        i += 1

      }

      ab.result()

    }

    @inline def length = l

    @inline def bufferSize = buffer.length

    @inline def get(index: Int): T = buffer(index)

    @inline def traverseUntil(itemOp: T => Boolean) = {

      var i = 0

      var stop = false

      while (!stop) {

        stop = i >= l || itemOp(buffer(i))

        i += 1

      }

    }

    @inline def count(pred: T => Boolean): Int = {

      var i = l - 1

      var count = 0

      while (i >= 0) {

        if (pred(buffer(i)))
          count += 1

        i -= 1

      }

      count

    }

    @inline def append(item: T) = {

      //val zero: T = implicitly[Numeric[T]].zero

      if (l >= buffer.length) {

        val newContent: Array[T] = Array.ofDim[T](l + incSize)

        incSize += 100

        Array.copy(buffer, 0, newContent, 0, buffer.length)

        buffer = newContent

      }

      buffer(l) = item

      l += 1

    }

    @inline def removeItem(item /*not an index*/ : T): Int /*Index of removed item (only the first occurrence is considered), or -1 */ = {

      var indexOfItem = -1

      var i = 0

      while (i < l && indexOfItem == -1) {

        if (buffer(i) == item)
          indexOfItem = i

        i += 1

      }

      if (indexOfItem >= 0) {

        System.arraycopy(buffer, indexOfItem + 1, buffer, indexOfItem, l - 1 - indexOfItem)

        l -= 1

      }

      indexOfItem

    }

    @inline def removeIntItemsRange(from: Int /*first item, not an index!*/ , to: Int): Unit = {

      val bld: ArrayBuilder.ofInt = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val bi = buffer(i).asInstanceOf[Int]

        if (bi < from || bi > to)
          bld.+=(bi)

        i += 1

      }

      buffer = bld.result().asInstanceOf[Array[T]]

      l = buffer.length

    }


  }

  class ArrayValExtensibleIntUnsafe(var buffer: IntArrayUnsafe) { // our unsafe low-level non-boxing replacement for
    // a growable-only ArrayBuffer. Similar to ArrayBuilder, but with random access and traversal.
    // NB: buffer may be modified, so before calling constructor, clone if necessary.

    def this(bufferA: Array[Int], c: Boolean = false, setFromBufferR: Boolean = true) {

      this(new IntArrayUnsafe(bufferA.length))

      if (setFromBufferR)
        buffer.setFromIntArray(bufferA)

      //this(buffer)

    }

    val incSize = 100

    var l = buffer.size() // generally, buffer contains items only up to index l-1, which might be less than buffer.length-1

    @inline def setContent(content: Array[Int]) = {

      buffer.setFromIntArray(content)

      l = buffer.size()

    }

    @inline def getContent: Array[Int] = {

      buffer.toArray().take(l)

    }

    @inline def getContentExceptInt(except: Int) = {

      val ab = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val item = buffer.get(i)

        if (item != except)
          ab += item

        i += 1

      }

      ab.result()

    }

    @inline def getContentUnsafeExceptInt(except: Int): ArrayEliUnsafe = {

      val ab = new ArrayEliUnsafe(length)

      var i = 0

      var j = 0

      while (i < l) {

        val item = buffer.get(i)

        if (item != except) {

          ab.update(j, item)

          j += 1

        }

        i += 1

      }

      ab.size_ = j

      ab

    }

    @inline def length = l

    @inline def bufferSize = buffer.size()

    @inline def get(index: Int): Int = buffer.get(index)

    @inline def get(index: Long): Int = buffer.get(index)

    @inline def traverseUntil(itemOp: Int => Boolean) = {

      var i = 0

      var stop = false

      while (!stop) {

        stop = i >= l || itemOp(buffer.get(i))

        i += 1

      }

    }

    @inline def contains(item: Int, until: Int): Boolean = {

      var i = until - 1

      while (i >= 0) {

        if (buffer.get(i) == item)
          return true

        i -= 1

      }

      false

    }

    @inline def append(item: Int) = {

      //val zero: T = implicitly[Numeric[T]].zero

      if (l >= buffer.size()) {

        buffer = buffer.clone(incSize)

      }

      buffer.update(l, item)

      l += 1

    }

    @inline def removeIntItemsRange(from: Int /*first item, not an index!*/ , to: Int): Unit = {

      val bld: ArrayBuilder.ofInt = new mutable.ArrayBuilder.ofInt

      var i = 0

      while (i < l) {

        val bi = buffer.get(i)

        if (bi < from || bi > to)
          bld.+=(bi)

        i += 1

      }

      val a = bld.result()

      buffer = new IntArrayUnsafe(a.length)

      buffer.setFromIntArray(a)

      l = a.length

    }

  }

}
