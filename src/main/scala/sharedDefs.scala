/**
  * DelSAT
  *
  * Copyright (c) 2018 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE
  *
  */

import commandline.delSAT
import utils.{IntArrayUnsafe, LongArrayUnsafe, XORShift32}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ArrayBuilder}
import scala.reflect.ClassTag

package object sharedDefs {

  // ************* Solver settings. From the delSAT commandline, most of these can be set using
  // --solverarg "paramName" "paramValue(s)"
  // Each --solverarg sets only a single parameter.

  // NB: given the primary use case of DelSAT (sampling and multi-model optimisation), the following settings are
  // geared towards solving of small or medium satisfiable problems. Many other problems can also be solved but
  // may require different settings (e.g., larger amount of removed nogoods, different freeEliSearchConfigsP order, ...).

  var showProgressStats = false // Note: true causes some delay in the solving progress

  var restartTriggerConf = (true /*Geometric seq on/off*/ , -1 /*initial cutoff. -1: auto, -2: no restarts*/ ,
    -1.5d /*base (if geometric) or cutoff items (see code) since prev restart as % of learned nogoods.
    Negative: normally distributed closely around -x*/ , -1 /*enforce restarts every x ms (disable with -1)*/ )
  // ^ On the commandline, specify like this: --solverarg "restartTriggerConf" "true 5 1.4"

  var skipNogisHTElisInBCP = false // false is typically faster with our non-standard variant of CDNL and true isn't parallelized

  var removeLearnedNogoods: Double = 1d // if > 0, removes sqrt(#learnedNogoods)*x learned nogoods at each restart (but minimum 1).
  // 0d: no removal of learned nogoods. Even small values can make a difference as they shuffle the problem

  // The following settings ending with "...P" are for parallel portfolio solving (see maxCompetingSolverThreadsR) - each
  // solver thread is assigned a combination of values from the respective sequences.
  // With a limited number of solver threads, values earlier in sequences get higher priority to be used by a solver thread.

  var freeEliSearchConfigsP = Seq(3, 2, 5, 1, 7, 8, 6, 0) // 0<= item <=8; parallel free eli search (branching) configurations if maxCompetingSolverThreads>0.
  // Sequence order determines priority. If there is just one portfolio solver thread (see below), head is used.
  // Duplicates allowed!
  // On the commandline, use like this: --solverarg "freeEliSearchConfigsP" "1 2 8 3 0 1" (not that this doesn't specify the
  // number of solver threads which has to be set using maxCompetingSolverThreadsR)

  var prearrangeEliPoolP: Seq[Int] = Seq(0, 1) // per solver thread; 0=off, 1=upwards, 2=downwards, 3=shuffle, 4=(0,1,2 or 3 picked at random) per each solver thread. Arranges branching eli pool initially by number of nogoods with eli (relevant where the freeEliSearchApproach chooses from a sequence of elis)

  var rndmBranchP: Seq[Float] = Seq(0.0001f, 0.1f) // per solver thread; with probability x select the next branching literal purely randomly
  // (instead of using one of the heuristics in freeEliSearchConfigsP). Each parallel solver thread uses one x out of the given list.
  // -x uses a kind of "burst" approach where probability -x is active for periods alternating with (longer) periods of low probability otherwise.

  var noHeapP: Seq[Int] = Seq(1) // per solver thread; 0/1 off/on. "On" omits the intermediate heap data structure for
  // BCP (unit propagations) and makes assignments directly and recursively.
  // You might have to increase stack size for that when calling java, e.g., -Xss5m ...
  // "On" is typically the best choice for DelSAT's main use case (sampling), as it is often much faster for small or medium problems,
  // whereas "Off" sometimes(!) (not clear when exactly) scales better for large problems.

  var maxCompetingSolverThreadsR: Int = -1 // for portfolio solving with competing solver instances (number of threads not guaranteed)
  // Keep in mind that the machine might decrease maximum core frequencies with more cores being utilized.
  // -1: auto (sets number of solver threads in dependency of number of cores and other factors).
  // NB: DelSAT also spawns some parallelism from within individual solver threads.

  var switchToBestConfig: Int = 2 // if >0, the portfolio approach which was fastest in the first sampling round is used
  // exclusively (if 1, single threaded then, if 2, still competing using multiple threads if maxCompetingSolverThreads > 1) for
  // all further model solving.

  var abandonThreadsThatFellBehind: Boolean = true // if true, solver threads which fell behind competing solver threads
  // are aborted, giving any remaining threads more computation time. Can be used to work with larger maxCompetingSolverThreadsR.

  var savePhasesR: Boolean = true // true overridden by diversify

  var diversify: Boolean = false // if true, solver aims at generating diverse models (might slow down solver, might override other settings)

  var resolveFactsInitially = false // Note: true isn't necessarily faster

  var initialActivBaseValue: Float = 1.05f // 1f = no updates. Must be >0

  var reviseActivFreq = 10 // every x conflicts

  var reviseActivFact: Float = 0.25f // 1f = no rescaling

  var nogoodExchangeProbability = 0.01f // exchange of learned nogoods between solver threads. 0f = no exchange

  var nogoodExchangeSizeThresh = 5 // only learned nogoods with size below that threshold are copied to other threads

  var localSolverParallelThreshR = 500 // localSolverParallelThreshMax: off.
  // Used (with various factors) as #items threshold for loop parallelization in various places (TODO: auto).
  // Overridden by skipNogisHTElisInBCP

  var partDerivComplete = false // false: variant of ILP'18 approach (less general, use with MSE-style inner cost expressions),
  // true: variant of PLP'18 approach (more general)

  var ignoreParamVariables = false // true ignores cost function and parameter/measured atoms. Cost is always assumed to be
  // negative infinity. Not required as such for non-probabilistic problems (you could simply set threshold = Double.MaxValue
  // and use -1 as number of models), but useful for debugging.

  var noOfUnfolds = 0 // for translating away disjunctions in ASP rule heads (an extension over normal ASP), increase the number of unfold operations
  // if necessary (try with 0 first, unless you need the full set of answer sets)

  var variableOrNogoodElimConfig = (false /*on/off*/ , 0d /*amount #resolvents can be larger than original nogood set for candidate variable, in % of nogis */ ,
    0d /*#literals in original nogood set can be larger than literals in resolvents, in % of literals. NB: total #literals can
    still become larger than original total #literals even with 0d here*/ ,
    0.2f /*maximum product of literals with positive or negative occurrence of variable candidate, in % of sqrt(all literals)*/ ,
    false /*true materially removes eliminated variables (instead of just ignoring them) <- only for SAT mode, not fully working yet*/ )
  // On the commandline, use like this: --solverarg "variableOrNogoodElimConfig" "true 0.5 0.5 0.001 false"

  var genBodyLitsFromSATClauses: Double = 0d // experimental. Generates "body literals" (blits) in SAT mode, for x% of all
  // variables. If 1d, we completely replace the original clause nogoods with an equivalent theory using blits.
  // Can easily blow up space.

  val initCleanUpSortClarkNogoods: Boolean = true // internal; leave at true

  val shuffleNogoodsOnRestart = false // experimental, leave at false

  val omitSingletonBlits = true // internal; leave at true

  checkSettings

  // *****************************************************************************************************************

  def checkSettings = {

    if (!(
      (!resolveFactsInitially || initCleanUpSortClarkNogoods) &&
        (!skipNogisHTElisInBCP || noHeapP == Seq(1)) &&
        (!shuffleNogoodsOnRestart || noHeapP == Seq(0))

      ))
      delSAT.stomp(-5006)

  }

  val localSolverParallelThreshMax = 99999999 // (we use this value just so to be able to multiply by small ints without overflow)

  var omitSysExit0 = false // If this .jar is dynamically included in prasp2 using classloader, we must not sys.exit in case of successful termination (except -v/-h), as this
  // would quit the overall program. We could prevent this issue using some additional wrapper method, but we want to keep prasp2 compatible with Java tools other than this.
  // If on the other hand the tool is invoked as an external process, sys.exit(0) is required.

  def overrideSolverArgs(additionalSolverArgsR: mutable.HashMap[String, String]) = {

    delSAT.log("additionalSolverArgsR = " + additionalSolverArgsR)

    val additionalSolverArgs = additionalSolverArgsR.map((tuple: (String, String)) => (tuple._1.replaceAllLiterally("\"", "").trim, tuple._2.replaceAllLiterally("\"", "").trim))

    additionalSolverArgs.foreach { case (paramName, paramValueStr) => { // see above for meaning of these parameters

      (paramName, paramValueStr.split("\\s+")) match {

        case ("showProgressStats", Array(v1)) => showProgressStats = v1.toBoolean

        //case ("initCleanUpSortClarkNogoods", Array(v1)) => initCleanUpSortClarkNogoods = v1.toBoolean

        case ("variableOrNogoodElimConfig", Array(v1, v2, v3, v4, v5)) => variableOrNogoodElimConfig = (v1.toBoolean, v2.toDouble, v3.toDouble, v4.toFloat, v5.toBoolean)

        case ("prearrangeEliPoolP", Array(v@_*)) => prearrangeEliPoolP = v.map(_.toInt)

        case ("restartTriggerConf", Array(v1, v2, v3, v4)) => restartTriggerConf = (v1.toBoolean, v2.toInt, v3.toDouble, v4.toInt)

        case ("skipNogisHTElisInBCP", Array(v1)) => skipNogisHTElisInBCP = v1.toBoolean

        case ("freeEliSearchConfigsP", Array(v@_*)) => freeEliSearchConfigsP = v.map(_.toInt)

        case ("rndmBranchP", Array(v@_*)) => rndmBranchP = v.map(_.toFloat)

        case ("savePhasesR", Array(v1)) => savePhasesR = v1.toBoolean

        case ("maxCompetingSolverThreadsR", Array(v1)) => maxCompetingSolverThreadsR = v1.toInt

        case ("switchToBestConfig", Array(v1)) => switchToBestConfig = v1.toInt

        case ("abandonThreadsThatFellBehind", Array(v1)) => abandonThreadsThatFellBehind = v1.toBoolean

        case ("localSolverParallelThreshR", Array(v1)) => localSolverParallelThreshR = v1.toInt

        case ("partDerivComplete", Array(v1)) => partDerivComplete = v1.toBoolean

        case ("noHeapP", Array(v@_*)) => noHeapP = v.map(_.toInt)

        case ("diversify", Array(v1)) => diversify = v1.toBoolean

        case ("resolveFactsInitially", Array(v1)) => resolveFactsInitially = v1.toBoolean

        //case ("shuffleNogoodsOnRestart", Array(v1)) => shuffleNogoodsOnRestart = v1.toBoolean

        case ("ignoreParamVariables", Array(v1)) => ignoreParamVariables = v1.toBoolean

        case ("noOfUnfolds", Array(v1)) => noOfUnfolds = v1.toInt

        case ("initialActivBaseValue", Array(v1)) => initialActivBaseValue = v1.toFloat

        case ("reviseActivFreq", Array(v1)) => reviseActivFreq = v1.toInt

        case ("reviseActivFact", Array(v1)) => reviseActivFact = v1.toFloat

        case ("removeLearnedNogoods", Array(v1)) => removeLearnedNogoods = v1.toDouble

        case ("genBodyLitsFromSATClauses", Array(v1)) => genBodyLitsFromSATClauses = v1.toDouble

        case ("nogoodExchangeProbability", Array(v1)) => nogoodExchangeProbability = v1.toFloat

        //case ("omitSingletonBlits", Array(v1)) => omitSingletonBlits = v1.toBoolean

        case (arg: String, Array(v1)) => delSAT.stomp(-1, "--solverarg " + arg + " " + v1)

      }

      checkSettings

    }

    }

  }

  // --------------------------------------------------------------

  type Eli = Int

  type Nogi = Int

  final case class Rule(headAtomsElis: Array[Eli],
                        bodyPosAtomsElis: Array[Eli],
                        bodyNegAtomsElis: Array[Eli],
                        blit: Eli /*note: if omitSingletonBlits, this is an ordinary (non body) eli if there's just one body literal*/) {}

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
                                                    /*from DIMACS:*/ Array[ArrayEliUnsafe]],
                                                  noOfPosBlits: Int,
                                                  externalAtomElis: Seq[Eli], // for aspif only
                                                  emptyBodyBlit: Int = -1,
                                                  directClauseNogoodsOpt: Option[Array[ArrayEliUnsafe]] = None /*for debugging/crosschecks*/ ,
                                                  clauseTokensOpt: Option[Array[Array[Int]]]
                                                 ) {}

  type RandomGen = java.util.SplittableRandom

  val rngGlobal: java.util.Random = new XORShift32() // not thread-safe

  @inline def shuffleArrayBlocked[A](arr: mutable.Seq[A], rg: RandomGen): Unit = { // Blocked Fisher-Yates shuffle
    // (method code based on public domain code from https://github.com/lemire/Code-used-on-Daniel-Lemire-s-blog)

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

  @inline def shuffleArray[A](array: mutable.Seq[A], rg: RandomGen, to: Int = -1): Unit = { // plain Fisher-Yates shuffle on init of array

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

  @inline def shuffleArray[A](array: IntArrayUnsafe, rg: RandomGen): Unit = { // plain Fisher-Yates shuffle

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

    @inline def removeItem(item /*<- not an index*/ : T): Int /*Index of removed item (only the first occurrence is considered), or -1 */ = {

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

    @inline def removeIntItemsRange(from: Int /*item, not an index!*/ , to: Int): Unit = {

      var i = l - 1

      while (i >= 0) {

        val bi = buffer.get(i)

        if (bi >= from && bi <= to) {

          buffer.remove(i)

          l -= 1

        }

        i -= 1

      }

    }

  }

  @inline def timerToElapsedMs(startNano: Long): Long = (System.nanoTime() - startNano) / 1000000

}
