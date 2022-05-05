/**
  * diff-SAT
  *
  * Copyright (c) 2018,2020 by Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import input.UNSAFEhelper
import sharedDefs.{Eli, RandomGenSuperclass}

import scala.annotation.tailrec

/**
  * Set of positive integers, using a dual index structure for looking up the index of an element
  * in O(1) (O(1) add (unsorted), O(1) remove).
  * (Can also be used as a simple special-purpose heap (with diff-SAT literal scores as order).)
  *
  * For storing small sets of small positive int elements only!
  *
  * Preallocates two off-heap arrays with maximum size.
  *
  * sortedMode adds a radix search-like feature.
  *
  * Set functionality based on Java code from https://stackoverflow.com/questions/124671/picking-a-random-element-from-a-set
  *
  * Not thread-safe. Not suitable for cryptographically secure randomness.
  *
  */
final class DualIndexedIntSet(sizeDta: Int /*Important: array data must cover the largest item as it is used directly as an index into data */ ,
                              rnd: RandomGenSuperclass,
                              sortedMode: Boolean = false,
                              getAbsEliScore: Eli => Double = null,
                              updateAbsEliScore_ : (Eli, Double) => Unit = null) /*extends ForceElis2*/ {

  var dta = new IntArrayUnsafeS(sizeDta)

  var idx = new IntArrayUnsafeS(sizeDta, initialValue = -1) // the index of an item within data
  // Thus we can store only int items with values from 0 until maxE (excluding)

  var dtaLength = 0

  @inline def clear(): Unit = {

    var index = 0

    while (index < dtaLength) {

      idx.update(get(index), -1)

      index += 1

    }

    dtaLength = 0

  }

  @inline def free(): Unit = {

    idx.free()

    dta.free()

  }

  @inline def addToGarbage(): Unit = {

    idx.addToGarbage()

    dta.addToGarbage()

  }

  @inline def contains(item: Int): Boolean = idx.get(item) >= 0

  @inline def add(item: Int): Unit = {

    assert(!sortedMode)

    assert(item < sizeDta && item >= 0)

    if (idx.get(item) < 0 || idx.get(item) >= dtaLength) {

      dta.update(dtaLength, item)

      idx.update(item, dtaLength)

      dtaLength += 1

    }

  }

  @tailrec
  @inline def isSorted(startIndex: Int = 0): Boolean = {

    // (slow; use for debugging purposes only)

    assert(sortedMode)

    if (startIndex >= dtaLength - 1)
      true
    else {

      getAbsEliScore(get(startIndex)) <= getAbsEliScore(get(startIndex + 1)) && isSorted(startIndex + 1)

    }

  }

 /* def print(scores: DoubleArrayUnsafeS = null, untilIndex: Int = Int.MaxValue): Unit = {

    println("size = " + size)

    var i = 0

    while (i < size.min(untilIndex)) {

      println("  index " + i + ", item (value) = " + data.get(i) + (if (scores != null) ", item score: " + getAbsEliScore(data.get(i)) else ""))

      i += 1

    }

  }*/

  @inline def addSorted(item: Int): Boolean = { // to use this indexed set like a heap.
    // Observe that the remove methods in this class destroy the order (since they change the index of an element which
    // remains in the set). With diff-SAT, use sort() or, where possible, nudgeUpSorted().

    assert(sortedMode)

    assert(item < sizeDta && item >= 0)

    val r = addItemSorted_(item, fromIndex = 0, toIndex = dtaLength)

    //assert(isSorted(scores))

    r

  }

  @inline def addItemSorted_(item: Int, fromIndex: Int, toIndex: Int): Boolean = {  // don't call directly,
    // call via addSorted() instead.

    assert(sortedMode)

    /*if(dtaLength > 200 && rnd.nextFloat() < 0.0001f) {

      print(scores, 200)

    }*/

    if (idx.get(item) < 0 /*|| index.get(item) >= dtaLength*/) {

      var insertionIndex = if (dtaLength == 0 || getAbsEliScore(item) < getAbsEliScore(get(0)))
        0
      else if (getAbsEliScore(item) >= getAbsEliScore(get(dtaLength - 1)))
        dtaLength
      else
        findInsertionIndexSorted_(item, fromIndex, toIndex)

      //println("InsertionPoint = " + dtaI)

      if (insertionIndex < dtaLength) {

        //assert(getAbsEliScore(get(insertionIndex)) >= getAbsEliScore(item))

        UNSAFEhelper.UNSAFE.copyMemory(dta.getAddr + (insertionIndex << 2), dta.getAddr + ((insertionIndex + 1) << 2), (dtaLength - insertionIndex) << 2)

        dta.update(insertionIndex, item)

        idx.update(item, insertionIndex)  // observe that from a user's point of view, this value is meaningless in sortedMode except
        // where it is -1. However, we can use index(item) as a hint to speed up the search for the precise index of item later.

        dtaLength += 1

        if(false && dtaLength < 50) {  // too costly:

          insertionIndex += 1

          while (insertionIndex < dtaLength) {

            idx.update(get(insertionIndex), insertionIndex)

            insertionIndex += 1

          }

        }

      } else {

        dta.update(dtaLength, item)

        idx.update(item, dtaLength)

        dtaLength += 1

      }

      true

    } else
      false

  }

  @tailrec
  @inline def findInsertionIndexSorted_(item: Int, fromIndex: Int, toIndex: Int): Int = {
    // binary search for successor index (utility function for addSorted_ to obtain insertion point)

    assert(sortedMode)

    if (fromIndex == toIndex) {

      if (fromIndex >= dtaLength)  // TODO: redundant >= dtaLength checks below
        dtaLength
      else {

      /*  assert(fromIndex >= 0)
        assert(fromIndex < dtaLength)
        assert(item >= 0)
        assert(item < scores.size)
        assert(get(fromIndex) >= 0)
        assert(get(fromIndex) < scores.size) */

        if (getAbsEliScore(get(fromIndex)) >= getAbsEliScore(item))
          fromIndex
        else if (fromIndex + 1 >= dtaLength)
          dtaLength
        else
          fromIndex + 1

      }

    } else if (fromIndex + 1 == toIndex) {  // TODO: optimize:

     /* assert(fromIndex >= 0)
      assert(fromIndex < dtaLength)
      assert(item >= 0)
      assert(item < scores.size)
      assert(get(fromIndex) >= 0)
      assert(get(fromIndex) < scores.size)*/

      if (getAbsEliScore(get(fromIndex)) >= getAbsEliScore(item))
        fromIndex
      else if (fromIndex + 1 >= dtaLength)
        dtaLength
      else if (getAbsEliScore(get(fromIndex + 1)) >= getAbsEliScore(item))
        fromIndex + 1
      else if (fromIndex + 2 >= dtaLength)
        dtaLength
      else
        fromIndex + 2

    } else {

     /* assert(item >= 0)
      assert(item < scores.size)
*/
      val pIndex = fromIndex + ((toIndex - fromIndex) >> 1)

      val scoreItem = getAbsEliScore(item)

  /*    assert(pIndex >= 0)
      assert(pIndex < dtaLength)
      assert(get(pIndex) >= 0)
      assert(get(pIndex) < scores.size)
*/
      val scoreP = getAbsEliScore(get(pIndex))

      if (scoreItem == scoreP)
        pIndex
      else if (scoreItem < scoreP)
        findInsertionIndexSorted_(item, fromIndex, pIndex - 1)
      else
        findInsertionIndexSorted_(item, pIndex + 1, toIndex)

    }

  }

  @inline def findIndexSorted(item: Int): Int = {

    if(idx.get(item) < dtaLength) {  // while the old index(item) cannot be reused directly, we can use it as a hint or cache:

      if(dta.get(idx.get(item)) == item)
        return idx.get(item)

      val optimisticBracketL = (idx.get(item) - 50/*sqrt(dtaLength)*/).max(0)

      val optimisticBracketR = (idx.get(item) + 50/*sqrt(dtaLength)*/).min(dtaLength - 1)

      val tr = findIndexSorted_(item, bracketL = optimisticBracketL, bracketR = optimisticBracketR)

      if(tr >= 0)
        return tr

    }

    findIndexSorted_(item, bracketL = 0, bracketR = dtaLength - 1)

  }

  @inline def findIndexSorted_(item: Int, bracketL: Int, bracketR: Int): Int = {
    // binary search for index of item (since the concrete index values are meaningless in sortedMode).
    // Result -1: item not found

    assert(sortedMode)

    //assert(contains(item))

    {

      var l = bracketL //0

      var r = bracketR //dtaLength - 1

      val t = getAbsEliScore(item)

      while (l <= r) {

        val m = if(idx.get(item) >= l && idx.get(item) <= r)  // while the old index(item) cannot be returned directly, we can use it as a hint:
          idx.get(item)
        else
          Math.floor((l + r) >> 1).toInt

        val sm = getAbsEliScore(get(m))

        if (sm < t)
          l = m + 1
        else if (sm > t)
          r = m - 1
        else {

          if (get(m) == item) {

            idx.update(item, m)

            return m

          }

          // we end up here if multiple items have the same score (recall we aren't looking for any item with that score but for
          // the exact index of the item)

          var mm = m - 1

          while (mm >= 0) {

            if (get(mm) == item) {

              idx.update(item, mm)

              return mm

            }

            mm -= 1

          }

          mm = m + 1

          while (mm < dtaLength) {

            if (get(mm) == item) {

              idx.update(item, mm)

              return mm

            }

            mm += 1

          }

          assert(false)

        }

      }

    }

    -1

  }

  /* TODO: repair:
  @inline def testSorted(): Unit = {  // TODO: add tests of score updates

    if (!areAssertionsEnabled)
      userAPItests.diffSAT.stomp(-1, "Assertions need to be enabled to run this test!")

    assert(sortedMode)

    val trials = 10000

    val printIntermediateResults = false

    val startTimeNs = System.nanoTime()

    for (trial <- 1 to trials) {

      println("\n------------- Trial " + trial)

      clear()

      val testIterations = 1000.min(sizeDta - 1)

      val testScores = new DoubleArrayUnsafeS(testIterations + 1, false)

      var si = 0

      while (si < testIterations) {

        val testScore = if (rnd.nextFloat() < 0.05) 1e-304d else if (rnd.nextFloat() < 0.1) 1e+304d else if (rnd.nextFloat() < 0.2) 0.5d else rnd.nextDouble()

        val testItem = si + 1

        val sizeBefore = dtaLength

        testupdateAbsEliScore_(testItem, testScore)

        if (printIntermediateResults) println("\nAdding testItem = " + testItem + ", testScore = " + testScore + "...")

        if (printIntermediateResults) println("\nBefore addSorted:")

        if (printIntermediateResults) print(testScores /*, untilIndex = 20*/)

        addItemSorted_(testItem, testScores, fromIndex = 0, toIndex = dtaLength)

        assert(contains(testItem))

        if (printIntermediateResults) println("After addSorted:")

        if (printIntermediateResults) print(testScores /*, untilIndex = 20*/)

        assert(size == sizeBefore + 1)

        assert(isSorted(testScores))

        val indexOfTestItem = findIndexSorted(testItem, testScores)

        assert(indexOfTestItem >= 0)

        if (rnd.nextFloat() < 0.1) {

          if (printIntermediateResults) println("\nRemoving testItem = " + testItem + "...")

          removeSorted(testItem, testScores)

          assert(!contains(testItem))

          assert(size == sizeBefore)

          assert(isSorted(testScores))

        }

        si += 1

      }

    }

    println("\n---- addSorted test completed successfully! ----")

    println("Test duration: " + timerToElapsedMs(startTimeNs) + " ms")

    sys.exit(0)


  }*/

  @tailrec
  @inline def nudgeUpSorted_(item: Int, indexOfItem: Int): Unit = { // works only if new score of item
    // is larger than or equal its previous score

    assert(sortedMode)

    assert(indexOfItem >= 0)

    if (indexOfItem < size - 1) {

      val scoreOfItem = getAbsEliScore(item)

      val nextItem = get(indexOfItem + 1)

      val scoreOfNextItem = getAbsEliScore(nextItem)

      if (scoreOfItem > scoreOfNextItem) {

        dta.update(indexOfItem, nextItem)

        dta.update(indexOfItem + 1, item)

        nudgeUpSorted_(item, indexOfItem + 1)

      }

    }

  }

  @tailrec
  @inline def nudgeDownSorted_(item: Int, indexOfItem: Int): Unit = { // works only if new score of item
    // is lower than or equal its previous score

    assert(sortedMode)

    assert(indexOfItem >= 0)

    if (indexOfItem > 0) {

      val scoreOfItem = getAbsEliScore(item)

      val prevItem = get(indexOfItem - 1)

      val scoreOfPrevItem = getAbsEliScore(prevItem)

      if (scoreOfItem < scoreOfPrevItem) {

        dta.update(indexOfItem, prevItem)

        dta.update(indexOfItem - 1, item)

        nudgeDownSorted_(item, indexOfItem - 1)

      }

    }

  }

  @inline def updateScoreSorted(item: Int/*, scores: DoubleArrayUnsafeS*/, newScore: Double,
                                ): Unit = {

    // Important: this method also updates the actual score

    assert(sortedMode)

    //assert(isSorted(scores))

    val indexOfItem = findIndexSorted(item)

    assert(indexOfItem >= 0)

    val oldScore = getAbsEliScore(item)

    if(newScore > oldScore) {

      updateAbsEliScore_(item, newScore)

      nudgeUpSorted_(item, indexOfItem)

    } else if(newScore < oldScore) {

      updateAbsEliScore_(item, newScore)

      nudgeDownSorted_(item, indexOfItem)

    }

    //assert(contains(item))

    //assert(isSorted(scores))

  }

  @inline def removeSorted(item: Int): Boolean = {

    assert(sortedMode)

    assert(contains(item))

    var indexOfItem = findIndexSorted(item)

    if (indexOfItem < 0) {

      assert(false)

      false

    } else {

      idx.update(item, -1)

      dtaLength -= 1

      input.UNSAFEhelper.UNSAFE.copyMemory(dta.getAddr + ((indexOfItem + 1) << 2),
        dta.getAddr + (indexOfItem << 2), (dtaLength - indexOfItem) << 2)

      if(false && dtaLength < 50) {  // too costly:

        while (indexOfItem < dtaLength) {

          idx.update(get(indexOfItem), indexOfItem)

          indexOfItem += 1

        }

      }

      assert(!contains(item))

      //assert(isSorted(scores))

      true

    }

  }

  @inline def sort(): Unit = { // TODO: optimize

    val dtaClone = dta.clone(0, 0)

    val dtaCloneSize = size

    clear()

    var i = 0

    while (i < dtaCloneSize) {

      addSorted(dtaClone.get(i))

      i += 1

    }

    assert(isSorted())

  }

  var item = -1

  var lastItem = -1

  @inline def removeAt(index: Int): Int = { // NB: destroys sorting order (if any)

    assert(!sortedMode)

    item = dta.get(index)

    idx.update(item, -1)

    dtaLength -= 1

    if (index < dtaLength) {

      lastItem = dta.get(dtaLength)

      idx.update(lastItem, index)

      dta.update(index, lastItem)

    }

    item

  }

  @inline def remove(item: Int): Boolean = { // NB: destroys sorting order (if any). See removeSorted()

    assert(!sortedMode)

    val id = idx.get(item)

    if (id < 0 || id >= dtaLength)
      false
    else {

      removeAt(id)

      true

    }

  }

  @inline def removeNR(item: Int): Unit = { // NB: destroys sorting order (if any)

    assert(!sortedMode)

    if (idx.get(item) >= 0 && idx.get(item) < dtaLength)
      removeAt(idx.get(item))

  }

  @inline def get(index: Int): Int = dta.get(index)

  @inline def getRandom(): Int = dta.get(rnd.nextInt(dtaLength))

  @inline def getRandomOpt(): Option[Int] = if (dtaLength == 0) None else Some(dta.get(rnd.nextInt(dtaLength)))

  @inline def getFirst(): Int = dta.get(0)

  @inline def getLast(): Int = dta.get(dtaLength - 1)

  @inline def getRemoveRandom(): Int = removeAt(rnd.nextInt(dtaLength))

  @inline def getRemoveLast(): Int = {

    dtaLength -= 1

    idx.update(dta.get(dtaLength), -1)

    dta.get(dtaLength)

  }

  @inline def removeLast(): Unit = {

    dtaLength -= 1

  }

  @inline def update(index: Int, item: Int): Unit = {

    assert(!sortedMode)

    dta.update(index, item)

    idx.update(item, index)

  }

  @inline def size(): Int = dtaLength

  @inline def isEmpty: Boolean = dtaLength == 0

}

