/**
  * diff-SAT
  *
  * Copyright (c) 2018-2020 by Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import it.unimi.dsi.fastutil.ints.IntArrayList
import sun.misc.Unsafe
import sharedDefs._
import input.UNSAFEhelper._


/** This is not code for general-purpose unsafe (off-heap) memory use - designed for use in project diff-SAT only. Not thread-safe.
  * >>> Deprecated: use either IntArrayUnsafeS or direct allocated addresses instead. <<< */
@deprecated object IntArrayLeanUS {

  //val hashForDuplRemGlob = new IntOpenHashSet(2048, 0.75f)

  @inline def getAtAddr(unsafe: Unsafe, addr: Long, index: Int): Int = UNSAFE.getInt(addr + (index << 2))

  @inline def updateAtAddr(unsafe: Unsafe, addr: Long, index: Int, value: Int): Unit =
    UNSAFE.putInt(addr + (index << 2), value)

  @inline def sortByAtAddr(unsafe: Unsafe, addr: Long, by: Int => Float, until: Int): Unit = {

    // insertion sort - use only if array is very small (but then it's fast)

    var j = 1

    var key = -1

    var i = -1

    while (j < until) {

      key = getAtAddr(unsafe, addr, j)

      i = j - 1

      while (i > -1 && by(getAtAddr(unsafe, addr, i)) > by(key)) {

        updateAtAddr(unsafe: Unsafe, addr: Long, i + 1, getAtAddr(unsafe, addr, i))

        i -= 1

      }

      updateAtAddr(unsafe: Unsafe, addr: Long, i + 1, key)

      j += 1

    }

  }

  @inline def twinSortIntLongByIntAtAddr(unsafe: Unsafe, addr: Long, by: Int => Double, until: Int, addrTwin: Long): Unit = {

    // insertion sort simultaneously over an int and a long array, using only the int items for sorting order. Use
    // only if array is very small (but then it's fast)

    var j = 1

    var key = -1
    var keyTwin = -1l

    var i = -1

    while (j < until) {

      key = getAtAddr(unsafe, addr, j)
      keyTwin = UNSAFE.getLong(addrTwin + (j << 3))


      i = j - 1

      while (i > -1 && by(getAtAddr(unsafe, addr, i)) > by(key)) {

        updateAtAddr(unsafe, addr, i + 1, getAtAddr(unsafe, addr, i))
        UNSAFE.putLong(addrTwin + ((i + 1) << 3), UNSAFE.getLong(addrTwin + (i << 3)))

        i -= 1

      }

      updateAtAddr(unsafe, addr, i + 1, key)
      UNSAFE.putLong(addrTwin + ((i + 1) << 3), keyTwin)

      j += 1

    }

  }

  @inline def twinSortIntLongByLongAtAddr(unsafe: Unsafe, addr: Long, by: Long => Float, until: Int, addrTwin: Long): Unit = {

    // insertion sort simultaneously over an int and a long array, using only the long items for sorting order. Use
    // only if array is very small (but then it's fast)

    var j = 1

    var key = -1
    var keyTwin = -1l

    var i = -1

    while (j < until) {

      key = getAtAddr(unsafe, addr, j)
      keyTwin = UNSAFE.getLong(addrTwin + (j << 3))


      i = j - 1

      while (i > -1 && by(UNSAFE.getLong(addrTwin + (i << 3))) > by(keyTwin)) {

        updateAtAddr(unsafe, addr, i + 1, getAtAddr(unsafe, addr, i))
        UNSAFE.putLong(addrTwin + ((i + 1) << 3), UNSAFE.getLong(addrTwin + (i << 3)))

        i -= 1

      }

      updateAtAddr(unsafe, addr, i + 1, key)
      UNSAFE.putLong(addrTwin + ((i + 1) << 3), keyTwin)

      j += 1

    }

  }

}


/** This is not a general-purpose unsafe array class - designed for use in project diff-SAT only. Not thread-safe. */
@deprecated class IntArrayLeanUS(var sizev: Int) {
  // Using this class is only efficient if each single instance allocates a large amount of memory off-heap.
  // Using this class to create small objects is rather inefficient.

  private[this] val allocated: Long = sizev << 2

  private[this] val addr: Long = allocateOffHeapMem(allocated) // NB(1): allocateMemory is slow (compared to a direct malloc in C)
  // NB(2): Without private[this] the field access in the bytecode is by invokevirtual before being inlined, however, sharedDefs.unsafe  gets inline, so no (palpable) difference

  @inline def getAddr: Long = addr

  @inline def this(valuesa: Array[Int]) {

    this(valuesa.length)

    setFromIntArray(valuesa)

  }

  @inline def this(values: IntArrayList) {

    this(values.size)

    var i = 0

    while (i < sizev) {

      update(i, values.getInt(i))

      i += 1

    }

  }

  @inline def this(sizev: Int, initialValue: Int) {

    this(sizev)

    var i = 0

    while (i < sizev) {

      update(i, initialValue)

      i += 1

    }

  }

  @inline def free(): Unit = {

    if(allocated > 0) {

      freeOffHeapMem(addr, allocated)

    }

  }

  @inline def addToGarbage(): Unit = {

    addAllocOffHeapMemToGarbage(addr, allocated)

  }

  @inline def size(): Int = sizev

  override def hashCode: Int = {

    var hashVal: Int = 1

    var i = 0

    while (i < sizev) {

      hashVal = 31 * hashVal + get(i)

      i += 1

    }

    hashVal

  }

  override def equals(obj: Any): Boolean = {

    obj.asInstanceOf[IntArrayLeanUS].sizev == sizev && {

      /*if (isSorted) {

        var i = 0

        while (i < sizev) {

          if (obj.asInstanceOf[IntArrayUnsafeS].get(i) != get(i))
            return false

          i += 1

        }

        true

      } else*/
      java.util.Arrays.equals(toArray, obj.asInstanceOf[IntArrayLeanUS].toArray)

    }

  }

  @inline def setFromIntArray(values: Array[Int]): Unit = {

    UNSAFE.copyMemory(values, sharedDefs.intArrayOffs, null, addr, values.length << 2)

  }

  @inline def setFromUnsafeMemory(sourceAddr: Long, sourceSize: Int): Unit = {

    UNSAFE.copyMemory(sourceAddr, addr, sourceSize << 2)

  }

  @inline def compareAndUpdate(index: Int, expectedValue: Int, newValue: Int): Boolean = {

    UNSAFE.compareAndSwapInt(null, addr + (index << 2), expectedValue, newValue)

  }

  @inline def compareWithZeroAndUpdate(index: Int, newValue: Int): Boolean = {

    UNSAFE.compareAndSwapInt(null, addr + (index << 2), 0, newValue)

  }

  @inline def get(index: Int): Int = {

    UNSAFE.getInt(addr + (index << 2))

  }

  @inline def get(index: Long): Int = {

    UNSAFE.getInt(addr + (index << 2))

  }

  @inline def geta(index: Long): Int = {

    UNSAFE.getInt(addr + index)

  }

  @inline def first: Int = {

    UNSAFE.getInt(addr)

  }

  @inline def second: Int = {

    UNSAFE.getInt(addr + 4)

  }

  @inline def update(index: Int, value: Int): Unit = {

    UNSAFE.putInt(addr + (index << 2), value)

  }


  @inline def update(index: Long, value: Int): Unit = {

    UNSAFE.putInt(addr + (index << 2), value)

  }

  @inline def inc(index: Int): Int = {

    UNSAFE.getAndAddInt(null, addr + (index << 2), 1)

  }

  @inline def dec(index: Int): Int = {

    UNSAFE.getAndAddInt(null, addr + (index << 2), -1) - 1

  }

  @inline def incBy(index: Int, x: Int): Int = {

    UNSAFE.getAndAddInt(null, addr + (index << 2), x)

  }

  @inline def shiftRightAll(by: Int): Unit = {

    var i = 0

    var a = 0l

    while (i < sizev) {

      a = addr + (i << 2)

      UNSAFE.putInt(a, UNSAFE.getInt(a) >> by)

      i += 1

    }

  }

  @inline def binSearch(key: Int, fromIndex: Int, untilIndex: Int): Int = {

    var low = fromIndex

    var high = untilIndex

    while (low <= high) {

      val mid = (low + high) >>> 1

      if (get(mid) < key)
        low = mid + 1
      else if (get(mid) > key)
        high = mid - 1
      else
        return mid

    }

    low - 1 // note that this is different from Java's binarySearch result semantics

  }

  @inline def toArray: Array[Int] = {

    //byte[] array = new byte[(int) sizev];  // note that an unsafe array can exceed Int.MaxValue sizev, in which case this would fail

    val array: Array[Int] = new Array[Int](sizev)

    UNSAFE.copyMemory(null, addr, array, sharedDefs.intArrayOffs, sizev << 2)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Int] = {

    val array: Array[Int] = new Array[Int](until - from)

    UNSAFE.copyMemory(null, addr + (from << 2), array, sharedDefs.intArrayOffs, (until - from) << 2)

    array

  }

  @inline def fill(value: Byte, length: Int = sizev): Unit = {

    UNSAFE.setMemory(addr, length << 2, value.toByte)

  }

  override def toString: String = {

    val s: StringBuilder = new StringBuilder

    var i = 0

    while (i < sizev) {

      s.append(if (i < sizev - 1)
        get(i) + ","
      else
        get(i)) {

        i += 1

        i - 1

      }

    }

    s.toString

  }

  @inline def foreach(what: Int => Unit): Unit = {

    var i = 0

    while (i < sizev) {

      what(get(i))

      i += 1

    }

  }

  @inline def contains(x: Int, maxAddrExclusive: Long): Boolean = {

    var a = addr

    while (a < maxAddrExclusive) {

      if (UNSAFE.getInt(a) == x)
        return true

      a += 4l

    }

    false

  }

  @inline def contains(x: Int, maxIndexExclusive: Int = sizev): Boolean = {

    var ai = 0

    while (ai < maxIndexExclusive) {

      if (get(ai) == x)
        return true

      ai += 1

    }

    false

  }

  @inline def exists(predicate: Int => Boolean, maxIndexExclusive: Int = sizev): Boolean = {

    var ai = 0

    while (ai < maxIndexExclusive) {

      if (predicate(get(ai)))
        return true

      ai += 1

    }

    false

  }


  @inline def find(predicate: Int => Boolean, maxIndexExclusive: Int = sizev): Int = {

    var ai = 0

    while (ai < maxIndexExclusive) {

      if (predicate(get(ai)))
        return ai

      ai += 1

    }

    -1

  }

  @inline def count(item: Int): Int = {

    var c = 0

    var i = 0

    while (i < sizev) {

      if (get(i) == item)
        c += 1

      i += 1

    }

    c

  }

  @inline def count(predicate: Int => Boolean, maxIndexExclusive: Int = sizev): Int = {

    var c = 0

    var ai = 0

    while (ai < maxIndexExclusive) {

      if (predicate(get(ai)))
        c += 1

      ai += 1

    }

    c

  }

  @inline def cloneToNewAddr(extraSizePre: Int, extraSizePost: Int): Long = {

    val allocated = (extraSizePre + sizev + extraSizePost) << 2

    val bauAddr: Long = UNSAFE.allocateMemory(allocated)

    UNSAFE.copyMemory(addr, bauAddr + (extraSizePre << 2), sizev << 2)

    bauAddr

  }

  @inline def cloneToAddr(targetAddr: Long, offset: Int = 0): Long = {

    UNSAFE.copyMemory(addr, targetAddr + (offset << 2), sizev << 2)

    targetAddr

  }

  @inline def cloneToIntArrayUnsafeS(): IntArrayUnsafeS = {

    val newIntArrayUnsafeS = new IntArrayUnsafeS(this.sizev)

    UNSAFE.copyMemory(addr, newIntArrayUnsafeS.getAddr, sizev << 2)

    newIntArrayUnsafeS

  }

  @inline def removeItem(item: Int): Unit = {  // as removeItemAll but stops after the first occurrence of item

    var i = sizev - 1

    while (i >= 0) {

      if (get(i) == item) {

        sizev -= 1

        if (i < sizev)
          UNSAFE.copyMemory(addr + (size << 2), addr + (i << 2), 1 << 2)

        i = -1

      } else
        i -= 1

    }

  }

  @inline def revert(): Unit = {

    var i = 0

    while (i < sizev / 2) {

      val temp = get(i)

      update(i, get(sizev - i - 1))

      update(sizev - i - 1, temp)

      i += 1

    }

  }

  def removeDuplicatesGlob(): Unit = { // not thread-safe

    IntArrayUnsafeS.hashForDuplRemGlob.clear()

    var src = 0

    var dest = 0

    while(src < sizev) {

      if(!IntArrayUnsafeS.hashForDuplRemGlob.contains(get(src))) {

        IntArrayUnsafeS.hashForDuplRemGlob.add(get(src))

        if(dest != src)
          update(dest, get(src))

        dest += 1

      }

      src += 1

    }

    sizev = dest

  }

  @inline def forEach(sideEffect: Int => Any): Unit = {

    var i = 0

    while (i < sizev) {

      sideEffect(get(i))

      i += 1

    }

  }

  @inline def forAll(predicate: Int => Boolean): Boolean = {

    var i = sizev - 1

    while (i >= 0) {

      if (!predicate(get(i)))
        return false

      i -= 1

    }

    return true

  }

  @inline def sortBy(by: Int => Float): Unit = {

    // insertion sort - use only if array is very small (but then it's relatively fast):

    IntArrayUnsafeS.sortByInplace(unsafe, addr, by, sizev)

  }

  @inline def subsetOf(nogoodB: IntArrayLeanUS): Boolean /*true: nogoodA subset of nogoodB*/ = {

    if (nogoodB.sizev <= sizev)
      false
    else {

      var ia = 0

      while (ia < sizev) {

        if (!nogoodB.contains(get(ia)))
          return false

        ia += 1

      }

      true

    }

  }

  @inline def subsetOfExceptOne(nogoodB: IntArrayLeanUS, ignoreIndexInThis: Int): Boolean
  /*true: this (ignoring eli index ignoreIndexInThis) is a subset of nogoodB */ = {

    nogoodB.sizev > sizev && {

      var ia = 0

      while (ia < sizev) {

        if (ia != ignoreIndexInThis && !nogoodB.contains(get(ia)))
          return false

        ia += 1

      }

      true

    }

  }

}
