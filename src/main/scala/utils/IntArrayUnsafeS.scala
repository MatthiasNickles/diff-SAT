/**
  * diff-SAT
  *
  * Copyright (c) 2018-2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import it.unimi.dsi.fastutil.ints.{IntArrayList, IntOpenHashSet}
import sun.misc.Unsafe
import sharedDefs._
import input.UNSAFEhelper._

/** This is not code for general-purpose unsafe (off-heap) memory use - designed for use in project diff-SAT only. */
object IntArrayUnsafeS {

  val hashForDuplRemGlob = new IntOpenHashSet(2048, 0.75f)

  @inline def getAtAddr(unsafe: Unsafe, addr: Long, index: Int): Int = UNSAFE.getInt(addr + (index << 2))

  @inline def updateAtAddr(unsafe: Unsafe, addr: Long, index: Int, value: Int): Unit =
    UNSAFE.putInt(addr + (index << 2), value)

  @inline def sortByInplace(unsafe: Unsafe, addr: Long, by: Int => Float, until: Int): Unit = {

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

  @inline def removeItemAll(unsafe: Unsafe, addr: Long, item: Int, initialLength: Int): Int= {

    var sizev = initialLength

    var i = sizev - 1

    while (i >= 0) {

      if (getAtAddr(unsafe, addr, i) == item) {

        sizev -= 1

        if (i < sizev)
          UNSAFE.copyMemory(addr + ((i + 1) << 2), addr + (i << 2), (sizev - i) << 2)

      }

      i -= 1

    }

    sizev

  }

}


/** This is not a general-purpose unsafe array class - designed for use in project diff-SAT only. Not thread-safe. */
class IntArrayUnsafeS(var sizev: Int, atAddress: Long = -1) extends IntOrLongArrayUnsafe[Int] {

  // Important: using this class, which simply combines an JVM off-heap memory address with meta-data (especially size)
  // into an object is only efficient if each single instance allocates a large amount of memory.
  // Using this class to create lots of small objects is inefficient - instead, store size and content into a single
  // off-heap memory slot in adjacent positions (e.g., int for size, at address + 4l the actual content) instead.

  import IntArrayUnsafeS._

  //private[this] val unsafe: Unsafe = sharedDefs.unsafe  // without private[this] the field access in the bytecode is by invokevirtual before
  // being inlined, however, sharedDefs.unsafe  gets inline, so no (palpable) difference

  /*private[this] val alignment: Int = 0  // observe that unsafe's allocateMemory does some alignment (to value size) by itself

  assert(alignment == 0) // alignment doesn't play well with our off-heap garbage collection and doesn't seem to be
  // useful anyway (on top of unsafe's built-in alignment)
  */

  //private[this] val internalPaddingFact = 1 // see below

  //private[this] lazy val intArrayOffs = sharedDefs.UNSAFE.arrayBaseOffset(classOf[Array[Int]]) // we put this here to ensure that scalac makes this a static field

  //var isSorted = false

  //var isAligned = false

  //private[this] var allocated = 0
  @inline def allocated: Int = sizev << 2

  //private[this] val align = false  // must be false

  private[this] var addr: Long = /*if (sizev == -1) -1l else*/ if (atAddress != -1l) {

    atAddress

  } else /*if (alignment == 0)*/ {

    //allocated = sizev << 2

    //sharedDefs.offHeapAllocatedEstimate += allocated

    allocateOffHeapMem(allocated) // observe that allocateMemory is slow (compared to a direct malloc in C)

  }/* else {

   // assert(false)  // it looks like alignment of this array has in diff-SAT no beneficial effect

    //isAligned = true

    allocated = (sizev << 2) + alignment //+ alignment * internalPaddingFact

    //sharedDefs.offHeapAllocatedEstimate += allocated

    var addra = allocateOffHeapMem(allocated)

    if (alignment > 0l && (addra & (alignment - 1l)) != 0)
      addra += (alignment - (addra & (alignment - 1)))

    addra //+ alignment * internalPaddingFact

  }*/

  private[this] val addrMid: Long = addr + ((sizev >> 1) << 2) //nope: addr + (allocated / 2)

  assert((addrMid - addr) % 4 == 0)

  @inline def getAddr: Long = addr

  @inline def setAddr(newAddr: Long): Unit = addr = newAddr

  @inline def setAllTo(value: Int): Unit = {

    var i = 0

    while (i < sizev) {

      update(i, value)

      i += 1

    }

  }

  @inline def this(values: Array[Int]) {

    this(values.length)

    setFromIntArray(values)

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

    setAllTo(initialValue)

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

  /*override def hashCode: Int = {  // don't use for checking nogood identity!

    var hashVal: Int = 1

    var i = 0

    while (i < sizev) {

      hashVal = 31 * hashVal + get(i)

      i += 1

    }

    hashVal

  }*/

  override def equals(obj: Any): Boolean = {

    obj.asInstanceOf[IntArrayUnsafeS].sizev == sizev && {

      java.util.Arrays.equals(toArray, obj.asInstanceOf[IntArrayUnsafeS].toArray)

    }

  }

  @inline def setFromIntArray(values: Array[Int]): Unit = {

    UNSAFE.copyMemory(values, sharedDefs.intArrayOffs, null, addr, values.length << 2)

  }

  @inline def setFromUnsafeIntArray(source: IntArrayUnsafeS, updateSize: Boolean = false): Unit = {

    UNSAFE.copyMemory(source.getAddr, addr, source.sizev << 2)

    if (updateSize)
      sizev = source.sizev

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

  @inline def getMid(index: Int): Int = {

    UNSAFE.getInt(addrMid + (index << 2))

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

  @inline def last: Int = {

    UNSAFE.getInt(addr + ((sizev - 1) << 2))

  }

  @inline def popLast: Int = {

    sizev -= 1

    UNSAFE.getInt(addr + (sizev << 2))

  }

  @inline def update(index: Int, value: Int): Unit = {

    UNSAFE.putInt(addr + (index << 2), value)

  }

  @inline def updateMid(index: Int, value: Int): Unit = {

    UNSAFE.putInt(addrMid + (index << 2), value)

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

  @inline def removeByIndex(index: Int): Unit = {

    sizev -= 1

    if(index < sizev) {

      update(index, get(sizev))

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

  @inline def clone(extraSizePre: Int, extraSizePost: Int): IntArrayUnsafeS = {

    val allocated = (extraSizePre + sizev + extraSizePost) << 2

    val bauAddr: Long = allocateOffHeapMem(allocated)

    UNSAFE.copyMemory(addr, bauAddr + (extraSizePre << 2), sizev << 2)

    new IntArrayUnsafeS(sizev = extraSizePre + sizev + extraSizePost, atAddress = bauAddr)

  }

  @inline def cloneToNewAddr(extraSizePre: Int, extraSizePost: Int): Long = {

    val allocated = (extraSizePre + sizev + extraSizePost) << 2

    val bauAddr: Long = allocateOffHeapMem(allocated)

    UNSAFE.copyMemory(addr, bauAddr + (extraSizePre << 2), sizev << 2)

    bauAddr

  }

  @inline def cloneToNewAddrFromUntil(from: Int, until/*excl*/: Int): Long = {

    val allocated = (until - from) << 2

    val bauAddr: Long = allocateOffHeapMem(allocated)

    UNSAFE.copyMemory(addr + (from << 2), bauAddr, allocated)

    bauAddr

  }

  @inline def cloneToNewWithSizeAddrFromUntilRRR(from: Int, until/*excl*/: Int, extraInfo: Int): Long = { //rrr

    val allocated = (until - from + 1/*for size*/ + 1/*for extraInfo*/) << 2

    val bauAddr: Long = allocateOffHeapMem(allocated)

    UNSAFE.putInt(bauAddr, until - from)  // size

    UNSAFE.putInt(bauAddr + 4l, extraInfo)

    UNSAFE.copyMemory(addr + (from << 2), bauAddr + 4l + 4l, allocated - 4l - 4l)

    bauAddr

  }

  @inline def cloneToNew(padding: Int, keep: Int, cutOff: Boolean): IntArrayUnsafeS = {

    val bau: IntArrayUnsafeS = new IntArrayUnsafeS(if(cutOff) keep + padding else sizev + padding)

    UNSAFE.copyMemory(addr, bau.getAddr, /*sizev*/keep << 2)

    bau

  }


  @inline def cloneTo(targetAddr: Long, offset: Int = 0): IntArrayUnsafeS = {

    UNSAFE.copyMemory(addr, targetAddr + (offset << 2), sizev << 2)

    new IntArrayUnsafeS(sizev = offset + sizev, atAddress = targetAddr)

  }

  @inline def cloneToAddr(targetAddr: Long, offset: Int = 0): Long = {

    UNSAFE.copyMemory(addr, targetAddr + (offset << 2), sizev << 2)

    targetAddr

  }

  @inline def removeItemAll(item: Int): Unit = {

    var i = sizev - 1

    while (i >= 0) {

      if (get(i) == item) {

        sizev -= 1

        if (i < sizev)
          UNSAFE.copyMemory(addr + ((i + 1) << 2), addr + (i << 2), (sizev - i) << 2)

      }

      i -= 1

    }

  }

  @inline def removeItem(item: Int): Unit = {  // as removeItemAll but stops after the first occurrence of item

    var i = sizev - 1

    while (i >= 0) {

      if (get(i) == item) {

        sizev -= 1

        if (i < sizev)
          UNSAFE.copyMemory(addr + ((i + 1) << 2), addr + (i << 2), (sizev - i) << 2)

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

  @inline def removeDuplicates(): Unit = {

    val hashForDuplRem = new IntOpenHashSet()

    var src = 0

    var dest = 0

    while(src < sizev) {

      if(src == 0 || !hashForDuplRem.contains(get(src))) {

        hashForDuplRem.add(get(src))

        update(dest, get(src))

        dest += 1

      }

      src += 1

    }

    sizev = dest

  }

  def removeDuplicatesGlob(): Unit = { // not thread-safe

    hashForDuplRemGlob.clear()
/*
    var src = 0

    var dest = 0

    while(src < sizev) {

      if(!hashForDuplRemGlob.contains(get(src))) {

        hashForDuplRemGlob.add(get(src))

        if(dest != src)
          update(dest, get(src))

        dest += 1

      }

      src += 1

    }

    sizev = dest */

    var src = 0

    var dest = 0

    while(src < sizev) {

      if(hashForDuplRemGlob.add(get(src))) {

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

    sortByInplace(unsafe, addr, by, sizev)

  }

  @inline def subsetOf(nogoodB: IntArrayUnsafeS): Boolean /*true: nogoodA subset of nogoodB*/ = {

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

  @inline def subsetOfExceptOne(nogoodB: IntArrayUnsafeS, ignoreIndexInThis: Int): Boolean
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
