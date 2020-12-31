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

package utils

import input.UNSAFEhelper._
import it.unimi.dsi.fastutil.longs.{LongArrayList, LongOpenHashSet}


/** This is not a general-purpose unsafe array class - designed for use in project diff-SAT only! */
class LongArrayUnsafeS(var sizev: Int) extends IntOrLongArrayUnsafe[Long] {

  //private[this] val unsafe: Unsafe = sharedDefs.unsafe

  private[this] val alignment = 0

  //private[this] val alignment = UNSAFE.pageSize // currently not used (see code below), no visible effect in diff-SAT

  //private[this] val internalPaddingFact = 0

  //private[this] val longArrayOffs = UNSAFE.arrayBaseOffset(classOf[Array[Long]])

  //private[this] val aligned = false  // must be false (true not fully implemented yet)

  private[this] var allocated = (sizev << 3) + alignment

  //sharedDefs.offHeapAllocatedEstimate += allocateSize

  private[this] var addr: Long = if (alignment == 0) { // without private[this] the field access in the bytecode would be by invokevirtual

    allocateOffHeapMem(allocated)

  } else {  // the following only makes sense where alignment is different from unsafe's alignment (sizeOf?)

    var addra = allocateOffHeapMem(allocated)

    if (alignment > 0l && (addra & (alignment - 1l)) != 0)
      addra += (alignment - (addra & (alignment - 1)))

    addra // + alignment * internalPaddingFact

  }

  private[this] val addrMid: Long = addr + ((sizev >> 1) << 3) // nope: addr + (allocateSize / 2)

  assert((addrMid - addr) % 8 == 0)

  @inline def this(values: LongArrayList) {

    this(sizev = values.size)

    var i = 0

    while (i < sizev) {

      update(i, values.getLong((i)))

      i += 1

    }

  }

  @inline def this(s: Int, initValue: Long) {

    this(sizev = s)

    var i = 0

    while (i < s) {

      update(i, initValue)

      i += 1

    }

  }

  @inline def free(): Unit = {

    freeOffHeapMem(addr, allocated)


  }

  @inline def addToGarbage(): Unit = {

    addAllocOffHeapMemToGarbage(addr, allocated)

  }

  @inline def size(): Int = sizev

  @inline def compareAndUpdate(index: Int, expectedValue: Long, newValue: Long): Boolean = {

    UNSAFE.compareAndSwapLong(null, addr + (index << 3), expectedValue, newValue)

  }

  @inline def compareWithZeroAndUpdate(index: Int, newValue: Long): Boolean = {

    UNSAFE.compareAndSwapLong(null, addr + (index << 3), 0l, newValue)

  }

  @inline def get(index: Int): Long = {

    UNSAFE.getLong(addr + (index << 3))

  }

  @inline def copyLongTo(fromIndex: Int, toIndex: Int): Unit = {

    UNSAFE.putLong(addr + (toIndex << 3), UNSAFE.getLong(addr + (fromIndex << 3)))

  }

  @inline def get(index: Long): Long = {

    UNSAFE.getLong(addr + (index << 3))

  }

  @inline def getMid(index: Long): Long = {

    UNSAFE.getLong(addrMid + (index << 3))

  }

  @inline def first: Long = {

    UNSAFE.getLong(addr)

  }

  @inline def last: Long = {

    UNSAFE.getLong(addr + ((sizev - 1) << 3))

  }

  @inline def popLast: Long = {

    sizev -= 1

    UNSAFE.getLong(addr + (sizev << 3))

  }

  @inline def update(index: Int, value: Long): Unit = {

    UNSAFE.putLong(addr + (index << 3), value)

  }

  @inline def updateVolatile(index: Int, value: Long): Unit = {

    UNSAFE.putLongVolatile(null, addr + (index << 3), value)

  }

  @inline def updateOrdered(index: Int, value: Long): Unit = {

    UNSAFE.putOrderedLong(null, addr + (index << 3), value)

  }

  @inline def updateMid(index: Int/*<- negative or positive*/, value: Long): Unit = {

    UNSAFE.putLong(addrMid + (index << 3), value)

  }

  @inline def update(index: Int, value: Int): Unit = {

    UNSAFE.putLong(addr + (index << 3), value)

  }

  @inline def update(index: Long, value: Long): Unit = {

    UNSAFE.putLong(addr + (index << 3), value)

  }

  @inline def inc(index: Int): Long = {

    UNSAFE.getAndAddLong(null, addr + (index << 3), 1)

  }

  @inline def dec(index: Int): Long = {

    UNSAFE.getAndAddLong(null, addr + (index << 3), -1) - 1

  }

  @inline def incBy(index: Int, x: Long): Unit = {

    UNSAFE.getAndAddLong(null, addr + (index << 3), x)

  }

  @inline def compareAndSwap(index: Int, valueOld: Long, valueNew: Long): Unit = {

    UNSAFE.compareAndSwapLong(null, addr + (index << 3), valueOld, valueNew)

  }

  @inline def removeByIndex(index: Int): Unit = {

    sizev -= 1

    if(index < sizev) {

      update(index, get(sizev))

    }

  }

  @inline def filter(keepBy: Long => Boolean): Unit = {

    var k = sizev - 1

    while(k >= 0) {

      if(!keepBy(get(k)))
        removeByIndex(k)

      k -= 1

    }

  }


  @inline def toArray(): Array[Long] = {

    val array = new Array[Long](sizev)

    UNSAFE.copyMemory(null, addr, array, UNSAFE.arrayBaseOffset(classOf[Array[Long]]), sizev << 3)

    array

  }

  @inline def toArray(l: Int): Array[Long] = {

    val array = new Array[Long](l)

    UNSAFE.copyMemory(null, addr, array, UNSAFE.arrayBaseOffset(classOf[Array[Long]]), l << 3)

    array

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

  @inline def getAddr: Long = addr

  @inline def setAddr(newAddr: Long): Unit = addr = newAddr

  @inline def getAllocated: Int = allocated

  @inline def clone(padding: Int): LongArrayUnsafeS = {

    val bau: LongArrayUnsafeS = new LongArrayUnsafeS(sizev + padding)

    UNSAFE.copyMemory(addr, bau.getAddr, sizev << 3)

    bau

  }

  @inline def cloneToNew(padding: Int, keep: Int, cutOff: Boolean): LongArrayUnsafeS = {

    val bau: LongArrayUnsafeS = new LongArrayUnsafeS(if(cutOff) keep + padding else sizev + padding)

    //assert(addr + ((sizev - 1) << 3) < bau.getAddr || bau.getAddr + ((sizev + padding - 1) << 3) < addr)

    UNSAFE.copyMemory(addr, bau.getAddr, /*sizev*/keep << 3)

    bau

  }

  @inline def resize(newSize: Int): Unit = {  // see resize(newSize: Int, retain: Int) for the case where only a part of the current content needs to be retained

    allocated = newSize << 3

    addr = resizeOffHeapMem(addr, sizev << 3, allocated)

    sizev = newSize

  }

  @inline def resize(newSize: Int, retain: Int): Unit = {

    allocated = newSize << 3

    val newAddr = allocateOffHeapMem(allocated)

    if(retain > 0)
      UNSAFE.copyMemory(addr, newAddr, retain << 3)

    freeOffHeapMem(addr, sizev << 3)

    sizev = newSize

    addr = newAddr

  }

  def sortByInplace(by: Long => Double, until: Int): Unit = {

    // insertion sort - use only if array is very small (but then it's fast):

    var j = 1

    var key = -1l

    var i = -1

    while (j < until) {

      key = get(j)

      i = j - 1

      while (i > -1 && by(get(i)) > by(key)) {

        update(i + 1, get(i))

        i -= 1

      }

      update(i + 1, key)

      j += 1

    }

  }

  @inline def swap(i: Int, j: Int) = {

    val h = get(i)

    update(i, get(j))

    update(j, h)

  }

  // Returns index of k-th smallest item in this array
  def floydRivest(leftR: Int, rightR: Int, k: Int, by: Long => Double): Int = {

    var left = leftR

    var right = rightR

    while (right > left) {

      if (right - left > 600) { // sample subarray (constants 600, 0.5 largely arbitrary, from original implementation)

        val n = right - left + 1

        val i = k - left + 1

        val z = Math.log(n)

        val s = 0.5 * Math.exp(2 * z / 3)

        val sd = 0.5 * Math.sqrt(z * s * (n - s) / n) * Math.signum(i - n / 2)

        val newLeft = Math.max(left, (k - i * s / n + sd).toInt)

        val newRight = Math.min(right, (k + (n - i) * s / n + sd).toInt)

        floydRivest(newLeft, newRight, k, by)  // TODO: the Ints get boxed

      }

      val t = get(k)

      var i = left

      var j = right

      swap(left, k)

      if (by(get(right)) > by(t))
        swap(left, right)

      while (i < j) {

        swap(i, j)

        i += 1

        j -= 1

        while (by(get(i)) < by(t))
          i += 1

        while (by(get(j)) > by(t))
          j -= 1

      }

      if (by(get(left)) == by(t))
        swap(left, j)
      else {

        j += 1

        swap(right, j)

      }

      if (j <= k)
        left = j + 1

      if (k <= j)
        right = j - 1

    }

    k //get(k)

  }

  @inline def removeDuplicates(to: Int): Unit = {

    val hashForDuplRem = new LongOpenHashSet()

    var src = 0

    var dest = 0

    while(src <= to) {

      if(src == 0 || !hashForDuplRem.contains(get(src))) {

        hashForDuplRem.add(get(src))

        update(dest, get(src))

        dest += 1

      }

      src += 1

    }

    sizev = dest

  }

  @inline def establishDuplicateFreePrefixBy(by: Long => Long, to: Int): Int = {

    val hashForDuplRem = new LongOpenHashSet()

    var src = 0

    var dest = 0

    while(src <= to) {

      if(src == 0 || !hashForDuplRem.contains(by(get(src)))) {

        hashForDuplRem.add(by(get(src)))

        update(dest, get(src))

        dest += 1

      }

      src += 1

    }

    dest

  }

}
