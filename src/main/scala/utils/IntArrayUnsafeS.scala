/**
  * delSAT
  *
  * Copyright (c) 2018, 2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/delSAT/blob/master/LICENSE
  *
  */

package utils

import it.unimi.dsi.fastutil.ints.IntArrayList

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only. */
object IntArrayUnsafeS {

  val alignment: Int = 128 // sharedDefs.unsafe.pageSize

  val internalPaddingFact = 1 // multiple of actual alignment (see below)

}

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only. */
class IntArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  import IntArrayUnsafeS._

  private[this] val unsafe = sharedDefs.unsafe

  private[this] val intArrayOffs = sharedDefs.unsafe.arrayBaseOffset(classOf[Array[Int]])  // we put this here to ensure that scalac makes this a static field

  var isSorted = false

  val isAligned = aligned

  /*private[this]*/ val addr: Long = if (!aligned)
    unsafe.allocateMemory(sizev << 2)
  else {

    var addra = unsafe.allocateMemory((sizev << 2) + alignment + alignment * internalPaddingFact)

    if (alignment > 0l && (addra & (alignment - 1l)) != 0)
      addra += (alignment - (addra & (alignment - 1)))

    addra + alignment * internalPaddingFact

  }

  @inline def getAddr: Long = addr

  @inline def this(values: Array[Int], aligned: Boolean) {

    this(values.length, aligned = aligned)

    setFromIntArray(values)

  }

  @inline def this(values: IntArrayList, aligned: Boolean) {

    this(values.size, aligned = aligned)

    var i = 0

    while (i < sizev) {

      update(i, values.getInt(i))

      i += 1

    }

  }

  @inline def this(sizev: Int, initialValue: Int, aligned: Boolean) {

    this(sizev, aligned = aligned)

    var i = 0

    while (i < sizev) {

      update(i, initialValue)

      i += 1

    }

  }

  @inline def free(): Unit = unsafe.freeMemory(addr)

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

    obj.asInstanceOf[IntArrayUnsafeS].sizev == sizev && {

      if (isSorted) {

        var i = 0

        while (i < sizev) {

          if (obj.asInstanceOf[IntArrayUnsafeS].get(i) != get(i))
            return false

          i += 1

        }

        true

      } else
        java.util.Arrays.equals(toArray, obj.asInstanceOf[IntArrayUnsafeS].toArray)

    }

  }

  @inline def setFromIntArray(values: Array[Int]): Unit = {

    unsafe.copyMemory(values, intArrayOffs, null, addr, values.length << 2)

  }

  @inline final def compareAndUpdate(index: Int, expectedValue: Int, newValue: Int): Boolean = {

    unsafe.compareAndSwapInt(null, addr + (index << 2), expectedValue, newValue)

  }

  @inline final def compareWithZeroAndUpdate(index: Int, newValue: Int): Boolean = {

    unsafe.compareAndSwapInt(null, addr + (index << 2), 0, newValue)

  }

  @inline final def get(index: Int): Int = {

    unsafe.getInt(addr + (index << 2))

  }

  @inline final def get(index: Long): Int = {

    unsafe.getInt(addr + (index << 2))

  }

  @inline final def first: Int = {

    unsafe.getInt(addr)

  }

  @inline final def second: Int = {

    unsafe.getInt(addr + 4)

  }

  @inline final def update(index: Int, value: Int): Unit = {

    unsafe.putInt(addr + (index << 2), value)

  }

  @inline final def update(index: Long, value: Int): Unit = {

    unsafe.putInt(addr + (index << 2), value)

  }

  @inline final def inc(index: Int): Int = {

    unsafe.getAndAddInt(null, addr + (index << 2), 1)

  }

  @inline final def dec(index: Int): Int = {

    unsafe.getAndAddInt(null, addr + (index << 2), -1) - 1

  }

  @inline final def incBy(index: Int, x: Int): Unit = {

    unsafe.getAndAddInt(null, addr + (index << 2), x)

  }

  @inline final def remove(index: Int): Unit = {

    unsafe.copyMemory(addr + ((index + 1) << 2), addr + (index << 2), ({
      sizev -= 1
      sizev
    } - index) << 2)

  }

  /*@inline def binSearchX(key: Int, untilIndex: Int): Int = { TODO; see 11Jan2019
  }*/

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

    low - 1 // note that this is different from Java's binarySearch result

  }

  @inline def toArray: Array[Int] = {

    //byte[] array = new byte[(int) sizev];  // note that an unsafe array can exceed Int.MaxValue sizev, in which case this would fail

    val array: Array[Int] = new Array[Int](sizev)

    unsafe.copyMemory(null, addr, array, intArrayOffs, sizev << 2)

    array

  }

  @inline def toArray(l: Int): Array[Int] = {

    val array: Array[Int] = new Array[Int](l)

    unsafe.copyMemory(null, addr, array, intArrayOffs, l << 2)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Int] = {

    val array: Array[Int] = new Array[Int](until - from)

    unsafe.copyMemory(null, addr + (from << 2), array, intArrayOffs, (until - from) << 2)

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

  @inline def contains(x: Int, maxAddr: Long): Boolean = {

    var a = addr //addr + (max << 2) - 4

    while (a < maxAddr) {

      if (unsafe.getInt(a) == x)
        return true

      a += 4l

    }

    false

  }

  @inline def clone(padding: Int): IntArrayUnsafeS = {

    val bau: IntArrayUnsafeS = new IntArrayUnsafeS(sizev + padding, aligned = false)

    unsafe.copyMemory(addr, bau.getAddr, sizev << 2)

    bau

  }

  @inline def distinctSorted(): Unit = {

    // insertion sort - use only if array is small:

    var i = 1

    while (i < sizev) {

      var j = i

      while (j > 0 && get(j - 1) > get(j)) {

        val h: Int = get(j)

        update(j, get(j - 1))

        update(j - 1, h)

        j -= 1

      }

      i += 1

    }

    // we remove duplicates (should not occur in original DIMACS but might creep in during preparation phases)

    i = sizev - 1

    while (i > 0 && i < sizev) {

      if (get(i) == get(i - 1))
        remove(i - 1)
      else {

        i -= 1

        i + 1

      }

    }

  }

}
