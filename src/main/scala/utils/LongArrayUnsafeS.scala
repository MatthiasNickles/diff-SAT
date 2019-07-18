/**
  * delSAT
  *
  * Copyright (c) 2018,2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import it.unimi.dsi.fastutil.longs.LongArrayList

import sun.misc.Unsafe

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only! */
class LongArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  val unsafe: Unsafe = sharedDefs.unsafe

  val alignment = 128 //unsafe.pageSize

  val internalPaddingFact = 1 // multiple of actual alignment (see below)

  val longArrayOffs = unsafe.arrayBaseOffset(classOf[Array[Long]])

  val addr: Long = if (!aligned)
    unsafe.allocateMemory(sizev << 3)
  else {

    var addra = unsafe.allocateMemory((sizev << 3) + alignment + alignment * internalPaddingFact)

    if (alignment > 0l && (addra & (alignment - 1l)) != 0)
      addra += (alignment - (addra & (alignment - 1)))

    addra + alignment * internalPaddingFact

  }

  @inline def this(values: Array[Long], aligned: Boolean) {

    this(sizev = values.length, aligned = aligned)

    setFromArray(values)

  }

  @inline def this(values: LongArrayList, aligned: Boolean) {

    this(sizev = values.size, aligned = aligned)

    var i = 0

    while (i < sizev) {

      update(i, values.getLong((i)))

      i += 1

    }

  }

  @inline def this(s: Int, initValue: Long, aligned: Boolean) {

    this(sizev = s, aligned = aligned)

    var i = 0

    while (i < s) {

      update(i, initValue)

      i += 1

    }

  }

  @inline def free(): Unit = unsafe.freeMemory(addr)

  @inline final def size(): Int = sizev

  @inline def setFromArray(values: Array[Long]): Unit = {

    unsafe.copyMemory(values, longArrayOffs, null, addr, values.length << 3)

  }

  @inline final def compareAndUpdate(index: Int, expectedValue: Long, newValue: Long): Boolean = {

    unsafe.compareAndSwapLong(null, addr + (index << 3), expectedValue, newValue)

  }

  @inline final def compareWithZeroAndUpdate(index: Int, newValue: Long): Boolean = {

    unsafe.compareAndSwapLong(null, addr + (index << 3), 0l, newValue)

  }

  @inline final def get(index: Int): Long = {

    unsafe.getLong(addr + (index << 3))

  }

  @inline final def get(index: Long): Long = {

    unsafe.getLong(addr + (index << 3))

  }

  @inline final def first: Long = {

    unsafe.getLong(addr)

  }

  @inline final def update(index: Int, value: Long): Unit = {

    unsafe.putLong(addr + (index << 3), value)

  }

  @inline final def update(index: Int, value: Int): Unit = {

    unsafe.putLong(addr + (index << 3), value)

  }

  @inline final def update(index: Long, value: Long): Unit = {

    unsafe.putLong(addr + (index << 3), value)

  }

  @inline final def inc(index: Int): Long = {

    unsafe.getAndAddLong(null, addr + (index << 3), 1)

  }

  @inline final def dec(index: Int): Long = {

    unsafe.getAndAddLong(null, addr + (index << 3), -1) - 1

  }

  @inline final def incBy(index: Int, x: Long): Unit = {

    unsafe.getAndAddLong(null, addr + (index << 3), x)

  }

  @inline final def remove(index: Int): Unit = {

    unsafe.copyMemory(addr + ((index + 1) << 3), addr + (index << 3), ({
      sizev -= 1
      sizev
    } - index) << 3)

  }

  @inline def toArray: Array[Long] = {

    val array = new Array[Long](sizev)

    unsafe.copyMemory(null, addr, array, longArrayOffs, sizev << 3)

    array

  }

  @inline def toArray(l: Int): Array[Long] = {

    val array = new Array[Long](l)

    unsafe.copyMemory(null, addr, array, longArrayOffs, l << 3)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Long] = {

    val array = new Array[Long](until - from)

    unsafe.copyMemory(null, addr + (from << 3), array, longArrayOffs, (until - from) << 3)

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

  @inline def clone(padding: Int): LongArrayUnsafeS = {

    val bau: LongArrayUnsafeS = new LongArrayUnsafeS(sizev + padding, aligned = aligned)

    unsafe.copyMemory(addr, bau.addr, sizev << 3)

    bau

  }

}
