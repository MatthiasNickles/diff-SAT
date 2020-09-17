/**
  * delSAT
  *
  * Copyright (c) 2018,2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import sun.misc.Unsafe
import input.UNSAFEhelper._

/** This is not general-purpose code for using unsafe memory - designed for use in project delSAT only! */
object DoubleArrayUnsafeS {

  //private[this] var unsafe: Unsafe = null

  var alignment = 0

  var internalPaddingFact = 0 // multiple of actual alignment (see below)

  var doubleArrayOffs = -1

  @inline def init(us: Unsafe): Unit = {

    //unsafe = us

    doubleArrayOffs = UNSAFE.arrayBaseOffset(classOf[Array[Double]])

  }

  @inline def getUnsafe: Unsafe = UNSAFE

}

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only! */
class DoubleArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  //private[this] val unsafe = ByteArrayUnsafeS.getUnsafe  // without private[this] the field access in the bytecode would be by invokevirtual

  private[this] var addr: Long = 0L

  private[this] var allocated: Long = 0l

  if (DoubleArrayUnsafeS.alignment == 0) {

    allocated = sizev << 3

    addr = allocateOffHeapMem(allocated)

  } else {

    allocated = (sizev << 3) + DoubleArrayUnsafeS.alignment +
      DoubleArrayUnsafeS.alignment * DoubleArrayUnsafeS.internalPaddingFact

    addr = allocateOffHeapMem(allocated)

    if (DoubleArrayUnsafeS.alignment > 0l && (addr & (DoubleArrayUnsafeS.alignment - 1l)) != 0)
      addr += (DoubleArrayUnsafeS.alignment - (addr & (DoubleArrayUnsafeS.alignment - 1)))

    addr += DoubleArrayUnsafeS.alignment * DoubleArrayUnsafeS.internalPaddingFact

  }

  @inline def this(values: Array[Double], aligned: Boolean) {

    this(sizev = values.length, aligned = aligned)

    setFromArray(values)

  }

  @inline def this(s: Int, initValue: Double, aligned: Boolean) {

    this(sizev = s, aligned = aligned)

    var i = 0

    while(i < s) {

      update(i, initValue)

      i += 1

    }

  }

  @inline def free(): Unit = freeOffHeapMem(addr, allocated)

  @inline def size(): Int = sizev

  @inline def setFromArray(values: Array[Double]): Unit = {

    UNSAFE.copyMemory(values, DoubleArrayUnsafeS.doubleArrayOffs, null, addr, values.length << 3)

  }

  @inline def get(index: Int): Double = {

    UNSAFE.getDouble(addr + (index << 3))

  }

  @inline def get(index: Long): Double = {

    UNSAFE.getDouble(addr + (index << 3))

  }

  @inline def first: Double = {

    UNSAFE.getDouble(addr)

  }

  @inline def update(index: Int, value: Double): Unit = {

    UNSAFE.putDouble(addr + (index << 3), value)

  }

  @inline def update(index: Long, value: Double): Unit = {

    UNSAFE.putDouble(addr + (index << 3), value)

  }

  @inline final def incBy(index: Int, by: Double): Double = {

    val newValue = UNSAFE.getDouble(addr + (index << 3)) + by

    UNSAFE.putDouble(addr + (index << 3), newValue)

    newValue

  }

  @inline final def mulBy(index: Int, by: Double): Unit = {

    UNSAFE.putDouble(addr + (index << 3), UNSAFE.getDouble(addr + (index << 3)) * by)

  }

  @inline def toArray: Array[Double] = {

    val array = new Array[Double](sizev)

    UNSAFE.copyMemory(null, addr, array, DoubleArrayUnsafeS.doubleArrayOffs, sizev << 3)

    array

  }

  @inline def toArray(l: Int): Array[Double] = {

    val array = new Array[Double](l)

    UNSAFE.copyMemory(null, addr, array, DoubleArrayUnsafeS.doubleArrayOffs, l << 3)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Double] = {

    val array = new Array[Double](until - from)

    UNSAFE.copyMemory(null, addr + (from << 3), array, DoubleArrayUnsafeS.doubleArrayOffs, (until - from) << 3)

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

  @inline def clone(padding: Int): DoubleArrayUnsafeS = {

    val bau: DoubleArrayUnsafeS = new DoubleArrayUnsafeS(sizev + padding, aligned = aligned)

    UNSAFE.copyMemory(addr, bau.getAddr, sizev << 3)

    bau

  }

}
