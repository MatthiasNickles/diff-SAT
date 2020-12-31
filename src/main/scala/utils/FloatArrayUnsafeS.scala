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

import sun.misc.Unsafe
import input.UNSAFEhelper._

/** This is not a general-purpose unsafe class - designed for use in project diff-SAT only! */
object FloatArrayUnsafeS {

  //private[this] var unsafe: Unsafe = null

  var alignment = 128 // UNSAFE.pageSize  Observe that unsafe's allocateMemory does some alignment (to value size) by itself

  var internalPaddingFact = 1 // multiple of actual alignment (see below)

  var floatArrayOffs = -1

  @inline def init(us: Unsafe): Unit = {

    //unsafe = us

    floatArrayOffs = UNSAFE.arrayBaseOffset(classOf[Array[Float]])

  }

  @inline def getUnsafe: Unsafe = UNSAFE

}

/** This is not a general-purpose unsafe array class - designed for use in project diff-SAT only! */
class FloatArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  //private[this] val unsafe = ByteArrayUnsafeS.getUnsafe  // without private[this] the field access in the bytecode would be by invokevirtual

  private[this] var addr: Long = 0L

  private[this] var allocated: Long = 0l

  if (!aligned) {

    allocated = sizev << 2

    addr = allocateOffHeapMem(allocated)

  } else {

    allocated = (sizev << 2) + FloatArrayUnsafeS.alignment +
      FloatArrayUnsafeS.alignment * FloatArrayUnsafeS.internalPaddingFact

    addr = allocateOffHeapMem(allocated)

    if (FloatArrayUnsafeS.alignment > 0l && (addr & (FloatArrayUnsafeS.alignment - 1l)) != 0)
      addr += (FloatArrayUnsafeS.alignment - (addr & (FloatArrayUnsafeS.alignment - 1)))

    addr += FloatArrayUnsafeS.alignment * FloatArrayUnsafeS.internalPaddingFact

  }

  @inline def this(values: Array[Float], aligned: Boolean) {

    this(sizev = values.length, aligned = aligned)

    setFromArray(values)

  }

  @inline def this(s: Int, initValue: Float, aligned: Boolean) {

    this(sizev = s, aligned = aligned)

    var i = 0

    while(i < s) {

      update(i, initValue)

      i += 1

    }

  }

  @inline def free(): Unit = freeOffHeapMem(addr, allocated)

  @inline def size(): Int = sizev

  @inline def setFromArray(values: Array[Float]): Unit = {

    UNSAFE.copyMemory(values, FloatArrayUnsafeS.floatArrayOffs, null, addr, values.length << 2)

  }

  @inline def get(index: Int): Float = {

    UNSAFE.getFloat(addr + (index << 2))

  }

  @inline def get(index: Long): Float = {

    UNSAFE.getFloat(addr + (index << 2))

  }

  @inline def first: Float = {

    UNSAFE.getFloat(addr)

  }

  @inline def update(index: Int, value: Float): Unit = {

    UNSAFE.putFloat(addr + (index << 2), value)

  }

  @inline def update(index: Long, value: Float): Unit = {

    UNSAFE.putFloat(addr + (index << 2), value)

  }

  @inline final def incBy(index: Int, by: Float): Float = {

    val newValue = UNSAFE.getFloat(addr + (index << 2)) + by

    UNSAFE.putFloat(addr + (index << 2), newValue)

    newValue

  }

  @inline final def mulBy(index: Int, by: Float): Unit = {

    UNSAFE.putFloat(addr + (index << 2), UNSAFE.getFloat(addr + (index << 2)) * by)

  }

  @inline def toArray: Array[Float] = {

    val array = new Array[Float](sizev)

    UNSAFE.copyMemory(null, addr, array, FloatArrayUnsafeS.floatArrayOffs, sizev << 2)

    array

  }

  @inline def toArray(l: Int): Array[Float] = {

    val array = new Array[Float](l)

    UNSAFE.copyMemory(null, addr, array, FloatArrayUnsafeS.floatArrayOffs, l << 2)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Float] = {

    val array = new Array[Float](until - from)

    UNSAFE.copyMemory(null, addr + (from << 2), array, FloatArrayUnsafeS.floatArrayOffs, (until - from) << 2)

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

  @inline def clone(padding: Int): FloatArrayUnsafeS = {

    val bau: FloatArrayUnsafeS = new FloatArrayUnsafeS(sizev + padding, aligned = aligned)

    UNSAFE.copyMemory(addr, bau.getAddr, sizev << 2)

    bau

  }

}
