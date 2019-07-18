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

import sun.misc.Unsafe

/** This is not a general-purpose unsafe class - designed for use in project delSAT only! */
object FloatArrayUnsafeS {

  var unsafe: Unsafe = null

  var alignment = 128 // unsafe.pageSize

  var internalPaddingFact = 1 // multiple of actual alignment (see below)

  var floatArrayOffs = -1

  def init(us: Unsafe): Unit = {

    unsafe = us

    floatArrayOffs = unsafe.arrayBaseOffset(classOf[Array[Float]])

  }

}

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only! */
class FloatArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  var isSorted: Boolean = false

  var addr: Long = 0L

  if (!aligned)
    addr = FloatArrayUnsafeS.unsafe.allocateMemory(sizev << 2)
  else {

    addr = FloatArrayUnsafeS.unsafe.allocateMemory((sizev << 2) + FloatArrayUnsafeS.alignment +
      FloatArrayUnsafeS.alignment * FloatArrayUnsafeS.internalPaddingFact)

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

  @inline def free(): Unit = FloatArrayUnsafeS.unsafe.freeMemory(addr)

  @inline def size(): Int = sizev

  @inline def setFromArray(values: Array[Float]): Unit = {

    FloatArrayUnsafeS.unsafe.copyMemory(values, FloatArrayUnsafeS.floatArrayOffs, null, addr, values.length << 2)

  }

  @inline def get(index: Int): Float = {

    FloatArrayUnsafeS.unsafe.getFloat(addr + (index << 2))

  }

  @inline def get(index: Long): Float = {

    FloatArrayUnsafeS.unsafe.getFloat(addr + (index << 2))

  }

  @inline def first: Float = {

    FloatArrayUnsafeS.unsafe.getFloat(addr)

  }

  @inline def update(index: Int, value: Float): Unit = {

    FloatArrayUnsafeS.unsafe.putFloat(addr + (index << 2), value)

  }

  @inline def update(index: Long, value: Float): Unit = {

    FloatArrayUnsafeS.unsafe.putFloat(addr + (index << 2), value)

  }

  @inline def remove(index: Int): Unit = {

    FloatArrayUnsafeS.unsafe.copyMemory(addr + ((index + 1) << 2), addr + (index << 2), ({
      sizev -= 1
      sizev
    } - index) << 2)

  }

  @inline def toArray: Array[Float] = {

    val array = new Array[Float](sizev)

    FloatArrayUnsafeS.unsafe.copyMemory(null, addr, array, FloatArrayUnsafeS.floatArrayOffs, sizev << 2)

    array

  }

  @inline def toArray(l: Int): Array[Float] = {

    val array = new Array[Float](l)

    FloatArrayUnsafeS.unsafe.copyMemory(null, addr, array, FloatArrayUnsafeS.floatArrayOffs, l << 2)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Float] = {

    val array = new Array[Float](until - from)

    FloatArrayUnsafeS.unsafe.copyMemory(null, addr + (from << 2), array, FloatArrayUnsafeS.floatArrayOffs, (until - from) << 2)

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

  @inline def clone(padding: Int): FloatArrayUnsafeS = {

    val bau: FloatArrayUnsafeS = new FloatArrayUnsafeS(sizev + padding, aligned = aligned)

    FloatArrayUnsafeS.unsafe.copyMemory(addr, bau.addr, sizev << 2)

    bau

  }

}
