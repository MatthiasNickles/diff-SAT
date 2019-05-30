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

import sun.misc.Unsafe

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only! */
object ByteArrayUnsafeS {

  var unsafe: Unsafe = null

  var alignment = 128 //unsafe.pageSize

  var internalPaddingFact = 1  // multiple of actual alignment (see below)

  var byteArrayOffset = -1l

  def init(us: Unsafe): Unit = {

    unsafe = us

    byteArrayOffset = unsafe.arrayBaseOffset(classOf[Array[Byte]])

  }

}

/** This is not a general-purpose unsafe array class - designed for use in project delSAT only! */
class ByteArrayUnsafeS(var sizev: Int, aligned: Boolean) {

  var isSorted: Boolean = false

  var addr: Long = 0L

  if (!aligned)
    addr = ByteArrayUnsafeS.unsafe.allocateMemory(sizev)
  else {

    addr = ByteArrayUnsafeS.unsafe.allocateMemory((sizev) + ByteArrayUnsafeS.alignment + ByteArrayUnsafeS.alignment * ByteArrayUnsafeS.internalPaddingFact)

    if (ByteArrayUnsafeS.alignment > 0l && (addr & (ByteArrayUnsafeS.alignment - 1l)) != 0)
      addr += (ByteArrayUnsafeS.alignment - (addr & (ByteArrayUnsafeS.alignment - 1)))

    addr += ByteArrayUnsafeS.alignment * ByteArrayUnsafeS.internalPaddingFact

  }

  @inline def this(values: Array[Byte], aligned: Boolean) = {

    this(sizev = values.length, aligned = aligned)

    setFromArray(values)

  }

  @inline def this(s: Int, initValue: Byte, aligned: Boolean) = {

    this(sizev = s, aligned = aligned)

    fill(initValue)

  }

  @inline def fill(value: Byte): Unit= {

    ByteArrayUnsafeS.unsafe.setMemory(addr, sizev, value)

  }

  @inline def free(): Unit = ByteArrayUnsafeS.unsafe.freeMemory(addr)

  @inline def size(): Int = sizev

  @inline def setFromArray(values: Array[Byte]): Unit = {

    ByteArrayUnsafeS.unsafe.copyMemory(values, ByteArrayUnsafeS.byteArrayOffset, null, addr, values.length)

  }

  @inline def get(index: Int): Byte = {

    ByteArrayUnsafeS.unsafe.getByte(addr + index)

  }

  @inline def get(index: Long): Byte = {

    ByteArrayUnsafeS.unsafe.getByte(addr + index)

  }

  @inline def getBoolean(index: Int): Boolean = {

    ByteArrayUnsafeS.unsafe.getByte(addr + index) != 0x00.toByte  // NB: caller specific. There is no "norm" for how to represent Booleans as bytes

  }

  @inline def first: Byte = {

    ByteArrayUnsafeS.unsafe.getByte(addr)

  }

  @inline def update(index: Int, value: Byte): Unit = {

    ByteArrayUnsafeS.unsafe.putByte(addr + index, value)

  }

  @inline def update(index: Long, value: Byte): Unit = {

    ByteArrayUnsafeS.unsafe.putByte(addr + index, value)

  }

  @inline def update(index: Int, value: Boolean): Unit = {

    ByteArrayUnsafeS.unsafe.putByte(addr + index, if (value) 0xFF.toByte else 0x00.toByte) // NB: caller specific. There is no "norm" for how to represent Booleans as bytes

  }

  @inline def remove(index: Int): Unit = {

    ByteArrayUnsafeS.unsafe.copyMemory(addr + ((index + 1)), addr + (index), ({
      sizev -= 1
      sizev
    } - index))

  }

  @inline def toArray: Array[Byte] = {

    val array = new Array[Byte](sizev)

    ByteArrayUnsafeS.unsafe.copyMemory(null, addr, array, ByteArrayUnsafeS.byteArrayOffset, sizev)

    array

  }

  @inline def toArray(l: Int): Array[Byte] = {

    val array = new Array[Byte](l)

    ByteArrayUnsafeS.unsafe.copyMemory(null, addr, array, ByteArrayUnsafeS.byteArrayOffset, l)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Byte] = {

    val array = new Array[Byte](until - from)

    ByteArrayUnsafeS.unsafe.copyMemory(null, addr + (from), array, ByteArrayUnsafeS.byteArrayOffset, (until - from))

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

  @inline def clone(padding: Int): ByteArrayUnsafeS = {

    val bau: ByteArrayUnsafeS = new ByteArrayUnsafeS(sizev + padding, aligned = aligned)

    ByteArrayUnsafeS.unsafe.copyMemory(addr, bau.addr, sizev)

    bau

  }

}
