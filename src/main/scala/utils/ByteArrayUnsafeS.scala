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

import input.UNSAFEhelper._
import sun.misc.Unsafe

/** This is not a general-purpose unsafe (off-heap) byte array class - designed for use in project delSAT only! */
object ByteArrayUnsafeS {

  //private[this] var unsafe: Unsafe = null

  //var alignment = 128 //UNSAFE.pageSize

  //var internalPaddingFact = 1  // multiple of actual alignment (see below)

  var byteArrayOffset = -1l

  def init(us: Unsafe): Unit = {

    byteArrayOffset = UNSAFE.arrayBaseOffset(classOf[Array[Byte]])

  }

  @inline def getUnsafe: Unsafe = UNSAFE

}

/** This is not a general-purpose unsafe byte array class - designed for use in project delSAT only! */
class ByteArrayUnsafeS(var sizev: Int /*, aligned: Boolean*/) {

  //var isSorted: Boolean = false

  private[this] var addr: Long = 0L

  //private[this] val unsafe = ByteArrayUnsafeS.getUnsafe

  private[this] val stringBuilder: java.lang.StringBuilder = new java.lang.StringBuilder(sizev)

  addr = allocateOffHeapMem(sizev)  /*{
    
    val alignment = 64

    addr = /*UNSAFE.allocateMemory*/allocateOffHeapMem((sizev) + alignment + alignment * 8/*ByteArrayUnsafeS.internalPaddingFact*/)

    if (alignment > 0l && (addr & (alignment - 1l)) != 0)
      addr += (alignment - (addr & (alignment - 1)))

    addr += alignment * 8/*ByteArrayUnsafeS.internalPaddingFact*/

  }*/

  private[this] val addrMid: Long = addr + ((sizev >> 1))


  @inline def this(values: Array[Byte]) = {

    this(sizev = values.length)

    setFromArray(values)

  }

  @inline def this(s: Int, initialValue: Byte /*, aligned: Boolean*/) = {

    this(sizev = s /*, aligned = aligned*/)

    fill(initialValue)

  }

  @inline def fill(value: Byte, length: Int = sizev): Unit = {

    UNSAFE.setMemory(addr, length, value)

  }

  @inline def free(): Unit = freeOffHeapMem(addr, sizev) //UNSAFE.freeMemory(addr)

  @inline def addToGarbage(): Unit = addAllocOffHeapMemToGarbage(addr, sizev)

  @inline def size(): Int = sizev

  @inline override def hashCode(): Int = {

    var h = 1

    var i = 0

    while (i < sizev) {

      h = 31 * h + get(i)

      i += 1

    }

    h

  }

  @inline override def equals(obj: Any): Boolean = {

    if (obj.isInstanceOf[ByteArrayUnsafeS] && obj != null)
      this.hashCode == obj.asInstanceOf[ByteArrayUnsafeS].hashCode
    else
      super.equals(obj)

  }

  @inline def setFromArray(values: Array[Byte]): Unit = {

    UNSAFE.copyMemory(values, ByteArrayUnsafeS.byteArrayOffset, null, addr, values.length)

  }

  @inline def setFromUnsafeByteArray(values: ByteArrayUnsafeS): Unit = {

    UNSAFE.copyMemory(values, 0l, null, addr, values.sizev)

  }

  @inline def get(index: Int): Byte = {

    UNSAFE.getByte(addr + index)

  }

  @inline def getMid(index: Int): Byte = {

    UNSAFE.getByte(addrMid + index)

  }

  @inline def get(index: Long): Byte = {

    UNSAFE.getByte(addr + index)

  }

  @inline def getBoolean(index: Int): Boolean = {

    UNSAFE.getByte(addr + index) != 0x00.toByte // NB: caller specific. There is no "norm" for how to represent Booleans as bytes

  }

  @inline def first: Byte = {

    UNSAFE.getByte(addr)

  }

  @inline def update(index: Int, value: Byte): Unit = {

    UNSAFE.putByte(addr + index, value)

  }

  @inline def updateMid(index: Int, value: Byte): Unit = {

    UNSAFE.putByte(addrMid + index, value)

  }

  @inline def update(index: Long, value: Byte): Unit = {

    UNSAFE.putByte(addr + index, value)

  }

  /*
  @inline def update(index: Int, value: Boolean): Unit = {

   UNSAFE.putByte(addr + index, if (value) 0xFF.toByte else 0x00.toByte) // NB: caller specific. There is no "norm" for how to represent Booleans as bytes

  }


  @inline def updateMid(index: Int, value: Boolean): Unit = {

    UNSAFE.putByte(addrMid + index, if (value) 0xFF.toByte else 0x00.toByte) // NB: caller specific. There is no "norm" for how to represent Booleans as bytes

  }*/


  @inline def toArray: Array[Byte] = {

    val array = new Array[Byte](sizev)

    UNSAFE.copyMemory(null, addr, array, ByteArrayUnsafeS.byteArrayOffset, sizev)

    array

  }

  @inline def toArray(l: Int): Array[Byte] = {

    val array = new Array[Byte](l)

    UNSAFE.copyMemory(null, addr, array, ByteArrayUnsafeS.byteArrayOffset, l)

    array

  }

  @inline def toArray(from: Int, until: Int): Array[Byte] = {

    val array = new Array[Byte](until - from)

    UNSAFE.copyMemory(null, addr + (from), array, ByteArrayUnsafeS.byteArrayOffset, (until - from))

    array

  }

  @inline override def toString: String = {

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

  @inline def toBitString: String = {

    stringBuilder.setLength(0)

    var i = 0

    while (i < sizev) {

      stringBuilder.append(
        if (get(i) != 0x00.toByte)
          '1'
        else
          '0'
      )

      i += 1

    }

    stringBuilder.toString

  }

  @inline def toBitStringLocal: String = {

    val stringBuilder: java.lang.StringBuilder = new java.lang.StringBuilder(sizev)

    var i = 0

    while (i < sizev) {

      stringBuilder.append(
        if (get(i) != 0x00.toByte)
          '1'
        else
          '0'
      )

      i += 1

    }

    stringBuilder.toString

  }

  @inline def getAddr: Long = addr

  @inline def clone(padding: Int = 0): ByteArrayUnsafeS = {

    val bau: ByteArrayUnsafeS = new ByteArrayUnsafeS(sizev + padding /*, aligned = aligned*/)

    UNSAFE.copyMemory(addr, bau.getAddr, sizev)

    bau

  }

}
