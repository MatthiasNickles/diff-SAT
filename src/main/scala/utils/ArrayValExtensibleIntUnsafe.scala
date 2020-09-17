/**
  * delSAT
  *
  * Copyright (c) 2018, 2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import sharedDefs.Eli

/**
  * Unsafe low-level non-boxing replacement for a growable-only ArrayBuffer. Similar to ArrayBuilder, but
  * with random access and traversal. NB: couldn't avoid boxing in bytecode with
  * the generic [@specialized T (Int/Long)] variant (with Scala 2.13.1)
  *
  * @param buffer
  * @param initiallyOccupiedInBuffer
  */
class ArrayValExtensibleIntUnsafe(var buffer: IntArrayUnsafeS, initiallyOccupiedInBuffer: Int = 0) {

  var contentLen = if (initiallyOccupiedInBuffer == -1) buffer.size else initiallyOccupiedInBuffer

  @inline def getContent: Array[Int] = {

    buffer.toArray.take(contentLen)

  }

  @inline def getContentUnsafe: IntArrayUnsafeS = {

    buffer.cloneToNew(padding = 0, keep = contentLen, cutOff = true)

  }

  @inline def length: Int = contentLen

  @inline def bufferSize: Int = buffer.size

  @inline def get(index: Int): Int = buffer.get(index)

  @inline def get(index: Long): Int = buffer.get(index)

  @inline def update(index: Int, value: Int): Unit = buffer.update(index, value)

  @inline def popLast: Int = {

    contentLen -= 1

    get(contentLen)

  }

  @inline def removeByIndex(index: Int): Unit = {

    if (index < contentLen - 1)
      update(index, popLast)
    else
      contentLen -= 1

  }

  @inline def removeByItem(item: Int): Unit = {

    removeByIndex(indexOf(item))

  }

  @inline def isEmpty: Boolean = contentLen == 0

  @inline def traverseUntil(itemOp: Int => Boolean): Unit = {

    var i = 0

    var stop = false

    while (!stop) {

      stop = i >= contentLen || itemOp(buffer.get(i))

      i += 1

    }

  }

  @inline def contains(item: Int, until: Int): Boolean = {

    var i = until - 1

    while (i >= 0) {

      if (buffer.get(i) == item)
        return true

      i -= 1

    }

    false

  }

  @inline def containsBy(item: Int, until: Int, by: Int => Int): Boolean = {

    var i = until - 1

    while (i >= 0) {

      if (by(buffer.get(i)) == by(item))
        return true

      i -= 1

    }

    false

  }

  @inline def indexOf(item: Int): Int = {

    var i = 0

    while (i < size) {

      if (buffer.get(i) == item)
        return i

      i += 1

    }

    -1

  }

  @inline def append(item: Int): Unit = {

    if (contentLen >= buffer.size) {

      val bufferOld = buffer

      val additionalSpace = contentLen >> 1

      buffer = buffer.cloneToNew(padding = additionalSpace, keep = contentLen, cutOff = false)

      if (buffer.getAddr != bufferOld.getAddr) {

        bufferOld.free() // (alternatively we could add the old buffer address to the UNSAFEhelper garbage)

      }

    }

    buffer.update(contentLen, item)

    contentLen += 1

  }

  @inline def appendNoExpansion(item: Int): Boolean = {

    (contentLen < buffer.size) && {

      buffer.update(contentLen, item)

      contentLen += 1

      true

    }

  }

  @inline def clear(): Unit = contentLen = 0

  @inline def size(): Eli = contentLen

  @inline def freeBuffer(): Unit = buffer.free()

  @inline def addToGarbageBuffer(): Unit = buffer.addToGarbage()

}