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
  * with random access and traversal.
  *
  * @param buffer
  * @param initiallyOccupiedInBuffer
  */
class ArrayValExtensibleLongUnsafe(var buffer: LongArrayUnsafeS, initiallyOccupiedInBuffer: Int = 0) {

  var contentLen = if (initiallyOccupiedInBuffer == -1) buffer.size else initiallyOccupiedInBuffer

  @inline def bufferSize: Int = buffer.size

  @inline def get(index: Int): Long = buffer.get(index)

  @inline def get(index: Long): Long = buffer.get(index)

  @inline def update(index: Int, value: Long): Unit = buffer.update(index, value)

  @inline def popLast: Long = {

    contentLen -= 1

    get(contentLen)

  }

  @inline def removeByIndex(index: Int): Unit = {

    if (index < contentLen - 1)
      update(index, popLast)
    else
      contentLen -= 1

  }

  @inline def removeByItem(item: Long): Unit = {

    removeByIndex(indexOf(item))

  }

  @inline def isEmpty: Boolean = contentLen == 0

  @inline def setSize(newSize: Int): Unit = contentLen = newSize

  @inline def traverseUntil(itemOp: Long => Boolean): Unit = {

    var i = 0

    var stop = false

    while (!stop) {

      stop = i >= contentLen || itemOp(buffer.get(i))

      i += 1

    }

  }

  @inline def contains(item: Long): Boolean = contains(item, contentLen)

  @inline def contains(item: Long, until: Int): Boolean = {

    var i = until - 1

    while (i >= 0) {

      if (buffer.get(i) == item)
        return true

      i -= 1

    }

    false

  }

  @inline def containsBy(item: Long, until: Int, by: Long => Int): Boolean = {

    var i = until - 1

    while (i >= 0) {

      if (by(buffer.get(i)) == by(item))
        return true

      i -= 1

    }

    false

  }

  @inline def indexOf(item: Long): Int = {

    var i = 0

    while (i < size) {

      if (buffer.get(i) == item)
        return i

      i += 1

    }

    -1

  }

  @inline def append(item: Long): Unit = {

    if (contentLen >= buffer.size) {

      val bufferOldAddr = buffer.getAddr

      val additionalSpace = contentLen >> 1

      buffer = buffer.cloneToNew(padding = additionalSpace, contentLen, cutOff = false)

      if (buffer.getAddr != bufferOldAddr) {

        input.UNSAFEhelper.UNSAFE.freeMemory(bufferOldAddr) // (alternatively we could add the old buffer address to the UNSAFEhelper garbage)

      }

    }

    buffer.update(contentLen, item)

    contentLen += 1

  }

  @inline def appendNoExpansion(item: Long): Boolean = {

    (contentLen < buffer.size) && {

      buffer.update(contentLen, item)

      contentLen += 1

      true

    }

  }

  @inline def clear(): Unit = contentLen = 0

  @inline def size(): Eli = contentLen

  @inline def sort(by: Long => Double): Unit = {

    buffer.sortByInplace(by = by, until = contentLen)

  }

  @inline def freeBuffer(): Unit = buffer.free()

  @inline def addToGarbageBuffer(): Unit = buffer.addToGarbage()

}