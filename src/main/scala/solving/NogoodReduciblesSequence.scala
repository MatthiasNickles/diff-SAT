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

package solving

import it.unimi.dsi.fastutil.longs.LongArrayList


@deprecated class NogoodReduciblesSequence(capacity: Int) extends LongArrayList(capacity) {  // consider using NogoodReduciblesSequenceUnsafe instead

  type NogoodReducible = Long

  @inline def clearUS(): Unit = size = 0

  @inline def cutoffUS(whereExclusive: Int): Unit = size = whereExclusive

  @inline def getUS(index: Int): NogoodReducible = a(index)

  @inline def removeUS(k: NogoodReducible): Unit = {

    this.rem(k)

  }

  @inline def removeByIndexUS(i: Int): Unit = {

    if(i < size - 1)
      set(i, getUS(size - 1))

    size -= 1

  }

  @inline def addUS(k: NogoodReducible): Unit = {

    if (size >= a.length) {

      val t = new Array[NogoodReducible](/*(a.length << 1) + 1*/a.length + 128)

      if(size > 0)
        System.arraycopy(a, 0, t, 0, size)

      a = t.asInstanceOf[Array[NogoodReducible]]

    }

    a.update(size, k)

    size += 1

  }

  @inline def getArray: Array[NogoodReducible] = a

  @inline def count(item: NogoodReducible) = {

    var c = 0

    var i = 0

    while(i < size) {

      if(getUS(i) == item)
        c += 1

      i += 1

    }

    c

  }

}