/**
  * delSAT
  *
  * Copyright (c) 2018, 2020 by Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package solving

import input.UNSAFEhelper.{addAllocOffHeapMemToGarbage, allocateOffHeapMem, _}

import it.unimi.dsi.fastutil.longs.LongOpenHashSet

import sharedDefs._

import scala.collection.mutable.ArrayBuffer

class NogoodReduciblesSequenceUnsafe(initialCapacity: Int) {

  type NogoodReducible = Long

  private[this] val bytesPerElement = 8 /*<-- reducible:Long*/
  // + 4/*<-- blocking eli:Int*/
  // To activate blocker elis, add 4 to slot (see above), look for other mentions of "blocker" in this class, and in BCP
  // omit all reducible list entries for which !isNegSetInPass(UNSAFE.getInt(addrOfItemInRedList + 8l)).
  // But doesn't seem to have any benefit in preliminary experiments.

  private[this] var noOfAvailableSlotsForItems = initialCapacity

  private[this] var a = allocateOffHeapMem(allocatedBytes(noOfAvailableSlotsForItems)) //new LongArrayUnsafeS(sizev = initialCapacity)

  private[this] var sizev = 0

  private[this] var cachedHashSet: LongOpenHashSet = null.asInstanceOf[LongOpenHashSet]

  @inline def allocatedBytes(allocatedItems: Int = noOfAvailableSlotsForItems): Int =
    allocatedItems * bytesPerElement

  @inline def addToGarbage(): Unit = {

    addAllocOffHeapMemToGarbage(a, allocatedBytes(noOfAvailableSlotsForItems)) //a.addToGarbage()

  }

  @inline def clearUS(): Unit = {

    sizev = 0

  }

  @inline def cutoffUS(whereExclusive: Int): Unit = {

    sizev = whereExclusive

  }

  @inline def getAddr: Long = a

  @inline def getBytesPerElement: Int = bytesPerElement

  @inline def getAddrOfItem(index: Int) = a + index * bytesPerElement // TODO: make shiftable?

  @inline def getReducibleUS(index: Int): NogoodReducible = UNSAFE.getLong(getAddrOfItem(index))

  @inline def removeByIndexUS(i: Int): Unit = {

    sizev -= 1

    if (i < sizev) {

      UNSAFE.copyMemory(getAddrOfItem(sizev), getAddrOfItem(i), bytesPerElement)

    }

  }

  @inline def removeByAddrUS(iAddr: Long): Unit = {

    sizev -= 1

    UNSAFE.copyMemory(getAddrOfItem(sizev), iAddr, bytesPerElement)

  }

  @inline def addReducibleUS(reducible: NogoodReducible): Unit = {

    if (sizev >= noOfAvailableSlotsForItems) { // should occur only rarely if we chose the initial size appropriately, however
      // it also depends on the number of learned nogoods which is difficult to predict.

      val newAvailableNoOfSlotsForItems = noOfAvailableSlotsForItems << 1 // sizev.get + incIfOverflow

      a = resizeOffHeapMem(a, allocatedBytes(noOfAvailableSlotsForItems),
        allocatedBytes(newAvailableNoOfSlotsForItems))

      noOfAvailableSlotsForItems = newAvailableNoOfSlotsForItems

    }

    UNSAFE.putLong(getAddrOfItem(sizev), reducible)

    sizev += 1

  }

  @inline def updateItemUS(index: Int, reducible: NogoodReducible) = {

    UNSAFE.putLong(getAddrOfItem(index), reducible)

  }


  @inline def swap(i: Int, j: Int, valueI: Long): Unit = {

    updateItemUS(i, getReducibleUS(j)) // if blockingElis are enabled, modify accordingly

    updateItemUS(j, valueI)

  }

  @inline def toArrayBufferOfReducibles: ArrayBuffer[NogoodReducible] = {

    val ab = ArrayBuffer[NogoodReducible]()

    var i = 0

    while (i < sizev) {

      ab.append(getReducibleUS(i))

      i += 1

    }

    ab

  }

  @inline def findReducibleUS(item: NogoodReducible): Int = {

    var i = 0

    while (i < sizev) {

      if (getReducibleUS(i) == item)
        return i

      i += 1

    }

    -1

  }

  @inline def containsReducible(item: NogoodReducible): Boolean = {

    findReducibleUS(item) != -1

  }

  @inline def toHashSetOfReducibles: LongOpenHashSet = {

    val hs = new LongOpenHashSet(64)

    var i = 0

    while (i < sizev) {

      hs.add(getReducibleUS(i))

      i += 1

    }

    cachedHashSet = hs

    hs

  }

  @inline def toHashSetOfReduciblesIncompl: LongOpenHashSet = {

    if (cachedHashSet == null) {

      toHashSetOfReducibles

    } else
      cachedHashSet

  }

  @inline def filterByReducibleUS(keepBy: NogoodReducible => Boolean): NogoodReduciblesSequenceUnsafe = {

    val ns = new NogoodReduciblesSequenceUnsafe(initialCapacity = sizev)

    var k = 0

    while (k < sizev) {

      if (keepBy(getReducibleUS(k)))
        ns.addReducibleUS(getReducibleUS(k))

      k += 1

    }

    ns

  }

  @inline def size(): Eli = sizev

}