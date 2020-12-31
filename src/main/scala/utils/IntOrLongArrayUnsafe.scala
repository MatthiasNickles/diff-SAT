/**
  * diff-SAT
  *
  * Copyright (c) 2018-2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */
  
package utils

@deprecated trait IntOrLongArrayUnsafe[@specialized T <: AnyVal] {  // nope (cannot avoid boxing)

  @inline def size(): Int

  @inline def getAddr: Long

  @inline def setAddr(newAddr: Long): Unit

  @inline def toArray: Array[T]

  @inline def get(index: Int): T

  @inline def get(index: Long): T

  @inline def popLast: T

  @inline def update(index: Int, value: T): Unit

  @inline def removeByIndex(index: Int): Unit

  @inline def cloneToNew(padding: Int, keep: Int, cutOff: Boolean): IntOrLongArrayUnsafe[T]

  @inline def free(): Unit

  @inline def addToGarbage(): Unit

}
