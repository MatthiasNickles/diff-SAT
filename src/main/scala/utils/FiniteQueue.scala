/**
  * delSAT
  *
  * Copyright (c) 2018,2020 by Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import sharedDefs.rngGlobal

class FiniteQueue[A](q: scala.collection.mutable.Queue[A]) {

  @inline def enqueueFinite(elem: A, maxSize: Int) = {

    while (q.size >= maxSize) {
      q.dequeue
    }

    q.enqueue(elem)

  }

  @inline def front = q.front

  @inline def size = q.size

  @inline def isEmpty = q.isEmpty

  @inline def randomElement(limit: Int): A = {

    q.apply(rngGlobal.nextInt(limit))

  }

  @inline def dequeue: A = q.dequeue()

}