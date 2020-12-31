package utils

import java.util.Random

import it.unimi.dsi.fastutil.longs.{Long2IntOpenHashMap, LongArrayList}

/**
  * For positive (Scala-)Longs only (in case of diff-SAT: nogood reducibles). Not suitable for cryptographic purposes.
  */
class RandomLongSet(expectedNoOfItems: Int = 1024) {

  val data = new LongArrayList(expectedNoOfItems)

  val index = new Long2IntOpenHashMap(expectedNoOfItems)
  // ^ maps items to their indices in data

  index.defaultReturnValue(-1)  // important because otherwise the "not found" value would be 0 which is a valid item in our use case

  @inline def clear(): Unit = {

    index.clear()

    data.clear()

  }

  @inline def contains(item: Long): Boolean = {

    index.containsKey(item)

  }

  @inline def add(item: Long): Unit = {  // NB: in contrast to similar standard lib methods, we avoid returning (boxed) Boolean success indicators

    if (!index.containsKey(item)) {

      index.put(item, data.size)

      data.add(item)

    }

  }

  @inline def removeAt(id: Int): Unit = {

    if (id < data.size) {

      index.remove(data.getLong(id))

      val last: Long = data.removeLong(data.size - 1)

      if (id < data.size) {

        index.put(last, id)

        data.set(id, last)

      }

    }

  }

  @inline def size: Int = data.size

  @inline def remove(item: Long): Unit = {

    val id = index.get(item)

    if (id >= 0)
      removeAt(id)

  }

  @inline def get(id: Int): Long = data.getLong(id)

  @inline def getRandomItem(rnd: Random): Long = {

    val id = rnd.nextInt(data.size)

    data.getLong(id)

  }

  @inline def pollRandomItem(rnd: Random): Long = {

    val id: Int = rnd.nextInt(data.size)

    val res: Long = data.getLong(id)

    removeAt(id)

    res

  }


}