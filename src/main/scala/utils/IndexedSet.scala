package utils

/**

 Weakly randomizable Int set with dual index structure (O(1) add, remove).

 Based on Java code from https://stackoverflow.com/questions/124671/picking-a-random-element-from-a-set

 Not well-tested yet (don't use in production). Not thread-safe. Not suitable as a source for cryptographically secure randomness.

*/
class IndexedSet(maxE: Int, rnd: scala.util.Random) {

  type E = Int

  var dta = new IntArrayUnsafeS(maxE, aligned = true)

  var idx = new IntArrayUnsafeS(maxE, initialValue = -1, aligned = true)

  var dtaLength = 0

  @inline def clear() = dtaLength = 0

  @inline def contains(item: E): Boolean = idx.get(item) >= 0 && idx.get(item) < dtaLength

  @inline def add(item: E): Unit = {

    if (idx.get(item) < 0 || idx.get(item) >= dtaLength) {

      dta.update(dtaLength, item)

      idx.update(item, dtaLength)

      dtaLength += 1

    }

  }

  @inline def removeAt(id: Int): E = {

    val item: E = dta.get(id)

    idx.update(item, -1)

    dtaLength -= 1

    if (id < dtaLength) {

      val lastItem: E = dta.get(dtaLength)

      idx.update(lastItem, id)

      dta.update(id, lastItem)

    }

    item

  }

  @inline def remove(item: E): Boolean = {

    val id = idx.get(item)

    if (id < 0 || id >= dtaLength)
      false
    else {

      removeAt(id)

      true

    }

  }

  @inline def get(i: Int): E = dta.get(i)

  @inline def getRandom(): E = dta.get(rnd.nextInt(dtaLength))

  @inline def getRandomOpt(): Option[E] = if (dtaLength == 0) None else Some(dta.get(rnd.nextInt(dtaLength)))

  @inline def getLast(): E = dta.get(dtaLength - 1)

  @inline def getRemoveRandom(): E =  removeAt(rnd.nextInt(dtaLength))

  @inline def getRemoveLast(): E = {

    dtaLength -= 1

    idx.update(dta.get(dtaLength), -1)

    dta.get(dtaLength)

  }

  @inline def size(): Int = dtaLength

}

