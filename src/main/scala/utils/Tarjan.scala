package utils

import com.carrotsearch.hppc.IntObjectHashMap

import scala.collection.mutable

@deprecated object Tarjan {

  /** Original: http://danlec.com/st4k#questions/18289991, modified by M. Nickles */
  def trajanRec(g: IntObjectHashMap[List[Int]]): mutable.ArrayBuffer[mutable.ArrayBuffer[Int]] = {
    // TODO: create iterative variant

    val s = mutable.Buffer.empty[Int]

    val sSet = mutable.Set.empty[Int]

    val index = new java.util.HashMap[Int, Int]()

    val lowLink = new java.util.HashMap[Int, Int]()

    val ret = mutable.ArrayBuffer.empty[mutable.ArrayBuffer[Int]]

    def visit(v: Int): Unit = {

      index.put(v, index.size)

      lowLink.put(v, index.get(v))

      s += v

      sSet += v

      for(w <- g.get(v)) {

        if(!index.keySet.contains(w)) {

          visit(w)

          lowLink.put(v, math.min(lowLink.get(w), lowLink.get(v)))

        } else if(sSet(w))
          lowLink.put(v, math.min(lowLink.get(v), index.get(w)))
      }

      if(lowLink.get(v) == index.get(v)) {

        val scc = mutable.ArrayBuffer.empty[Int]

        var w = -1

        while(v != w) {

          w = s.remove(s.size - 1)

          scc += w

          sSet -= w

        }

        ret += scc

      }
    }

    val gKeys = g.keys()

    gKeys.forEach(v => {

      if (v.value >= 0 && !index.keySet.contains(v))
        visit(v.value)

    })

    ret

  }

}
