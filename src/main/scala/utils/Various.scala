/**
  * diff-SAT
  *
  * Copyright (c) 2018, 2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package utils

import input.diffSAT
import input.diffSAT.changeConsoleWidthUnderWin
import sharedDefs.RandomGenSuperclass

import scala.collection.mutable

object Various {

  /** Plain Fisher-Yates shuffle on init of array */
  @inline def shuffleArray[A](array: mutable.Seq[A], rg: RandomGenSuperclass, to: Int = -1): Unit = {

    if (to < 0 && array.length >= 16384)
      shuffleArrayBlocked[A](array, rg)
    else {

      val l = if (to < 0) array.length - 1 else to

      var i = l

      while (i > 0) {

        val j = rg.nextInt(i + 1)

        val temp = array(j)

        array(j) = array(i)

        array(i) = temp

        i -= 1

      }

    }

  }

  /** Fisher-Yates-Durstenfeld shuffle */
  @inline def shuffleArrayUnsafe(array: IntArrayUnsafeS, rg: RandomGenSuperclass, from /*inclusive*/ : Long = 0l, to /*inclusive*/ : Long = -1l): Unit = {

    val l = if (to < 0l) array.sizev - 1 else to

    var i: Long = l

    while (i > from) {

      val j = rg.nextInt(i.toInt + 1)

      val temp = array.get(j)

      array.update(j, array.get(i))

      array.update(i, temp)

      i -= 1

    }

  }

  /** Fisher-Yates-Durstenfeld shuffle */
  @inline def shuffleLongArrayUnsafe(array: LongArrayUnsafeS, rg: RandomGenSuperclass, from /*inclusive*/ : Long = 0l, to /*inclusive*/ : Long = -1l): Unit = {

    val l = if (to < 0l) array.sizev - 1 else to

    var i: Long = l

    while (i > from) {

      val j = rg.nextInt(i.toInt + 1)

      val temp = array.get(j)

      array.update(j, array.get(i))

      array.update(i, temp)

      i -= 1

    }

  }

  /** Blocked Fisher-Yates shuffle */
  @inline def shuffleArrayBlocked[A](arr: mutable.Seq[A], rg: RandomGenSuperclass): Unit = {
    // (method code based on public domain code from https://github.com/lemire/Code-used-on-Daniel-Lemire-s-blog)

    def swap(i: Int, j: Int) = {

      val tmp = arr(i)

      arr(i) = arr(j)

      arr(j) = tmp

    }

    val size = arr.length

    val block = 1024

    val buffer = Array.ofDim[Int](block)

    var i = size

    while (i > block + 1) {

      var k = 0

      while (k < block) {

        buffer(k) = rg.nextInt(i - k)

        k += 1

      }

      k = 0

      while (k < block) {

        swap(i - 1 - k, buffer(k))

        k += 1

      }

      i -= block

    }

    while (i > 1) {

      swap(i - 1, rg.nextInt(i))

      i -= 1

    }

  }

  @inline def round(n: Double, digits: Int): Double = {

    val p = Math.pow(10d, digits)

    Math.round(n * p) / p

  }


  @inline def powFloat(a: Float, b: Float): Float = {

    Math.pow(a, b).toFloat //org.apache.commons.math3.util.FastMath.pow(a, b).toFloat

  }

  @inline def powInt(a: Double, b: Int): Double = org.apache.commons.math3.util.FastMath.pow(a, b)

  @inline def printStatusLine(pStrR: String, cutOffAt: Int = 0) = {

    val pStr = if(sharedDefs.debug) pStrR else pStrR.take(sharedDefs.maxAssumedConsoleWidth.max(cutOffAt))+(" " * (sharedDefs.maxAssumedConsoleWidth.max(cutOffAt) - pStrR.length).max(0))  // progress line scrolls if larger than console width. No reliable way to determine console width in Java

    if(diffSAT.osWin && changeConsoleWidthUnderWin) {  // for older versions of Windows (pre Win 10 built xxxx?)

      // System.out.write(pStr.getBytes()) // if more than 4 lines, IntelliJ console flickers

      // \r moves to start of current console row (not supported with all OS)

      System.out.print(("\b" * 1100) + "\r" + pStr + "            ")
      // with Win, \b's seem to required in addition to '\r'. But still doesn't work if console line buffer width to small.

      // print("\u001b[s" + pStr + "\u001b[u")  // nope in Win

    } else {

     // System.out.print("\u001b[1A\u001b[2K")

      System.out.write(("\r" + pStr).getBytes())

    }

    System.out.flush()

  }

  @inline def timerToElapsedMs(startNano: Long): Long = (System.nanoTime() - startNano) / 1000000

  @inline def next2Pow(x: Int): Int = if (x <= 1) 1 else 1 << (32 - Integer.numberOfLeadingZeros(x - 1))

  /** Divisor must be a power of 2 */
  @inline def fastModByPow2(dividend: Int, divisor: Int): Int = dividend & (divisor - 1)

  @inline def binLog(x: Int): Int = {

    //assert(x != 0)

    31 - Integer.numberOfLeadingZeros(x)

  }


  def fileNameFromFullPath(fileStr: String): String = {

    java.nio.file.Paths.get(fileStr).getFileName().toString()

  }

  /**
    * Pretty prints a Scala value similar to its source represention.
    * Particularly useful for case classes.
    * Derived from code at https://gist.github.com/carymrobbins/7b8ed52cd6ea186dbdf8
    * with enhancements: @see https://gist.github.com/myDisconnect/1f7046b23e18b4b43dd3c5932d0db7dc
    *
    * @param a               - The value to pretty print.
    * @param indentSize      - Number of spaces for each indent.
    * @param maxElementWidth - Largest element size before wrapping.
    * @param depth           - Initial depth to pretty print indents.
    * @return
    */
  def prettyPrint(a: Any, indentSize: Int = 3, maxElementWidth: Int = 30, depth: Int = 0, omit: List[String]): String = {

    val indent = " " * depth * indentSize

    val fieldIndent = indent + (" " * indentSize)

    val nextDepth = prettyPrint(_: Any, indentSize, maxElementWidth, depth + 1, omit = omit)

    a match {

      case s: String =>
        val replaceMap = Seq(
          "\n" -> "\\n",
          "\r" -> "\\r",
          "\t" -> "\\t",
          "\"" -> "\\\""
        )
        '"' + replaceMap.foldLeft(s) { case (acc, (c, r)) => acc.replace(c, r) } + '"'

      case opt: Some[_] =>
        val resultOneLine = s"Some(${nextDepth(opt.get)})"
        if (resultOneLine.length <= maxElementWidth) return resultOneLine
        s"Some(\n$fieldIndent${nextDepth(opt.get)}\n$indent)"

      case xs: Seq[_] if xs.isEmpty =>
        xs.toString()

      case map: Map[_, _] if map.isEmpty =>
        map.toString()

      case xs: Map[_, _] =>
        val result = xs.map { case (key, value) => s"\n$fieldIndent${nextDepth(key)} -> ${nextDepth(value)}" }.toString
        "Map" + s"${result.substring(0, result.length - 1)}\n$indent)".substring(4)

      // Make Strings look similar to their literal form.
      // For an empty Seq just use its normal String representation.
      case xs: Seq[_] =>
        // If the Seq is not too long, pretty print on one line.
        val resultOneLine = xs.map(nextDepth).toString()
        if (resultOneLine.length <= maxElementWidth) return resultOneLine
        // Otherwise, build it with newlines and proper field indents.
        val result = xs.map(x => s"\n$fieldIndent${nextDepth(x)}").toString()
        result.substring(0, result.length - 1) + "\n" + indent + ")"

      // Product should cover case classes.
      case p: Product =>
        val prefix = p.productPrefix
        // We'll use reflection to get the constructor arg names and values.
        val cls = p.getClass
        val fields = cls.getDeclaredFields.filterNot(_.isSynthetic).map(_.getName)
        val values = p.productIterator.toSeq
        // If we weren't able to match up fields/values, fall back to toString.
        if (fields.length != values.length) return p.toString
        fields.zip(values).toList match {
          // If there are no fields, just use the normal String representation.
          case Nil => p.toString
          // If there is more than one field, build up the field names and values.
          case kvps =>
            val prettyFields = kvps.map {

              case (k, v) => {

                if (omit.contains(k))
                  s"$fieldIndent$k = (omitted)"
                else
                  s"$k = ${nextDepth(v)}"

              }


            }
            // If the result is not too long, pretty print on one line.
            val resultOneLine = s"$prefix(${prettyFields.mkString(", ")})"
            if (resultOneLine.length <= maxElementWidth) return resultOneLine
            // Otherwise, build it with newlines and proper field indents.
            s"$prefix(\n${
              kvps.map {

                // case ("dependencyGraph", _) => fieldIndent + "dependencyGraph = (omitted)"

                case (k, v) => {

                  if (omit.contains(k))
                    s"$fieldIndent$k = (omitted)"
                  else
                    s"$fieldIndent$k = ${nextDepth(v)}"


                }


              }.mkString(",\n")
            }\n$indent)"
        }

      // if we haven't specialized this type, just use its toString.
      case _ => a.toString

    }

  }

}
