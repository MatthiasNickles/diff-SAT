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

import java.io.{BufferedOutputStream, File, FileOutputStream, OutputStream}
import java.time.Instant
import java.util
import java.util.UUID

import com.jsoniter.output.JsonStream

import input.diffSAT
import input.diffSAT.stats

import sharedDefs._
import utils.Various._


// For visualization of the serialized runtime statistics events, use Satalyzer (separate project)

final case class StatsEntry( // Any modification of this class (e.g., new fields or field names) need to be reflected in the
                             // deserialization method further below (can't be don't automatically).
                             // Also, of course, class StatsEntry needs to be identical with StatsEntry in project RuntimeStats/StatsVisualizer.

                             messageTimeStamp: Long = -1l, // in nano secs from program start (not to be used as a unique entry or message key)

                             threadNo: Int = 0,

                             key: String = null,

                             valueStr: String = null,

                             @transient runIDTransient: String = null

                           ) {

}

final case class Stats( // Any modification of this class (e.g., new fields or field names) need to be reflected in the
                        // deserialization method further below (can't be don't automatically).
                        // Also, of course, class Stats needs to be identical with Stats in project RuntimeStats/StatsVisualizer.

                        problemFile: String,

                        runID: String = UUID.randomUUID().toString, // a type-4 UUID represented as a string

                        runStartTimeMs: Long = Instant.now.toEpochMilli(),

                        // any other information, including solving duration, should be written as StatsEntry entries

                        entries: util.List[StatsEntry] /*doesn't serialize properly: ArrayBuffer[StatsEntry]*/ =
                        new util.ArrayList[StatsEntry](),

                        @transient var outFile: File = null,

                        @transient var statsFileStream: OutputStream = null,

                        @transient var lastFlush: Long = 0l

                      ) {

  def initializeStatsFile(): Unit = {

    val outFileName = "stats_" + toString.replaceAll("[^\\w.-]", "_") + "(UTC).json"

    val dir = new File(writeStatsDirectory)

    outFile = new File(dir, outFileName)

  }

  @inline def initializeStatsFileStream(): Unit = {

    assert(outFile != null)

    statsFileStream = new BufferedOutputStream(
      new FileOutputStream(outFile))

  }

  /** This writes the entire stats to file, replacing any existing file with the respective name */
  @inline def writeToFile(): Unit = {

    if (writeRuntimeStatsToFile) { // for performance reasons, this condition should ideally be checked already
      // before calling this method

      initializeStatsFileStream()

      try {

        JsonStream.serialize(stats, statsFileStream) // closes stream!

      } catch { // TODO: probable reason: Graal 20 native image not working with Jsoniter

        case e: Exception => diffSAT.stomp(-10000, "Cannot serialize runtime stats: " + e + "\nIf you are using a native image executable, it is recommended to try writeRuntimeStatsToFile() with a JVM instead")

      }

    }

  }

  /** Don't use this for frequent writing such as logging. For long period statistics gathering only.
    */
  @inline def writeEntry(key: String, value: scala.Any,
                         solverThreadNo: Int = 0 /*0: outside SAT solver thread*/ ,
                         replace: Boolean = false): Unit = {

    if (writeRuntimeStatsToFile) { // for performance reasons, this condition should ideally be checked already
      // before calling writeEntry

      val messageTimeStampRelativeToProgStartNs = (Instant.now.toEpochMilli() - runStartTimeMs) * 1000000l // TODO

      val valueStr = value.toString()

      val newStatsEntry = new StatsEntry(messageTimeStamp = messageTimeStampRelativeToProgStartNs,
        threadNo = solverThreadNo, key = key, valueStr = valueStr,
        runIDTransient = runID)

      //println(statsEntry)

      this.synchronized {

        assert(newStatsEntry != null)

        if (replace) { // (costly, but rarely used and for deserialization-related reasons we shouldn't use a map here anyway)

          var i = stats.entries.size() - 1

          while (i >= 0) {

            val existingEntry = stats.entries.get(i)

            if (existingEntry.key == key) {

              stats.entries.set(i, newStatsEntry)

              i = -2

            } else
              i -= 1

          }

          if (i == -2)
            writeToFile() // since otherwise any existing serialization would be "outdated" (containing the old value of the unique key)
          else
            entries.add(newStatsEntry)

        } else
          entries.add(newStatsEntry)

        val currentTimerNs = System.nanoTime()

        if (currentTimerNs - lastFlush > flushRuntimeStatsEverySec /*sec*/ * 1000000000l) {

          lastFlush = currentTimerNs

          writeToFile()

        }

      }

    }

  }

  def getFirstOpt(key: String): Option[StatsEntry] = {

    var i = 0

    while (i < entries.size()) {

      val existingEntry = entries.get(i)

      if (existingEntry.key == key)
        return Some(existingEntry)

      i += 1

    }

    None

  }

  def countEntriesWithKey(key: String, maxCount: Int = Int.MaxValue): Int = {

    var count = 0

    var i = 0

    while (i < entries.size()) {

      if (entries.get(i).key == key) {

        count += 1

        if (count >= maxCount)
          return count

      }

      i += 1

    }

    count

  }

  override def toString(): String = {

    val runStartTimeMsStr = Instant.ofEpochMilli(runStartTimeMs).toString

    val problemName = fileNameFromFullPath(problemFile)

    problemName + " [" + runStartTimeMsStr + "]"

  }

}

