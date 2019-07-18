/**
  * delSAT
  *
  * Copyright (c) 2018, 2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * Licensed under MIT License (see file LICENSE for details)
  *
  */

name := "delSAT"

version := "0.4.1"

scalaVersion := "2.12.8"

scalacOptions ++= Seq("-Xdisable-assertions")  // remove line for debugging

mainClass in (Compile, run) := Some("commandlineDelSAT.delSAT")

mainClass in (Compile, packageBin) := Some("commandlineDelSAT.delSAT") 

libraryDependencies += "com.accelad" % "nilgiri-math" % "1.16"

libraryDependencies += "org.scijava" % "parsington" % "1.0.4"

libraryDependencies += "it.unimi.dsi" % "fastutil" % "8.2.2"


