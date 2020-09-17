/**
  * delSAT
  *
  * Copyright (c) 2018,2020 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * Licensed under MIT License (see file LICENSE for details)
  *
  */

name := "delSAT"

version := "0.5.0"

scalaVersion := "2.13.2" // (probably still also works with 2.12 with minor modifications)

scalacOptions ++= Seq("-opt:l:method", "-opt:l:inline",
  "-opt-inline-from:solving.SingleSolverThreadData.**;sharedDefs.**;solving.Preparation.**;utils.**")

scalacOptions ++= Seq("-Xdisable-assertions")  // comment out this statement for development and debugging

mainClass in (Compile, run) := Some("userAPItests.delSAT")

mainClass in (Compile, packageBin) := Some("userAPItests.delSAT")

// NB: If the "fat jar" isn't built with sbt-assembly, remember to also update artifact modules/versions in IntelliJ
// with all of the following libs by letting "Artifacts" unpack(!) them into the .jar:

libraryDependencies += "org.scala-lang.modules" %% "scala-parallel-collections" % "0.2.0"

libraryDependencies += "com.accelad" % "nilgiri-math" % "1.16"

libraryDependencies += "org.scijava" % "parsington" % "1.0.4"

libraryDependencies += "it.unimi.dsi" % "fastutil" % "8.3.1"

libraryDependencies += "org.apache.commons" % "commons-math3" % "3.6.1"

// The following dependencies are not required for core functionality:

//libraryDependencies += "com.oracle.substratevm" % "svm" % "19.2.1" % Provided  // only required if you want
// to create a native image using GraalVM. Also see RuntimeReflectionRegistrationFeature.java and Target_scala_runtime_Statics.java

libraryDependencies += "com.jsoniter" % "jsoniter" % "0.9.23" // required for stats/persistent logging only

/*
resolvers += "cibo artifacts" at "https://dl.bintray.com/cibotech/public/"
libraryDependencies += "com.cibo" %% "evilplot" % "0.8.0" // required for stats/persistent logging only
*/







