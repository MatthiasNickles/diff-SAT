/**
  * delSAT
  *
  * Copyright (c) 2018, 2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/delSAT/blob/master/LICENSE
  *
  */

name := "DelSAT"

version := "0.3.1"

scalaVersion := "2.12.8"

scalacOptions ++= Seq("-Xdisable-assertions")  // remove line for debugging 

mainClass in (Compile, run) := Some("commandline.delSAT")

mainClass in (Compile, packageBin) := Some("commandline.delSAT") 

libraryDependencies += "com.accelad" % "nilgiri-math" % "1.16" 

libraryDependencies += "org.scijava" % "parsington" % "1.0.1"

libraryDependencies += "it.unimi.dsi" % "fastutil" % "8.2.2"
