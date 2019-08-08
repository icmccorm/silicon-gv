// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.Verifier
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.reporter.NoopReporter

class SiliconTests extends SilSuite {
  private val siliconTestDirectories = Seq("consistency", "issue387", "symbExLogTests")
  private val silTestDirectories = Seq("all", "quantifiedpermissions", "wands", "examples", "quantifiedpredicates" ,"quantifiedcombinations")
  val testDirectories = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    val fe = new SiliconFrontend(NoopReporter)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation) = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) => issue != 34
      case _ => false
    }
  }

  lazy val verifiers = List(createSiliconInstance())

  val commandLineArguments: Seq[String] = Seq.empty

  private def createSiliconInstance() = {
    val configMap = prefixSpecificConfigMap.getOrElse("silicon", Map())
    var args =
      commandLineArguments ++
      Silicon.optionsFromScalaTestConfigMap(configMap)
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }
}
