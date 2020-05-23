// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silver.ast.PredicateAccess

trait PredicateSnapFunctionsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

class DefaultPredicateSnapFunctionsContributor(preambleReader: PreambleReader[String, String],
                                               symbolConverter: SymbolConverter,
                                               termConverter: TermConverter[String, String, String],
                                               predicateSnapGenerator: PredicateSnapGenerator,
                                               config: Config)
    extends PredicateSnapFunctionsContributor[Sort, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty
  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty // TODO: Make Set[sorts.PredicateSnapFunction]
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset() {
    collectedPredicates = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop() {}

  def start() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    program visit {
      case QuantifiedPermissionAssertion(_, _, acc: ast.PredicateAccessPredicate) =>
        val predicate = program.findPredicate(acc.loc.predicateName)
        collectedPredicates += predicate
      case ast.Forall(_, triggers, _) =>
        val trigExps = triggers flatMap (_.exps)
        val predicateAccesses = trigExps flatMap (e => e.deepCollect {case pa: PredicateAccess => pa})
        collectedPredicates ++= (predicateAccesses map (_.loc(program)))
    }

    // WARNING: DefaultSetsContributor contributes a sort that is due to QPs over predicates

    collectedSorts = (
        (collectedPredicates.map(predicate =>
          sorts.PredicateSnapFunction(predicateSnapGenerator.getSnap(predicate)._1)): InsertionOrderedSet[Sort])
            + sorts.PredicateSnapFunction(sorts.Snap)
        )

    collectedFunctionDecls = generateFunctionDecls
    collectedAxioms = generateAxioms
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generateFunctionDecls: Iterable[PreambleBlock] = {
    val snapsTemplateFile = "/predicate_snap_functions_declarations.smt2"

    collectedPredicates map (p => {
      val snapSort = predicateSnapGenerator.getSnap(p)._1
      val id = p.name
      val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(snapSort))
      val declarations = preambleReader.readParametricPreamble(snapsTemplateFile, substitutions)

      (s"$snapsTemplateFile [$id: $snapSort]", declarations)
    })
  }

  def generateAxioms: Iterable[PreambleBlock] = {
    val templateFile =
      if (config.disableISCTriggers()) "/predicate_snap_functions_axioms_no_triggers.smt2"
      else "/predicate_snap_functions_axioms.smt2"

    collectedPredicates map (p => {
      val sort = predicateSnapGenerator.getSnap(p)._1
      val id = p.name
      val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id: $sort]", declarations)
    })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
