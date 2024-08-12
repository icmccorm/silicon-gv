// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.Stack
import viper.silicon.state.CheckPosition
import viper.silicon.state.terms._
import viper.silicon.utils.Counter
import viper.silver.ast
import viper.silver.ast.Exp
import viper.silicon.state.terms.{And, Decl, Implies, Quantification, Quantifier, Term, Trigger, True, Var, sorts}
import viper.silicon.utils
/*
 * Interfaces
 */

/* TODO: 'contains' functionality currently not needed. If removed, 'allAssumptions' could
 *       probably removed as well.
 *       Benchmark runtime difference!
 */

trait RecordedPathConditions {
  def branchConditions: Stack[Term]
  def branchConditionExps: Stack[Option[ast.Exp]]
  def branchConditionsSemanticExps: Stack[Option[ast.Exp]]
  def branchConditionsOrigins: Stack[Option[CheckPosition]]

  def assumptions: InsertionOrderedSet[Term]
  def definingAssumptions: InsertionOrderedSet[Term]
  def declarations: InsertionOrderedSet[Decl]

  def definitionsOnly: RecordedPathConditions

  def contains(assumption: Term): Boolean

  def conditionalized: Seq[Term]

  def quantified(quantifier: Quantifier,
                 qvars: Seq[Var],
                 triggers: Seq[Trigger],
                 name: String,
                 isGlobal: Boolean,
                 ignore: Term /* TODO: Hack, implement properly */)
                : (Seq[Term], Seq[Quantification])

  // If the heap does not contain a mapping for a snapshot(?) value, the path
  // condition must...? maybe
  def getEquivalentVariables(variable: Term, lenient: Boolean = false): Seq[Term] = {
    assumptions.foldRight[Seq[Term]](Seq.empty)((term, equivalentVars) => term match {
      case Equals(var1@Var(_, _), term2) if term2 == variable =>
        var1 +: equivalentVars
      case Equals(term1, var2@Var(_, _)) if term1 == variable =>
        var2 +: equivalentVars
      case Equals(var1@Var(_, _), term2) if lenient && term2.toString == variable.toString && term2.sort == variable.sort =>
        var1 +: equivalentVars
      case Equals(term1, var2@Var(_, _)) if lenient && term1.toString == variable.toString && term1.sort == variable.sort =>
        var2 +: equivalentVars
      case Equals(term1, term2) if lenient && term1.sort == sorts.Ref && term2.toString == variable.toString && term2.sort == variable.sort =>
        term1 +: equivalentVars
      case Equals(term1, term2) if lenient && term2.sort == sorts.Ref && term1.toString == variable.toString && term1.sort == variable.sort =>
        term2 +: equivalentVars
      case _ => equivalentVars
    })
  }
}

trait PathConditionStack extends RecordedPathConditions {
  def setCurrentBranchCondition(condition: Term, conditionExp: Option[ast.Exp], semanticExp: Option[ast.Exp], conditionOrigin: Option[CheckPosition]): Unit

  def add(assumption: Term): Unit
  def addDefinition(assumption: Term): Unit
  def add(declaration: Decl): Unit
  def pushScope(): Unit
  def popScope(): Unit
  def mark(): Mark
  def popUntilMark(mark: Mark): Unit
  def after(mark: Mark): RecordedPathConditions
  def isEmpty: Boolean
  def duplicate(): PathConditionStack
    /* Public method 'clone' impossible, see https://issues.scala-lang.org/browse/SI-6760 */
}

/*
 * Implementations (mostly mutable!)
 */

private class PathConditionStackLayer
    extends Cloneable {

  private var _branchCondition: Option[Term] = None
  private var _branchConditionExp: Option[ast.Exp] = None
  private var _branchConditionSemanticExp: Option[ast.Exp] = None
  private var _branchConditionOrigin: Option[CheckPosition] = None
  private var _globalAssumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _nonGlobalAssumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _globalDefiningAssumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _nonGlobalDefiningAssumptions: InsertionOrderedSet[Term] = InsertionOrderedSet.empty
  private var _declarations: InsertionOrderedSet[Decl] = InsertionOrderedSet.empty

  def branchCondition: Option[Term] = _branchCondition
  def branchConditionExp: Option[ast.Exp] = _branchConditionExp
  def branchConditionSemanticExp: Option[ast.Exp] = _branchConditionSemanticExp
  def branchConditionOrigin: Option[CheckPosition] = _branchConditionOrigin
  def globalAssumptions: InsertionOrderedSet[Term] = _globalAssumptions
  def globalDefiningAssumptions: InsertionOrderedSet[Term] = _globalDefiningAssumptions
  def nonGlobalDefiningAssumptions: InsertionOrderedSet[Term] = _nonGlobalDefiningAssumptions
  def nonGlobalAssumptions: InsertionOrderedSet[Term] = _nonGlobalAssumptions
  def declarations: InsertionOrderedSet[Decl] = _declarations

  def assumptions: InsertionOrderedSet[Term] = globalAssumptions ++ nonGlobalAssumptions
  def pathConditions: InsertionOrderedSet[Term] = assumptions ++ branchCondition

  def definitionsOnly(): PathConditionStackLayer = {
    val result = new PathConditionStackLayer
    result._globalAssumptions = _globalDefiningAssumptions
    result._globalDefiningAssumptions = _globalDefiningAssumptions
    result._nonGlobalAssumptions = _nonGlobalDefiningAssumptions
    result._nonGlobalDefiningAssumptions = _nonGlobalDefiningAssumptions
    result._declarations = _declarations
    result
  }

  def branchCondition_=(condition: Term): Unit = {
    assert(_branchCondition.isEmpty,
             s"Branch condition is already set (to ${_branchCondition.get}), "
           + s"won't override (with $condition).")

    _branchCondition = Some(condition)
  }

  def branchConditionExp_=(condition: Option[ast.Exp]): Unit = {
    assert(_branchConditionExp.isEmpty,
      s"Branch condition is already set (to ${_branchConditionExp.get}), "
        + s"won't override (with $condition).")

    _branchConditionExp = condition
  }
  def branchConditionSemanticExp_=(conditionSemanticAstNode: Option[Exp]) {

    assert(_branchConditionSemanticExp.isEmpty,
      s"Branch condition position is already set (to ${_branchConditionSemanticExp.get}), "
    + s"refusing to override (with $conditionSemanticAstNode).")

    _branchConditionSemanticExp = conditionSemanticAstNode
  }

  def branchConditionOrigin_=(conditionOrigin: Option[CheckPosition]) {

    assert(_branchConditionOrigin.isEmpty,
      s"Branch condition origin is already set (to ${_branchConditionOrigin.get}), "
    + s"refusing to override (with $conditionOrigin).")

    _branchConditionOrigin = conditionOrigin
  }

  def add(assumption: Term): Unit = {
    assert(
      !assumption.isInstanceOf[And],
      s"Unexpectedly found a conjunction (should have been split): $assumption")

    /* TODO: Don't record branch conditions as assumptions */

    if (PathConditions.isGlobal(assumption))
      _globalAssumptions += assumption
    else
      _nonGlobalAssumptions += assumption
  }

  def addDefinition(assumption: Term): Unit = {
    assert(
      !assumption.isInstanceOf[And],
      s"Unexpectedly found a conjunction (should have been split): $assumption")

    if (PathConditions.isGlobal(assumption)) {
      _globalAssumptions += assumption
      _globalDefiningAssumptions += assumption
    } else {
      _nonGlobalAssumptions += assumption
      _nonGlobalDefiningAssumptions += assumption
    }
  }

  def add(declaration: Decl): Unit = _declarations += declaration

  def contains(pathCondition: Term): Boolean = {
    assert(
      !pathCondition.isInstanceOf[And],
      s"Unexpectedly found a conjunction (should have been split): $pathCondition")

    if (PathConditions.isGlobal(pathCondition))
      /* Assumption: globals are never used as branch conditions */
      _globalAssumptions.contains(pathCondition)
    else
      _nonGlobalAssumptions.contains(pathCondition) || _branchCondition.contains(pathCondition)
  }

  override def clone(): AnyRef = {
    /* Attention: the original and its clone must not share any mutable data! */
    super.clone()
  }
}

private trait LayeredPathConditionStackLike {
  protected def branchConditions(layers: Stack[PathConditionStackLayer]): Stack[Term] =
    layers.flatMap(_.branchCondition)

  protected def branchConditionExps(layers: Stack[PathConditionStackLayer]): Stack[Option[ast.Exp]] =
    layers.map(_.branchConditionExp)

  protected def branchConditionsSemanticExps(layers:
    Stack[PathConditionStackLayer]): Stack[Option[Exp]] =
      layers.map(_.branchConditionSemanticExp)

  protected def branchConditionsOrigins(layers: Stack[PathConditionStackLayer]): Stack[Option[CheckPosition]] =
    layers.map(_.branchConditionOrigin)

  protected def assumptions(layers: Stack[PathConditionStackLayer]): InsertionOrderedSet[Term] =
    InsertionOrderedSet(layers.flatMap(_.assumptions)) // Note: Performance?

  protected def definingAssumptions(layers: Stack[PathConditionStackLayer]): InsertionOrderedSet[Term] =
    InsertionOrderedSet(layers.flatMap(_.globalDefiningAssumptions) ++ layers.flatMap(_.nonGlobalDefiningAssumptions)) // Note: Performance?

  protected def declarations(layers: Stack[PathConditionStackLayer]): InsertionOrderedSet[Decl] =
    InsertionOrderedSet(layers.flatMap(_.declarations)) // Note: Performance?

  protected def contains(layers: Stack[PathConditionStackLayer], assumption: Term): Boolean =
    layers exists (_.contains(assumption))

  protected def conditionalized(layers: Stack[PathConditionStackLayer]): Seq[Term] = {
    var unconditionalTerms = Vector.empty[Term]
    var conditionalTerms = Vector.empty[Term]
    var implicationLHS: Term = True

    for (layer <- layers.reverseIterator) {
      unconditionalTerms ++= layer.globalAssumptions

      layer.branchCondition match {
        case Some(condition) =>
          implicationLHS = And(implicationLHS, condition)
        case None =>
      }

      conditionalTerms :+=
        Implies(implicationLHS, And(layer.nonGlobalAssumptions))
    }

    unconditionalTerms ++ conditionalTerms
  }

  protected def quantified(layers: Stack[PathConditionStackLayer],
                           quantifier: Quantifier,
                           qvars: Seq[Var],
                           triggers: Seq[Trigger],
                           name: String,
                           isGlobal: Boolean,
                           ignore: Term)
                          : (Seq[Term], Seq[Quantification]) = {

    var globals = Vector.empty[Term]
    var nonGlobals = Vector.empty[Quantification]

    val ignores = ignore.topLevelConjuncts

    for (layer <- layers) {
      val actualBranchCondition = layer.branchCondition.getOrElse(True)
      val relevantNonGlobals = layer.nonGlobalAssumptions -- ignores
      val (trueNonGlobals, additionalGlobals) = if (!actualBranchCondition.existsDefined{ case t if qvars.contains(t) => }) {
        // The branch condition is independent of all quantified variables
        // Any assumptions that are also independent of all quantified variables can be treated as global assumptions.
        val (trueNonGlobals, unconditionalGlobals) = relevantNonGlobals.partition(a => a.existsDefined{ case t if qvars.contains(t) => })
        (trueNonGlobals, unconditionalGlobals.map(Implies(actualBranchCondition, _)))
      } else {
        (relevantNonGlobals, Seq())
      }

      globals ++= layer.globalAssumptions ++ additionalGlobals

      nonGlobals :+=
        Quantification(
          quantifier,
          qvars,
          Implies(actualBranchCondition, And(trueNonGlobals)),
          triggers,
          name,
          isGlobal)
    }

    (globals, nonGlobals)
  }
}

private class DefaultRecordedPathConditions(from: Stack[PathConditionStackLayer])
    extends LayeredPathConditionStackLike
       with RecordedPathConditions {

  val branchConditions: Stack[Term] = branchConditions(from)
  val branchConditionExps: Stack[Option[ast.Exp]] = branchConditionExps(from)
  val branchConditionsSemanticExps: Stack[Option[Exp]] = branchConditionsSemanticExps(from)
  val branchConditionsOrigins: Stack[Option[CheckPosition]] = branchConditionsOrigins(from)
  val assumptions: InsertionOrderedSet[Term] = assumptions(from)
  val definingAssumptions: InsertionOrderedSet[Term] = definingAssumptions(from)
  val declarations: InsertionOrderedSet[Decl] = declarations(from)

  def contains(assumption: Term): Boolean = contains(from, assumption)

  val conditionalized: Seq[Term] = conditionalized(from)

  def definitionsOnly(): RecordedPathConditions = {
    new DefaultRecordedPathConditions(from.map(_.definitionsOnly))
  }

  def quantified(quantifier: Quantifier,
                 qvars: Seq[Var],
                 triggers: Seq[Trigger],
                 name: String,
                 isGlobal: Boolean,
                 ignore: Term)
                : (Seq[Term], Seq[Quantification]) = {

    quantified(from, quantifier, qvars, triggers, name, isGlobal, ignore)
  }
}

private[decider] class LayeredPathConditionStack
    extends LayeredPathConditionStackLike
       with PathConditionStack
       with Cloneable {

  /* private */ var layers: Stack[PathConditionStackLayer] = Stack.empty
  private var markToLength: Map[Mark, Int] = Map.empty
  private var scopeMarks: List[Mark] = List.empty
  private var markCounter = new Counter(0)

  /* Set of assumptions across all layers. Maintained separately to improve performance. */
  private var allAssumptions = InsertionOrderedSet.empty[Term]

  pushScope() /* Create an initial layer on the stack */

  def setCurrentBranchCondition(condition: Term, conditionExp: Option[ast.Exp], semanticExp: Option[ast.Exp], conditionOrigin: Option[CheckPosition]): Unit = {
    /* TODO: Split condition into top-level conjuncts as well? */
    layers.head.branchCondition = condition
    layers.head.branchConditionExp = conditionExp
    layers.head.branchConditionSemanticExp = semanticExp
    layers.head.branchConditionOrigin = conditionOrigin
  }

  def add(assumption: Term): Unit = {
    /* TODO: Would be cleaner to not add assumptions that are already set as branch conditions */

    val tlcs = assumption.topLevelConjuncts

    tlcs foreach layers.head.add
    allAssumptions ++= tlcs
  }

  def addDefinition(assumption: Term): Unit = {
    /* TODO: Would be cleaner to not add assumptions that are already set as branch conditions */

    val tlcs = assumption.topLevelConjuncts

    tlcs foreach layers.head.addDefinition
    allAssumptions ++= tlcs
  }

  def add(declaration: Decl): Unit = {
    layers.head.add(declaration)
  }

  def pushScope(): Unit = {
    val scopeMark = pushLayer()
    scopeMarks = scopeMark :: scopeMarks
  }

  def popScope(): Unit = {
    val scopeMark = scopeMarks.head
    scopeMarks = scopeMarks.tail

    popLayersAndRemoveMark(scopeMark)
  }

  private def pushLayer(): Mark = {
    val mark = markCounter.next()

    markToLength += (mark -> layers.length)
    layers = new PathConditionStackLayer() +: layers

    mark
  }

  def popUntilMark(mark: Mark): Unit = {
    assert(markToLength.contains(mark), "Cannot pop unknown mark")
    popLayersAndRemoveMark(mark)
  }

  private def popLayersAndRemoveMark(mark: Mark): Unit = {
    val targetLength = markToLength(mark)
    val dropLength = layers.length - targetLength

    markToLength = markToLength - mark

//    /* Remove marks pointing to popped layers (including mark itself) */
//    markToLength = markToLength filter (_._2 < targetLength)
//      /* TODO: Performance? Do lazily, e.g. when isEmpty is called? */

    var i = 0
    layers =
      layers.dropWhile(layer => {
        i += 1
        allAssumptions --= layer.assumptions
        i < dropLength
        /* If i < dropLength is false, the current - and last-to-drop - layer won't be
         * dropped, but its assumptions have already been removed from allAssumptions.
         * Subsequently taking the tail of the remaining layers results in also
         * dropping the last layer that needs to be dropped.
         */
      }).tail
  }


  def branchConditions: Stack[Term] = layers.flatMap(_.branchCondition)

  override def branchConditionExps: Stack[Option[ast.Exp]] = layers.map(_.branchConditionExp)

  def branchConditionsSemanticExps: Stack[Option[Exp]] = layers.map(_.branchConditionSemanticExp)

  def branchConditionsOrigins: Stack[Option[CheckPosition]] = layers.map(_.branchConditionOrigin)

  def assumptions: InsertionOrderedSet[Term] = allAssumptions

  def declarations: InsertionOrderedSet[Decl] =
    InsertionOrderedSet(layers.flatMap(_.declarations)) // Note: Performance?

  def definingAssumptions: InsertionOrderedSet[Term] =
    InsertionOrderedSet(layers.flatMap(_.globalDefiningAssumptions) ++ layers.flatMap(_.nonGlobalDefiningAssumptions)) // Note: Performance?

  def contains(assumption: Term): Boolean = allAssumptions.contains(assumption)

  def conditionalized: Seq[Term] = conditionalized(layers)

  def quantified(quantifier: Quantifier,
                 qvars: Seq[Var],
                 triggers: Seq[Trigger],
                 name: String,
                 isGlobal: Boolean,
                 ignore: Term)
                : (Seq[Term], Seq[Quantification]) = {

    quantified(layers, quantifier, qvars, triggers, name, isGlobal, ignore)
  }

  def mark(): Mark = pushLayer()

  def after(mark: Mark): RecordedPathConditions = {
    val afterLength = layers.length - markToLength(mark)
    val afterLayers = layers.take(afterLength)

    new DefaultRecordedPathConditions(afterLayers)
  }

  def isEmpty: Boolean = (
       layers.forall(_.branchCondition.isEmpty)
    && allAssumptions.isEmpty
    && (markToLength.keySet -- scopeMarks).isEmpty)

  override def duplicate(): LayeredPathConditionStack = {
    /* Attention: The original and its clone must not share any mutable data! */

    val clonedStack = new LayeredPathConditionStack

    /* Sharing immutable data is safe */
    clonedStack.allAssumptions = allAssumptions
    clonedStack.markToLength = markToLength
    clonedStack.scopeMarks = scopeMarks

    /* Mutable data is cloned */
    clonedStack.markCounter = markCounter.clone()
    clonedStack.layers = layers map (_.clone().asInstanceOf[PathConditionStackLayer])

    clonedStack
  }

  override def definitionsOnly: RecordedPathConditions = {
    val result = duplicate()
    result.layers = layers map (_.definitionsOnly())
    result.allAssumptions = InsertionOrderedSet(layers.flatMap(_.globalDefiningAssumptions) ++
      layers.flatMap(_.nonGlobalDefiningAssumptions))
    result
  }

  override def toString: String =  {
    val sb = new StringBuilder(s"${this.getClass.getSimpleName}:\n")
    val sep = s" ${"-" * 10}\n"

    sb.append(sep)

    sb.append(s"  height: ${layers.length}\n")
    sb.append(s"  allAssumptions:\n")
    for (assumption <- allAssumptions) {
      sb.append(s"    $assumption\n")
    }

    sb.append(sep)

    for (layer <- layers) {
      sb.append(s"  branch condition: ${layer.branchCondition}\n")
      sb.append( "  assumptions:\n")
      for (assumption <- layer.assumptions) {
        sb.append(s"    $assumption\n")
      }
    }

    sb.append(sep)

    val marks = markToLength.keySet -- scopeMarks
    sb.append("  marks:\n")
    marks foreach (m => {
      sb.append(s"    $m -> ${markToLength(m)} (${scopeMarks.contains(m)})\n")
    })

    sb.result()
  }
}

private object PathConditions {
  def isGlobal(assumption: Term): Boolean = {
    assumption match {
      case quantification: Quantification => quantification.isGlobal
      case _: IsReadPermVar => true
      case _ => false
    }
  }
}
