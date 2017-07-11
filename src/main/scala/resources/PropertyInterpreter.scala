/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

import viper.silicon.interfaces.state._
import viper.silicon.state.terms
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier

class PropertyInterpreter(heap: Iterable[Chunk], verifier: Verifier) {

  private type PlaceholderMap = Map[ChunkPlaceholder, ResourceChunk]
  private val resourceChunks: Iterable[ResourceChunk] = heap.flatMap {
    case c: ResourceChunk => Some(c)
    case _ => None
  }
  private var currentResourceID: Option[ResourceID] = None

  /**
    * Builds a term for the path conditions out of the expression. If <code>expression</code> contains a
    * <code>ForEach(...)</code> clause, it iterates over all chunks with the same ResourceID as <code>chunk</code>.
    * @param chunk the chunk used for the <code>This()</code> placeholder
    * @param expression an expression potentially containing <code>This()</code>
    * @return the corresponding term
    */
  def buildPathConditionForChunk(chunk: ResourceChunk, expression: BooleanExpression): terms.Term = {
    currentResourceID = Some(chunk.resourceID)
    val pc = buildPathCondition(expression, Map(This() -> chunk))
    currentResourceID = None
    pc
  }

  /**
    * Builds a term for the path conditions out of the expression. If <code>expression</code> contains a
    * <code>ForEach(...)</code> clause, it iterates over all chunks with ResourceID <code>resourceID</code>.
    * @param resourceID a resource ID
    * @param expression an expression <b>not</b> containing <code>This()</code>
    * @return the corresponding term
    */
  def buildPathConditionForResource(resourceID: ResourceID, expression: BooleanExpression): terms.Term = {
    currentResourceID = Some(resourceID)
    val pc = buildPathCondition(expression, Map.empty)
    currentResourceID = None
    pc
  }

  def buildPathConditionsForChunk(chunk: ResourceChunk, expressions: Iterable[BooleanExpression]): Iterable[terms.Term] = {
    expressions.map(buildPathConditionForChunk(chunk, _))
  }

  def buildPathConditionsForResource(resourceID: ResourceID, expressions: Iterable[BooleanExpression]): Iterable[terms.Term] = {
    expressions.map(buildPathConditionForResource(resourceID, _))
  }

  private def buildPathCondition(expression: PropertyExpression, placeholderMap: PlaceholderMap): Term = expression match {
      // Literals
    case True() => terms.True()
    case False() => terms.False()
    case PermissionLiteral(numerator, denominator) => buildPermissionLiteral(numerator, denominator)
    case Null() => terms.Null()

      // Boolean operators
    case Not(expr) => terms.Not(buildPathCondition(expr, placeholderMap))
    case And(left, right) => buildAnd(left, right, placeholderMap)
    case Or(left, right) => buildOr(left, right, placeholderMap)
    case Implies(left, right) => buildImplies(left, right, placeholderMap)

      // Universal operators
    case Equals(left, right) => buildEquals(left, right, placeholderMap)
    case NotEquals(left, right) => buildNotEquals(left, right, placeholderMap)

      // Permission operators
    case Plus(left, right) => buildBinary(terms.PermPlus, left, right, placeholderMap)
    case Minus(left, right) => buildBinary(terms.PermMinus, left, right, placeholderMap)
    case Times(left, right) => buildBinary(terms.PermTimes, left, right, placeholderMap)
    case Div(left, right) => buildBinary(terms.Div, left, right, placeholderMap)

    case GreaterThanEquals(left, right) => buildBinary(terms.PermAtMost, right, left, placeholderMap)
    case GreaterThan(left, right) => buildBinary(terms.PermLess, right, left, placeholderMap)
    case LessThanEquals(left, right) => buildBinary(terms.PermAtMost, left, right, placeholderMap)
    case LessThan(left, right) => buildBinary(terms.PermLess, left, right, placeholderMap)

      // Chunk accessors, only work for appropriate chunks
    case PermissionAccess(cv) => placeholderMap(cv) match {
      case b: DefaultChunk => b.perm
      case _ =>
        // TODO: this will be removed once magic wands have snapshots
        sys.error("Permission access of non-permission chunk")
    }
    case ValueAccess(cv) => placeholderMap(cv) match {
      case b: DefaultChunk => b.snap
      case _ =>
        // TODO: this will be remvoed once magic wands have snapshots
        sys.error("Value access of non-value chunk")
    }

      // decider / heap interaction
    case Check(condition, thenDo, otherwise) =>
      val conditionTerm = buildPathCondition(condition, placeholderMap)
      if (verifier.decider.check(conditionTerm, Verifier.config.checkTimeout())) {
        buildPathCondition(thenDo, placeholderMap)
      } else {
        buildPathCondition(otherwise, placeholderMap)
      }
    case ForEach(chunkVariables, body) => buildForEach(chunkVariables, body, placeholderMap)

      // If then else
    case PermissionIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise, placeholderMap)
    case ValueIfThenElse(condition, thenDo, otherwise) => buildIfThenElse(condition, thenDo, otherwise, placeholderMap)

      // The only missing cases are chunk expressions which only happen in accessors, and location expressions which
      // only happen in equality expressions and are treated separately
    case e => sys.error( s"An expression of type ${e.getClass} is not allowed here.")
  }

  // Assures short-circuit evalutation of 'and'
  private def buildAnd(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case leftTerm @ terms.False() => leftTerm
      case leftTerm @ _ => terms.And(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildOr(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case leftTerm @ terms.True() => leftTerm
      case leftTerm @ _ => terms.Or(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildImplies(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    buildPathCondition(left, pm) match {
      case terms.False() => terms.True()
      case leftTerm @ _ => terms.Implies(leftTerm, buildPathCondition(right, pm))
    }
  }

  private def buildEquals(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    (left, right) match {
      case (Null(), Null()) => terms.True()
      case (IdentifierAccess(cv1), IdentifierAccess(cv2)) =>
        if (pm(cv1).id == pm(cv2).id) terms.True() else terms.False()
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.args.size != chunk2.args.size) {
          // if arguments disagree, they can't be equal
          terms.False()
        } else if (chunk1.args == chunk2.args) {
          // if all arguments are the same, they are definitely equal
          terms.True()
        } else {
          // else return argument-wise equal
          terms.And(chunk1.args.zip(chunk2.args).map{ case (t1, t2) => terms.Equals(t1, t2) })
        }
      case (ArgumentAccess(cv), Null()) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case (Null(), ArgumentAccess(cv)) => terms.And(pm(cv).args.map(terms.Equals(_, terms.Null())))
      case _ =>
        val leftTerm = buildPathCondition(left, pm)
        val rightTerm = buildPathCondition(right, pm)
        if (leftTerm.sort == rightTerm.sort) {
          terms.Equals(leftTerm, rightTerm)
        } else {
          terms.False()
        }
    }
  }

  private def buildNotEquals(left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    (left, right) match {
      case (Null(), Null()) => terms.False()
      case (IdentifierAccess(cv1), IdentifierAccess(cv2)) =>
        if (pm(cv1).id != pm(cv2).id) terms.True() else terms.False()
      case (ArgumentAccess(cv1), ArgumentAccess(cv2)) =>
        val chunk1 = pm(cv1)
        val chunk2 = pm(cv2)
        if (chunk1.args.size != chunk2.args.size) {
          terms.True()
        } else {
          terms.Or(chunk1.args.zip(chunk2.args).map{ case (t1, t2) => t1 !== t2 })
        }
      case (ArgumentAccess(cv), Null()) => terms.And(pm(cv).args.map(terms.Null() !== _))
      case (Null(), ArgumentAccess(cv)) => terms.And(pm(cv).args.map(terms.Null() !== _))
      case _ =>
        val leftTerm = buildPathCondition(left, pm)
        val rightTerm = buildPathCondition(right, pm)
        if (leftTerm.sort == rightTerm.sort) {
          leftTerm !== rightTerm
        } else {
          terms.True()
        }
    }
  }

  private def buildPermissionLiteral(numerator: BigInt, denominator: BigInt): Term = {
    (numerator, denominator) match {
      case (n, d) if n == 0 && d != 0 => terms.NoPerm()
      case (n, d) if n == d && d != 0 => terms.FullPerm()
      case (n, d) => terms.FractionPerm(terms.IntLiteral(n), terms.IntLiteral(d))
    }
  }

  private def buildBinary(builder: (Term, Term) => Term, left: PropertyExpression, right: PropertyExpression, pm: PlaceholderMap) = {
    val leftTerm = buildPathCondition(left, pm)
    val rightTerm = buildPathCondition(right, pm)
    builder(leftTerm, rightTerm)
  }

  private def buildForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression, pm: PlaceholderMap) = {
    val (chunkVariable, nextExpression) = chunkVariables match {
      case c :: Nil => (c, body)
      case c :: tail => (c, ForEach(tail, body))
    }
    terms.And(resourceChunks.flatMap((chunk) => {
      // check that only chunks with the same resource type and only distinct tuples are handled
      if (chunk.resourceID == currentResourceID.get && !pm.values.exists(chunk == _)) {
        Some(buildPathCondition(nextExpression, pm + ((chunkVariable, chunk))))
      } else {
        None
      }
    }))
  }

  private def buildIfThenElse(condition: PropertyExpression, thenDo: PropertyExpression, otherwise: PropertyExpression, pm: PlaceholderMap) = {
    val conditionTerm = buildPathCondition(condition, pm)
    val thenDoTerm = buildPathCondition(thenDo, pm)
    val otherwiseTerm = buildPathCondition(otherwise, pm)
    terms.Ite(conditionTerm, thenDoTerm, otherwiseTerm)
  }

}
