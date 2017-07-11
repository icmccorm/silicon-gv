/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.resources

sealed abstract class PropertyExpression

sealed abstract class EquatableExpression extends PropertyExpression
sealed abstract class BooleanExpression extends EquatableExpression
sealed abstract class IdentifierExpression extends EquatableExpression
sealed abstract class ArgumentExpression extends EquatableExpression
sealed abstract class PermissionExpression extends EquatableExpression
sealed abstract class ValueExpression extends EquatableExpression

case class Check(condition: BooleanExpression, thenDo: BooleanExpression, otherwise: BooleanExpression) extends BooleanExpression

/**
  * Foreach c1, c2 iterates over all <b>distinct</b> pairs of chunks.
  * @param chunkVariables a non-empty sequence of chunk variables without duplicates
  * @param body an expression
  */
case class ForEach(chunkVariables: Seq[ChunkVariable], body: BooleanExpression) extends BooleanExpression {
  require(chunkVariables.nonEmpty, "Cannot quantify over no variable.")
  require(chunkVariables.distinct.size == chunkVariables.size, "Cannot quantify over non-distinct variables.")
}

case class PermissionIfThenElse(condition: BooleanExpression, thenDo: PermissionExpression, otherwise: PermissionExpression) extends PermissionExpression
case class ValueIfThenElse(condition: ValueExpression, thenDo: ValueExpression, otherwise: ValueExpression) extends ValueExpression

case class Equals(left: EquatableExpression, right: EquatableExpression) extends BooleanExpression {
  require(left.isInstanceOf[BooleanExpression] == right.isInstanceOf[BooleanExpression])
  require(left.isInstanceOf[IdentifierExpression] == right.isInstanceOf[IdentifierExpression])
  require(left.isInstanceOf[ArgumentExpression] == right.isInstanceOf[ArgumentExpression])
  require(left.isInstanceOf[PermissionExpression] == right.isInstanceOf[PermissionExpression])
  require(left.isInstanceOf[ValueExpression] == right.isInstanceOf[ValueExpression])
}
case class NotEquals(left: EquatableExpression, right: EquatableExpression) extends BooleanExpression {
  require(left.isInstanceOf[BooleanExpression] == right.isInstanceOf[BooleanExpression])
  require(left.isInstanceOf[IdentifierExpression] == right.isInstanceOf[IdentifierExpression])
  require(left.isInstanceOf[ArgumentExpression] == right.isInstanceOf[ArgumentExpression])
  require(left.isInstanceOf[PermissionExpression] == right.isInstanceOf[PermissionExpression])
  require(left.isInstanceOf[ValueExpression] == right.isInstanceOf[ValueExpression])
}

case class GreaterThan(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class GreaterThanEquals(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class LessThan(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression
case class LessThanEquals(left: PermissionExpression, right: PermissionExpression) extends BooleanExpression

case class Not(argument: BooleanExpression) extends BooleanExpression
case class And(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression
case class Or(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression
case class Implies(left: BooleanExpression, right: BooleanExpression) extends BooleanExpression

case class Plus(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Minus(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Times(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression
case class Div(left: PermissionExpression, right: PermissionExpression) extends PermissionExpression

sealed abstract class BooleanLiteral extends BooleanExpression
case class True() extends BooleanLiteral
case class False() extends BooleanLiteral

case class PermissionLiteral(numerator: BigInt, denominator: BigInt) extends PermissionExpression

sealed abstract class ChunkPlaceholder(name: String) extends PropertyExpression

/**
  * A placeholder for a chunk.
  * @param name a string starting with a lowercase <i>c</i>
  */
case class ChunkVariable(name: String) extends ChunkPlaceholder(name) {
  require(name.startsWith("c"))
}
case class This() extends ChunkPlaceholder(name = "this")

case class IdentifierAccess(chunk: ChunkPlaceholder) extends IdentifierExpression
case class ArgumentAccess(chunk: ChunkPlaceholder) extends ArgumentExpression
case class PermissionAccess(chunk: ChunkPlaceholder) extends PermissionExpression
case class ValueAccess(chunk: ChunkPlaceholder) extends ValueExpression

case class Null() extends ArgumentExpression
