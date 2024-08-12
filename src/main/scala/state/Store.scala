// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silicon.{Map, toMap}
import viper.silicon.state.terms.{Term, sorts}
import viper.silver.ast.AbstractLocalVar

trait Store {
  def values: Map[ast.AbstractLocalVar, Term]
  def apply(key: ast.AbstractLocalVar): Term
  def get(key: ast.AbstractLocalVar): Option[Term]
  def getKeyForValue(termVariable: terms.Term, lenient: Boolean = false): Option[ast.AbstractLocalVar]
  def +(kv: (ast.AbstractLocalVar, Term)): Store
  def +(other: Store): Store
}

trait StoreFactory[ST <: Store] {
  def apply(): ST
  def apply(bindings: Map[ast.AbstractLocalVar, Term]): ST
  def apply(pair: (ast.AbstractLocalVar, Term)): ST
  def apply(pairs: Iterable[(ast.AbstractLocalVar, Term)]): ST
}

object Store extends StoreFactory[MapBackedStore] {
  def apply() = new MapBackedStore(Map.empty)
  def apply(pair: (AbstractLocalVar, Term)) = new MapBackedStore(Map(pair))
  def apply(bindings: Map[AbstractLocalVar, Term]) = new MapBackedStore(toMap(bindings))
  def apply(bindings: Iterable[(AbstractLocalVar, Term)]) = new MapBackedStore(toMap(bindings))
}

final class MapBackedStore private[state] (map: Map[ast.AbstractLocalVar, Term])
  extends Store {

  val values = map
  def apply(key: ast.AbstractLocalVar): Term = map(key)
  def get(key: ast.AbstractLocalVar): Option[Term] = map.get(key)
  def getKeyForValue(symbolicVariable: terms.Term, lenient: Boolean = false): Option[ast.AbstractLocalVar] = {
    def compare(t: Term): Boolean = {
      if (lenient) {
      symbolicVariable.toString == t.toString && symbolicVariable.sort == t.sort
    } else {
      symbolicVariable == t
    }
    }
    val lookupResult = symbolicVariable match {
      case _ @ terms.Var(_, _) =>
        map.find({
          case (_, var2 @ terms.Var(_, _)) => compare(var2)
          case (_, term2) if term2.sort == sorts.Ref => compare(term2)
          case _ => false
        })
      case _ => map.find({
        case (_, var2) => {
          symbolicVariable == var2
        }
        case _ => false
      })
    }
    lookupResult.map(kv => kv._1)
  }
  def +(entry: (ast.AbstractLocalVar, Term)) = new MapBackedStore(map + entry)
  def +(other: Store) = new MapBackedStore(map ++ other.values)
}
