package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.state.terms
import viper.silicon.state.State
import viper.silicon.decider.RecordedPathConditions

// should we use the path conditions from the state?
final class Translator(s: State, pcs: RecordedPathConditions) {
  
  // this is, to some extent, a stub method currently
  def translate(t: terms.Term): ast.Exp = {
    t match {
      case terms.Null() => ast.NullLit()()
      case terms.False() => ast.FalseLit()()
      case terms.True() => ast.TrueLit()()
      case terms.IntLiteral(i) => ast.IntLit(i)()
      case terms.Plus(t0, t1) => ast.Add(translate(t0), translate(t1))()
      case terms.Minus(t0, t1) => ast.Sub(translate(t0), translate(t1))()
      case terms.Div(t0, t1) => ast.Div(translate(t0), translate(t1))()
      case terms.Times(t0, t1) => ast.Mul(translate(t0), translate(t1))()
      case terms.Mod(t0, t1) => ast.Mod(translate(t0), translate(t1))()
      case terms.Not(t) => ast.Not(translate(t))()
      // exhaustiveness warnings are suppressed by the following four cases; do
      // these employ match guards via the seq matching?
      case terms.Or(ts) =>
        ts match {
          case t +: Seq() => ast.Or(translate(t), ast.FalseLit()())()
          case t +: vs => ast.Or(translate(t), translate(terms.Or(vs)))()
        }
      case terms.And(ts) =>
        ts match {
          case t +: Seq() => ast.And(translate(t), ast.TrueLit()())()
          case t +: vs => ast.And(translate(t), translate(terms.And(vs)))()
        }
      case terms.Implies(t0, t1) => ast.Implies(translate(t0), translate(t1))()
      case terms.Iff(t0, t1) => ast.And(ast.Implies(translate(t1), translate(t0))(),
        ast.Implies(translate(t0), translate(t1))())()
      case terms.Equals(t0, t1) => ast.EqCmp(translate(t0), translate(t1))()
      case terms.Less(t0, t1) => ast.LtCmp(translate(t0), translate(t1))()
      case terms.AtMost(t0, t1) => ast.LeCmp(translate(t0), translate(t1))()
      case terms.AtLeast(t0, t1) => ast.GeCmp(translate(t0), translate(t1))()
      case terms.Greater(t0, t1) => ast.GtCmp(translate(t0), translate(t1))()
      case terms.Ite(t0, t1, t2) => ast.CondExp(translate(t0), translate(t1), translate(t2))()
      case terms.Var(name, sort) =>
        sort match {
          case terms.sorts.Snap => ast.LocalVar("snapvar", ast.Int)()
          // TODO: sanitize variable names to safe numbers, if we have time
          case _ => variableResolver(terms.Var(name, sort))
        }
      // how do we deal with snapshots? we need not {
      // snapshots only exist in the path condition because the latter is
      // already passed around everywhere; translated snapshot terms should
      // never be returned from diff as part of a necessary runtime check, so
      // we need not translate them
      case terms.Unit => ast.NullLit()()
      case terms.First(t) => translate(t)
      case terms.Second(t) => translate(t)
      case terms.Combine(t0, t1) => ast.And(translate(t0), translate(t1))()
      // }
      // case 
    }
  }

  private def variableResolver(variable: terms.Var): ast.Exp = {
    // TODO: this is not as efficient as it might be; we search both heaps when
    // this may not be necessary
    //
    // a successful variable lookup in one heap obviates the need for a
    // variable lookup in the other
    
    val varType = variable match {
      case terms.Var(_, terms.sorts.Int) => ast.Int
      case terms.Var(_, terms.sorts.Bool) => ast.Bool
      case terms.Var(_, terms.sorts.Ref) => ast.Ref
      case terms.Var(_, terms.sorts.Perm) => ast.Perm
    }

    val heapOrStoreVar: terms.Var = pcs.getEquivalentVariable(variable) match {
      case None => variable
      case Some(equivalentVariable) => equivalentVariable
    }

    (s.h.getChunkForValue(heapOrStoreVar), s.optimisticHeap.getChunkForValue(heapOrStoreVar)) match {
      case (Some((symVar, id)), None) =>
        ast.FieldAccess(s.g.getKeyForValue(symVar), ast.Field(id, varType)())()
      case (None, Some((symVar, id))) =>
        ast.FieldAccess(s.g.getKeyForValue(symVar), ast.Field(id, varType)())()
      case (None, None) => s.g.getKeyForValue(heapOrStoreVar)
    }
  }
}