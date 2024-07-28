package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silicon.logger.records.data.WellformednessCheckRecord
import scala.collection.mutable.ListBuffer

trait WellFormednessRules extends SymbolicExecutionRules {
  def wellformed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: Seq[ast.Exp],
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult
  
  def isEquiImp(s: State, as: Seq[ast.Exp])
               : Boolean

  def isIsoImp(as: Seq[ast.Exp])
              : Boolean
}

object wellFormedness extends WellFormednessRules {
  import producer._
  private var visitedPreds: Seq[String] = Seq() // assumes pred names unique; silver + C0's typecheckers/parsers ensure this

  def wellformed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: Seq[ast.Exp],
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult = {
    val id = v.symbExLog.openScope(new WellformednessCheckRecord(e, s, v.decider.pcs))
    produce(s, sf, viper.silicon.utils.ast.BigAnd(e), pve, v)((s1, v1) =>
      produce(s, sf, viper.silicon.utils.ast.BigAnd(e), pve, v1)((s2, v2) => {
        v.symbExLog.closeScope(id)
        Q(s2, v2)
      })
    )
  }

  /** @inheritdoc */
  def isEquiImp(s: State, as: Seq[ast.Exp])
               : Boolean = {

    val allTlcs = ListBuffer[ast.Exp]()
    
    as.foreach(a => {
      val tlcs = a.topLevelConjuncts
      allTlcs ++= tlcs
    })

    isEquiImpTlcs(s, allTlcs.result())
  
  }

  private def isEquiImpTlcs(s: State, tlcs: Seq[ast.Exp])
                          : Boolean = {
    if (tlcs.isEmpty)
      false 
    else {
      tlcs.foldLeft(false) { (b, a) => 
        b || isEquiImpTlc(s, a)
      }
    }
  }

  private def isEquiImpR(s: State, a: ast.Exp)
                        : Boolean = {
    val tlcs = a.topLevelConjuncts
    
    isEquiImpTlcs(s, tlcs)
  }

  private def isEquiImpTlc(s: State, a: ast.Exp) 
                         : Boolean = {
    a match {
      case _ @ ast.ImpreciseExp(_) => true
      
      case _ @ ast.CondExp(_, a1, a2) => isEquiImpR(s, a1) || isEquiImpR(s, a2)

      case ast.PredicateAccessPredicate(ast.PredicateAccess(_, predicateName), _) =>
        if (visitedPreds.contains(predicateName))
          false
        else {
          visitedPreds = visitedPreds :+ predicateName
          val predicate = s.program.findPredicate(predicateName)
          var res = false
          res = isEquiImpR(s, predicate.body.get)     
          visitedPreds = visitedPreds.filter(p => p != predicateName)
          res
        }
      case _ => false
    }
  }

  /** @inheritdoc */
  def isIsoImp(as: Seq[ast.Exp])
              : Boolean = {
    
    val allTlcs = ListBuffer[ast.Exp]()
    as.foreach(a => {
      val tlcs = a.topLevelConjuncts
      allTlcs ++= tlcs
    })

    isIsoImpTlcs(allTlcs.result())
  }

  private def isIsoImpTlcs(tlcs: Seq[ast.Exp])
                          : Boolean = {
    if (tlcs.isEmpty)
      false 
    else {
      tlcs.foldLeft(false) { (b, a) => 
        b || isIsoImpTlc(a)
      }
    }
  }

  // This function assumes conditionals will never contain ? in their paths
  // This is a fair assumption because ? && (x > 2) ? ... : ... can give the same
  // affect as if ? was inside the conditional
  private def isIsoImpTlc(a: ast.Exp) 
                         : Boolean = {
    a match {
      case _ @ ast.ImpreciseExp(_) => true
      case _ => false
    }
  }
}