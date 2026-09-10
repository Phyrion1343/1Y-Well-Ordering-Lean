import OneYTruth.ActualFiniteReflection
import OneYTruth.ActualDynamics

/-! # Well-ordering and termination for the actual 1-Y expansion

The canonical finite-reflection theorem is supplied as a proved theorem.
These exits have no representation, reflection, truth-set, reconstruction,
or well-foundedness hypotheses.
This Lean theorem status does not identify the weakest set-theoretic axioms.
-/
namespace OneYTruth.WellOrdering
open OneY.RootIndexed OneY.Numeric YesMetaZFC.BMS.StabilityFrame

/-- Every descending chain of actual nonempty 1-Y expansions terminates. -/
theorem expansion_wellFounded : WellFounded (ZeroY.ExpansionStep expand) :=
  RootSemantics.actual_expansion_wellFounded RootSemantics.actual_finiteReflection.{0}

/-- The standard generated 1-Y sequence order is a strict well-order. -/
theorem generated_strictWellOrder : StrictWellOrder GeneratedExpr GeneratedLt :=
  RootSemantics.actual_generated_strictWellOrder RootSemantics.actual_finiteReflection.{0}

/-- Every fixed starting sequence's generated descendant order is a strict well-order. -/
theorem descendants_strictWellOrder (s : ZeroY.Expr) :
    StrictWellOrder (Descendant s) DescendantLt :=
  RootSemantics.actual_descendants_strictWellOrder RootSemantics.actual_finiteReflection.{0} s

/-- Arbitrary choices of finite copy counts still reach the empty sequence. -/
theorem expansion_chain_reaches_empty (chain : Nat → ZeroY.Expr)
    (hNext : ∀ n, ∃ N, chain (n+1) = expand (chain n) N) :
    ∃ n, (chain n).values = [] :=
  RootSemantics.actual_expansion_chain_reaches_empty RootSemantics.actual_finiteReflection.{0} chain hNext

end OneYTruth.WellOrdering
#print axioms OneYTruth.WellOrdering.expansion_wellFounded
#print axioms OneYTruth.WellOrdering.generated_strictWellOrder
#print axioms OneYTruth.WellOrdering.descendants_strictWellOrder
#print axioms OneYTruth.WellOrdering.expansion_chain_reaches_empty

