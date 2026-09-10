import OneYTruth.ActualExpansion
import OneY.Dynamics

/-! Consequences for the user's actual expansion and standard generated order,
conditional on the single unfinished finite-reflection obligation. -/

namespace OneYTruth.RootSemantics

open Constructible OneY.RootIndexed OneY.Numeric YesMetaZFC.BMS.StabilityFrame

universe u

theorem actual_descendants_strictWellOrder
    (reflection : FiniteReflection (α := Ordinal.{u}) (· < ·) Adequate R) (s : ZeroY.Expr) :
    StrictWellOrder (Descendant s) DescendantLt :=
  descendants_strictWellOrder (actual_expansion_wellFounded reflection) s

theorem actual_generated_strictWellOrder
    (reflection : FiniteReflection (α := Ordinal.{u}) (· < ·) Adequate R) :
    StrictWellOrder GeneratedExpr GeneratedLt :=
  generated_strictWellOrder (actual_expansion_wellFounded reflection)

theorem actual_expansion_chain_reaches_empty
    (reflection : FiniteReflection (α := Ordinal.{u}) (· < ·) Adequate R)
    (chain : Nat → ZeroY.Expr) (hNext : ∀ n, ∃ N, chain (n + 1) = expand (chain n) N) :
    ∃ n, (chain n).values = [] :=
  expansion_chain_reaches_empty (actual_expansion_wellFounded reflection) chain hNext

end OneYTruth.RootSemantics

#print axioms OneYTruth.RootSemantics.actual_generated_strictWellOrder
#print axioms OneYTruth.RootSemantics.actual_expansion_chain_reaches_empty
