import OneYTruth.InitialRepresentations
import OneYTruth.ActualTowerConstructible
import OneY.RootIndexed.ExpansionWellFounded

/-!
# Actual expansion with the concrete canonical ordinal semantics

The only remaining semantic hypothesis is finite reflection for the actual R.
Constructibility of the actual ambient truth set is proved and supplied.
Numerical reconstruction, initial labels, and ordinal descent are supplied
by proved theorems. This is a conditional theorem, not the final result.
-/

namespace OneYTruth.RootSemantics

open Constructible OneY.RootIndexed

universe u

theorem actual_expansion_wellFounded
    (reflection : FiniteReflection (α := Ordinal.{u}) (· < ·) Adequate R) :
    WellFounded (ZeroY.ExpansionStep OneY.Numeric.expand) := by
  apply OneY.RootIndexed.actual_expansion_wellFounded (α := Ordinal.{u})
    (· < ·) Adequate R Ordinal.lt_wf
    (fun h₁ h₂ => lt_trans h₁ h₂)
    (fun h => h.strict)
    (fun h hR => hR.weaken h.le) reflection
  intro s
  exact exists_initial_representation ambientTruth_mem_L (exprDiagram s)

end OneYTruth.RootSemantics

#print axioms OneYTruth.RootSemantics.actual_expansion_wellFounded
