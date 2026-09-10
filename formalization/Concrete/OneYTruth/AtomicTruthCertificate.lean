import OneYTruth.AtomicTruthCorrect
import OneYTruth.BoundedFilterGraph

/-! A literal bounded certificate for the complete true-atomic-node set. -/

namespace OneYTruth.AtomicTruthFormula

open Constructible Constructible.Delta0Formula SyntaxDiagram BoundedFilterGraph

universe u v

def certificate : Delta0Formula 13 := filterFormula formula

theorem trueAtomSet_eq_sep {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hmem : ∀ x y, M.mem x y ↔ x.val ∈ y.val) :
    trueAtomSet indexCode M =
      ZFSet.sep (fun x => Satisfies ZFMem formula (snoc (parameters indexCode M) x))
        (atomSet (k := k) U indexCode) := by
  apply filtered_range_eq_sep
    (fun z : AtomicAssignment (k := k) I U => nodeCode indexCode z.val)
    (fun z => OneYTruth.realize M z.val.1.2 Empty.elim z.val.2) formula (parameters indexCode M)
  intro z
  exact satisfies_formula_atomic hi M hmem z.val.1.2 z.val.2 z.property

theorem satisfies_certificate {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hmem : ∀ x y, M.mem x y ↔ x.val ∈ y.val) (T : ZFSet.{u}) :
    Satisfies ZFMem certificate
      (snoc (snoc (parameters indexCode M) (atomSet (k := k) U indexCode)) T) ↔
      T = trueAtomSet indexCode M := by
  rw [certificate, satisfies_filterFormula, ← trueAtomSet_eq_sep hi M hmem]

end OneYTruth.AtomicTruthFormula
