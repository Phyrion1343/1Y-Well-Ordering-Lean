import OneYTruth.StageRecursionL

/-! # Supplying stage syntax to a one-step formula

The source-domain and predecessor formulas are fixed actual formulas.
An arbitrary one-step formula only needs its own ordinary parameters; this
constructor prepends the stage-set parameter and proves every reindexing.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

theorem snoc_prepend {α : Type u} {n : Nat} (a : α) (v : Tuple α n) (x : α) :
    snoc (Fin.cases a v) x = Fin.cases a (snoc v x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change snoc (Fin.cases a v) x (Fin.castSucc (0 : Fin (n + 1))) = a
    rw [snoc_castSucc]
    rfl
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.cases_succ, Fin.succ_last, snoc_last, snoc_last]
    · rw [Fin.cases_succ, Fin.succ_castSucc, snoc_castSucc, Fin.cases_succ, snoc_castSucc]

/-- Build the entire stage-recursion presentation from a whole-step formula
and its exact semantics. All class/relation syntax is supplied here. -/
noncomputable def stageStepPresentationOfFormula (κ : Ordinal.{u})
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) {n : Nat}
    (params : Tuple LCarrier.{u} n) (φ : FOFormula (n + 3))
    (hφ : ∀ x q v : LCarrier.{u}, x.val ∈ stageSet κ →
      (FOFormula.Satisfies lCarrierMem φ (snoc (snoc (snoc params x) q) v) ↔
        v.val = op x.val q.val))
    (hclosed : ∀ x q : LCarrier.{u}, x.val ∈ stageSet κ → op x.val q.val ∈ L) :
    StageStepPresentation κ op where
  arity := n + 1
  params := Fin.cases ⟨stageSet κ, stageSet_mem_L κ⟩ params
  classFormula := classFormulaAt stageClassFormula.toFO (fun _ => 0) (Fin.last (n + 1))
  relationFormula := relationFormulaAt stageRelationFormula.toFO (fun _ => 0)
    (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
  stepFormula := φ.rename Fin.succ
  class_exact := by
    intro z
    rw [satisfies_classFormulaAt_generic]
    have he : (fun _ : Fin 1 => snoc
        (Fin.cases ⟨stageSet κ, stageSet_mem_L κ⟩ params) z 0) = stageParams κ := by
      funext i
      fin_cases i
      rw [snoc_prepend]
      rfl
    simpa only [he, snoc_last] using satisfies_stageClassFormula κ z
  relation_exact := by
    intro y z
    rw [satisfies_relationFormulaAt_generic]
    have he : (fun _ : Fin 1 => snoc (snoc
        (Fin.cases ⟨stageSet κ, stageSet_mem_L κ⟩ params) y) z 0) = stageParams κ := by
      funext i
      fin_cases i
      rw [snoc_prepend, snoc_prepend]
      rfl
    have h := satisfies_stageRelationFormula κ y z
    change FOFormula.Satisfies lCarrierMem stageRelationFormula.toFO
      (snoc (snoc (stageParams κ) y) z) ↔ CodedEarlier κ y.val z.val at h
    simpa only [he, snoc_castSucc, snoc_last] using h
  step_exact := by
    intro x q v hx
    rw [FOFormula.satisfies_rename]
    rw [snoc_prepend, snoc_prepend, snoc_prepend]
    simp only [Fin.cases_succ]
    exact hφ x q v hx
  step_mem_L := hclosed

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.stageStepPresentationOfFormula
