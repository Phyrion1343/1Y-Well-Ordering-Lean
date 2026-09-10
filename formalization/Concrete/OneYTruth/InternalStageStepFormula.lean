import OneYTruth.InternalStageRecursion
import OneYTruth.StageStepFormula
import OneYTruth.GraphInputTower

/-! # Actual stage syntax and the internal truth-tower recursion bridge

The stage domain and order have fixed bounded definitions. Only the exact
internal whole-step formula and its one-step closure remain to be supplied.
Neither a recursive graph nor its membership is assumed.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula

universe u

noncomputable def internalStageParams {V : ZFSet.{u}} (κ : Ordinal.{u})
    (hsource : stageSet κ ∈ V) : Tuple (ZFCarrier V) 1 := ![⟨stageSet κ, hsource⟩]

theorem satisfies_stageClassFormula_carrier {V : ZFSet.{u}} (κ : Ordinal.{u})
    (hsource : stageSet κ ∈ V) (z : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V) stageClassFormula.toFO
      (snoc (internalStageParams κ hsource) z) ↔ z.val ∈ stageSet κ := Iff.rfl

theorem satisfies_stageRelationFormula_carrier {V : ZFSet.{u}} (hV : V.IsTransitive)
    (κ : Ordinal.{u}) (hsource : stageSet κ ∈ V) (y z : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V) stageRelationFormula.toFO
      (snoc (snoc (internalStageParams κ hsource) y) z) ↔ CodedEarlier κ y.val z.val := by
  rw [satisfies_toFO, satisfies_absolute hV]
  simp only [stageRelationFormula, Satisfies, satisfies_rename]
  change (y.val ∈ stageSet κ ∧ z.val ∈ stageSet κ ∧
    Satisfies ZFMem earlierFormula ![y.val, z.val]) ↔ CodedEarlier κ y.val z.val
  constructor
  · rintro ⟨hy, hz, h⟩
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hy
    obtain ⟨t, ht⟩ := ZFSet.mem_range.mp hz
    rw [← hs, ← ht] at h
    exact ⟨s, t, hs, ht, (satisfies_earlierFormula s t).mp h⟩
  · rintro ⟨s, t, hs, ht, h⟩
    rw [← hs, ← ht]
    exact ⟨stageCode_mem_stageSet s, stageCode_mem_stageSet t, (satisfies_earlierFormula s t).mpr h⟩

noncomputable def internalStagePresentationOfFormula {V : ZFSet.{u}}
    (E : RecursionEnvironment V) (κ : Ordinal.{u}) (hsource : stageSet κ ∈ V)
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) {n : Nat}
    (params : Tuple (ZFCarrier V) n) (φ : FOFormula (n + 3))
    (hφ : ∀ x q v : ZFCarrier V, x.val ∈ stageSet κ →
      (FOFormula.Satisfies (zfCarrierMem V) φ (snoc (snoc (snoc params x) q) v) ↔
        v.val = op x.val q.val))
    (hclosed : ∀ x q : ZFCarrier V, x.val ∈ stageSet κ → op x.val q.val ∈ V) :
    InternalStagePresentation V κ op where
  env := E
  source_mem := hsource
  arity := n + 1
  params := Fin.cases ⟨stageSet κ, hsource⟩ params
  classFormula := classFormulaAt stageClassFormula.toFO (fun _ => 0) (Fin.last (n + 1))
  relationFormula := relationFormulaAt stageRelationFormula.toFO (fun _ => 0)
    (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
  stepFormula := φ.rename Fin.succ
  class_exact := by
    intro z
    rw [satisfies_classFormulaAt_generic]
    have he : (fun _ : Fin 1 => snoc
        (Fin.cases ⟨stageSet κ, hsource⟩ params) z 0) = internalStageParams κ hsource := by
      funext i
      fin_cases i
      rw [snoc_prepend]
      rfl
    simpa only [he, snoc_last] using satisfies_stageClassFormula_carrier κ hsource z
  relation_exact := by
    intro y z
    rw [satisfies_relationFormulaAt_generic]
    have he : (fun _ : Fin 1 => snoc (snoc
        (Fin.cases ⟨stageSet κ, hsource⟩ params) y) z 0) = internalStageParams κ hsource := by
      funext i
      fin_cases i
      rw [snoc_prepend, snoc_prepend]
      rfl
    simpa only [he, snoc_castSucc, snoc_last] using
      satisfies_stageRelationFormula_carrier E.transitive κ hsource y z
  step_exact := by
    intro x q v hx
    rw [FOFormula.satisfies_rename]
    rw [snoc_prepend, snoc_prepend, snoc_prepend]
    simp only [Fin.cases_succ]
    exact hφ x q v hx
  step_mem := hclosed

/-- The actual externally defined truth tower lies in the smaller carrier,
provided its canonical whole-step formula is correct there and the step is
closed there. These are one-step hypotheses, not assumptions on the tower. -/
theorem graph_mem_of_internal_stepFormula {V : ZFSet.{u}} {κ : Ordinal.{u}}
    (E : RecursionEnvironment V) (hsource : stageSet κ ∈ V) (U : ZFSet.{u})
    {n : Nat} (params : Tuple (ZFCarrier V) n) (φ : FOFormula (n + 3))
    (hφ : ∀ x q v : ZFCarrier V, x.val ∈ stageSet κ →
      (FOFormula.Satisfies (zfCarrierMem V) φ (snoc (snoc (snoc params x) q) v) ↔
        v.val = graphInputStep κ U x.val q.val))
    (hclosed : ∀ x q : ZFCarrier V, x.val ∈ stageSet κ → graphInputStep κ U x.val q.val ∈ V) :
    @graph κ U ∈ V := by
  rw [graph_eq_restrictionGraph]
  exact (internalStagePresentationOfFormula E κ hsource (graphInputStep κ U)
    params φ hφ hclosed).stageGraph_mem (codedTruth κ U) (codedTruth_graphInputStep U)

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.graph_mem_of_internal_stepFormula
