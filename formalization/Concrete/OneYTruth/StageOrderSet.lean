import OneYTruth.StageRecursionDomain
import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph

/-! The entire actual lexicographic relation, as one constructible set of pairs. -/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

noncomputable def stageOrderSet (κ : Ordinal.{u}) : ZFSet.{u} :=
  (canonicalDefinableRelationGraph stageRelationFormula.toFO (stageParams κ)
    ⟨stageSet κ, stageSet_mem_L κ⟩).val

theorem stageOrderSet_mem_L (κ : Ordinal.{u}) : stageOrderSet κ ∈ L :=
  (canonicalDefinableRelationGraph stageRelationFormula.toFO (stageParams κ)
    ⟨stageSet κ, stageSet_mem_L κ⟩).property

theorem mem_stageOrderSet_iff (κ : Ordinal.{u}) (pair : ZFSet.{u}) :
    pair ∈ stageOrderSet κ ↔ ∃ s t : Stage κ,
      pair = ZFSet.pair (stageCode s) (stageCode t) ∧ Earlier s t := by
  constructor
  · intro hp
    let pL : LCarrier.{u} := ⟨pair, mem_L_of_mem hp (stageOrderSet_mem_L κ)⟩
    obtain ⟨x, y, _, _, he, hφ⟩ :=
      (mem_canonicalDefinableRelationGraph_iff stageRelationFormula.toFO
        (stageParams κ) ⟨stageSet κ, stageSet_mem_L κ⟩ pL).mp hp
    have hrel : CodedEarlier κ x.val y.val :=
      (satisfies_stageRelationFormula κ x y).mp hφ
    obtain ⟨s, t, hs, ht, hst⟩ := hrel
    exact ⟨s, t, by rw [hs, ht]; exact he, hst⟩
  · rintro ⟨s, t, rfl, hst⟩
    let sL : LCarrier.{u} := ⟨stageCode s, stageCode_mem_L s⟩
    let tL : LCarrier.{u} := ⟨stageCode t, stageCode_mem_L t⟩
    let pL := orderedPairLCarrier sL tL
    apply (mem_canonicalDefinableRelationGraph_iff stageRelationFormula.toFO
      (stageParams κ) ⟨stageSet κ, stageSet_mem_L κ⟩ pL).mpr
    exact ⟨sL, tL, stageCode_mem_stageSet s, stageCode_mem_stageSet t, rfl,
      (satisfies_stageRelationFormula κ sL tL).mpr ⟨s, t, rfl, rfl, hst⟩⟩

theorem pair_mem_stageOrderSet_iff (κ : Ordinal.{u}) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ stageOrderSet κ ↔ CodedEarlier κ a b := by
  rw [mem_stageOrderSet_iff]
  constructor
  · rintro ⟨s, t, he, hst⟩
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp he
    exact ⟨s, t, ha.symm, hb.symm, hst⟩
  · rintro ⟨s, t, rfl, rfl, hst⟩
    exact ⟨s, t, rfl, hst⟩

theorem stageOrderSet_wellFounded (κ : Ordinal.{u}) :
    WellFounded (fun a b : ZFSet.{u} => ZFSet.pair a b ∈ stageOrderSet κ) := by
  have he : (fun a b : ZFSet.{u} => ZFSet.pair a b ∈ stageOrderSet κ) =
      CodedEarlier κ := by
    funext a b
    exact propext (pair_mem_stageOrderSet_iff κ a b)
  rw [he]
  exact codedEarlier_wellFounded κ

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.stageOrderSet_mem_L
#print axioms OneYTruth.ExternalTower.stageOrderSet_wellFounded
