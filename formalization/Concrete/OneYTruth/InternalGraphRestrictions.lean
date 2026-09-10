import OneYTruth.InternalUniformTower

/-! # Actual predecessor restrictions inside the adequate carrier

These are literal restrictions of the already constructed full graph,
obtained by a fixed bounded Separation predicate on its first component.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula CodedPaths

universe u

namespace RecursionEnvironment

variable {V : ZFSet.{u}} (E : RecursionEnvironment V)
include E

theorem restrictionGraph_mem {c d : ZFSet.{u}} {F : ZFSet.{u} → ZFSet.{u}}
    (hc : c ∈ V) (hg : predecessorRestrictionGraph d F ∈ V)
    (hsub : ∀ z ∈ c, z ∈ d) : predecessorRestrictionGraph c F ∈ V := by
  let φ : Delta0Formula 2 := pathMemAt [false] 1 0
  let cV : ZFCarrier V := ⟨c, hc⟩
  let gV : ZFCarrier V := ⟨predecessorRestrictionGraph d F, hg⟩
  obtain ⟨q, hq⟩ := E.separation 1 φ.toFO ![cV] gV
  have htest (p : ZFCarrier V) :
      FOFormula.Satisfies (zfCarrierMem V) φ.toFO (snoc ![cV] p) ↔
        ∃ z, Follows [false] p.val z ∧ z ∈ c := by
    rw [satisfies_toFO, satisfies_absolute E.transitive]
    exact satisfies_pathMemAt [false] 1 0 _
  have heq : q.val = predecessorRestrictionGraph c F := by
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      let pV : ZFCarrier V := ⟨p, E.transitive.mem_trans hp q.property⟩
      obtain ⟨hpg, hφ⟩ := (hq pV).mp hp
      obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hpg
      obtain ⟨w, hw, hwc⟩ := (htest pV).mp hφ
      have hwz : w = z := by
        rw [← he] at hw
        obtain ⟨a, ha, haw⟩ := hw
        have haz : a = z := component_pair.mp ha
        exact haw.symm.trans haz
      exact mem_predecessorRestrictionGraph_iff.mpr ⟨z, hwz ▸ hwc, he⟩
    · intro hp
      obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
      have hpg : p ∈ predecessorRestrictionGraph d F :=
        mem_predecessorRestrictionGraph_iff.mpr ⟨z, hsub z hz, he⟩
      let pV : ZFCarrier V := ⟨p, E.transitive.mem_trans hpg hg⟩
      apply (hq pV).mpr
      refine ⟨hpg, (htest pV).mpr ⟨z, ?_, hz⟩⟩
      change Follows [false] p z
      rw [← he]
      exact ⟨z, ⟨F z, rfl⟩, rfl⟩
  exact heq ▸ q.property

end RecursionEnvironment

theorem predecessorGraph_mem_of_adequate {κ β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β) {U : ZFSet.{u}}
    (hU : U ∈ LStageZF β) (s : Stage κ) :
    predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) (codedTruth κ U) ∈
      LStageZF β := by
  apply (recursionEnvironment_of_adequate hβ).restrictionGraph_mem
    (stagePredecessors_mem_of_adequate hβ hκβ s)
  · rw [← graph_eq_restrictionGraph]
    exact graph_mem_of_adequate hβ hκβ hU
  · intro z hz
    exact (stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz)

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.predecessorGraph_mem_of_adequate
