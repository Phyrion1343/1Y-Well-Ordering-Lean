import OneYTruth.StageRecursionDomain
import OneYTruth.PureFOSchemas

/-! # The actual bounded stage domain inside an adequate smaller level

The index bound κ is strictly below β. No claim is made that the entire
Stage β source is itself an element of Lβ.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula
open Constructible.Godel InternalProducts InternalClosure RootSemantics
open ConstructibleBoundedIteration ConstructibleDiagramSources

universe u

theorem stageSet_mem_LStage {κ β : Ordinal.{u}} (hβ : Order.IsSuccLimit β)
    (hω : Ordinal.omega0 < β) (hκ : κ < β) : stageSet κ ∈ LStageZF β := by
  rw [stageSet_eq_product, pairProduct_eq_F2]
  exact op_mem_LStageZF_of_isSuccLimit hβ 2
    (ordinal_toZFSet_mem_LStageZF_of_lt hω)
    (ordinal_toZFSet_mem_LStageZF_of_lt (hβ.succ_lt hκ))

/-- The actual predecessor set is obtained from the displayed pure
Separation schema, using the already proved fixed Δ₀ predecessor test. -/
theorem stagePredecessors_mem_of_foSeparation {κ : Ordinal.{u}} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hSep : HasFOSeparation V)
    (hsource : stageSet κ ∈ V) (s : Stage κ) : stagePredecessors κ (stageCode s) ∈ V := by
  let sL : ZFCarrier V := ⟨stageCode s, hV.mem_trans (stageCode_mem_stageSet s) hsource⟩
  let sourceL : ZFCarrier V := ⟨stageSet κ, hsource⟩
  let φ : Delta0Formula 2 := earlierFormula.rename ![1, 0]
  obtain ⟨d, hd⟩ := hSep 1 φ.toFO ![sL] sourceL
  have htest (t : Stage κ) (tL : ZFCarrier V) (ht : tL.val = stageCode t) :
      FOFormula.Satisfies (zfCarrierMem V) φ.toFO (snoc ![sL] tL) ↔ Earlier t s := by
    rw [satisfies_toFO, satisfies_absolute hV]
    have he : val (snoc ![sL] tL) = ![stageCode s, stageCode t] := by
      funext i
      fin_cases i
      · rfl
      · exact ht
    rw [he]
    dsimp only [φ]
    rw [satisfies_rename]
    have ha : (fun i => ![stageCode s, stageCode t] (![1, 0] i)) =
        ![stageCode t, stageCode s] := by funext i; fin_cases i <;> rfl
    rw [ha]
    exact satisfies_earlierFormula t s
  have heq : d.val = stagePredecessors κ (stageCode s) := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : ZFCarrier V := ⟨z, hV.mem_trans hz d.property⟩
      obtain ⟨hzin, hzφ⟩ := (hd zL).mp hz
      obtain ⟨t, ht⟩ := ZFSet.mem_range.mp hzin
      apply mem_stagePredecessors.mpr
      exact ⟨t, s, ht, rfl, (htest t zL ht.symm).mp hzφ⟩
    · intro hz
      have hzsource := (stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz)
      let zL : ZFCarrier V := ⟨z, hV.mem_trans hzsource hsource⟩
      apply (hd zL).mpr
      refine ⟨hzsource, ?_⟩
      obtain ⟨t, ht⟩ := ZFSet.mem_range.mp hzsource
      apply (htest t zL ht.symm).mpr
      apply (codedEarlier_codes t s).mp
      rw [ht]
      exact mem_stagePredecessors.mp hz
  exact heq ▸ d.property

theorem stagePredecessors_mem_of_adequate {κ β : Ordinal.{u}}
    (hβ : Adequate β) (hκ : κ < β) (s : Stage κ) :
    stagePredecessors κ (stageCode s) ∈ LStageZF β :=
  stagePredecessors_mem_of_foSeparation (LStageZF_isTransitive β)
    hβ.pureFOSchemas.1 (stageSet_mem_LStage hβ.2.1 hβ.1 hκ) s

theorem stageLocalDomain_mem_of_adequate {κ β : Ordinal.{u}}
    (hβ : Adequate β) (hκ : κ < β) (s : Stage κ) :
    stageLocalDomain s ∈ LStageZF β := by
  apply union_mem_LStageZF_of_isSuccLimit hβ.2.1
  · apply singleton_mem_LStageZF_of_isSuccLimit hβ.2.1
    exact (LStageZF_isTransitive β).mem_trans (stageCode_mem_stageSet s)
      (stageSet_mem_LStage hβ.2.1 hβ.1 hκ)
  · exact stagePredecessors_mem_of_adequate hβ hκ s

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.stageLocalDomain_mem_of_adequate

