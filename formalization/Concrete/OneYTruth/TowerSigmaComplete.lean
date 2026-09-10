import OneYTruth.TowerEntryWitnesses
import OneYTruth.TowerSigmaSoundness
import OneYTruth.UniformWitnessBound

/-! Completeness of the genuine whole-tower Sigma-one formula. Collection
provides one common internal bound for all local records of the actual graph. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula Constructible.Model
open ExternalTower GraphStepMatrix CodedPaths InternalClosure

universe u v

theorem query_complete {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u})
    (p : Fin 14 → ZFCarrier (LStageZF β))
    (hp : ∀ i : Fin 13, (p i.castSucc).val = (fixedParameters κ U i).val)
    (hg : (p 13).val = @graph κ U.val) :
    OneYTruth.realize N (query K J) Empty.elim p := by
  let V := LStageZF β
  have hV : V.IsTransitive := LStageZF_isTransitive β
  let E := recursionEnvironment_of_adequate hβ
  have hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V :=
    fun _ ha _ hb => E.orderedPair_mem ha hb
  have hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V := fun _ ha => E.sUnion_mem ha
  have hf (i : Fin 13) : (fixedParameters κ U i).val ∈ V := hp i ▸ (p i.castSucc).property
  have hU : U.val ∈ V := hf 0
  have hempty : (∅ : ZFSet.{u}) ∈ V := hf 6
  have hlocal (x : ZFCarrier V) (hx : x.val ∈ (p 13).val) :
      ∃ w : Fin 24 → ZFCarrier V, Satisfies ZFMem entryMatrix
        (Fin.append (fun i => ((Fin.snoc p x : Fin 15 → ZFCarrier V) i).val)
          (fun i => (w i).val)) := by
    apply entry_witnesses hβ hκβ N hmem hCol hSep U hU (Fin.snoc p x)
    · intro i
      change ((Fin.snoc p x : Fin 15 → ZFCarrier V) i.castSucc.castSucc).val = _
      rw [Fin.snoc_castSucc]
      exact hp i
    · exact hg
    · exact hg ▸ hx
  obtain ⟨B,hB⟩ := UniformWitnessBound.exists_uniform_bound hV N hmem hCol
    hpair hUnion hempty 24 entryMatrix p (p 13) hlocal
  let D : ZFCarrier V := ⟨stageSet κ,stageSet_mem_LStage hβ.2.1 hβ.1 hκβ⟩
  let C : ZFCarrier V := ⟨(Order.succ κ).toZFSet,
    ordinal_toZFSet_mem_LStageZF_of_lt (hβ.2.1.succ_lt hκβ)⟩
  apply (realize_query hV N hmem p).mpr
  refine ⟨D,C,B,?_,?_,?_,?_⟩
  · change (Order.succ κ).toZFSet = insert (p 1).val (p 1).val
    rw [show (p 1).val = κ.toZFSet from hp 1,Ordinal.toZFSet_succ]
  · change stageSet κ = InternalProducts.pairProduct (p 5).val (Order.succ κ).toZFSet
    rw [show (p 5).val = Ordinal.omega0.toZFSet from hp 5,stageSet_eq_product]
  · change ((∀ x ∈ stageSet κ, ∃ e ∈ (p 13).val, Component false e x) ∧
      (∀ e ∈ (p 13).val, ∃ x ∈ stageSet κ, Component false e x))
    rw [hg]
    constructor
    · intro x hx
      obtain ⟨s,rfl⟩ := ZFSet.mem_range.mp hx
      exact ⟨ZFSet.pair (stageCode s) (truth U.val s),
        ZFSet.mem_range_self (f := fun t : Stage κ => ZFSet.pair (stageCode t) (truth U.val t)) s,
        truth U.val s,rfl⟩
    · intro e he
      obtain ⟨s,rfl⟩ := ZFSet.mem_range.mp he
      exact ⟨stageCode s,stageCode_mem_stageSet s,truth U.val s,rfl⟩
  · intro e he
    let eV : ZFCarrier V := ⟨e,hV.mem_trans he (p 13).property⟩
    have hc := hB eV he
    rw [← entryCertificate] at hc
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem,val_snoc,val_snoc] at hc
    exact hc

theorem realize_query_iff {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u})
    (p : Fin 14 → ZFCarrier (LStageZF β))
    (hp : ∀ i : Fin 13, (p i.castSucc).val = (fixedParameters κ U i).val) :
    OneYTruth.realize N (query K J) Empty.elim p ↔ (p 13).val = @graph κ U.val := by
  constructor
  · exact query_sound (LStageZF_isTransitive β)
      (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)) N hmem κ U p hp
  · exact query_complete hβ hκβ N hmem hCol hSep U p hp

end OneYTruth.TowerSigma
