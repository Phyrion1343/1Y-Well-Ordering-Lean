import OneYTruth.TowerSigmaSemantics
import OneYTruth.GraphInputConstructible

/-! Each bounded entry certificate forces its genuine graph-input truth value. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula Constructible.Model
open ExternalTower GraphStepMatrix

universe u v

theorem entryChecks_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (s : Stage κ) (P : Fin 39 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (P (Fin.castAdd 26 i)).val = (fixedParameters κ U i).val)
    (hs : (P 15).val = stageCode s) (h : EntryChecks (fun i => (P i).val)) :
    (P 16).val = graphInputStep κ U.val (stageCode s)
      (TowerRestriction.restrict (stageCode s) (P 13).val) := by
  let p : Fin 16 → ZFCarrier V := fun i => P (localMap (Fin.castAdd 21 i))
  let w : Fin 21 → ZFCarrier V := fun i => P (localMap (Fin.natAdd 16 i))
  have he : Fin.append p w = fun i => P (localMap i) := by
    exact @Fin.append_castAdd_natAdd 16 21 (ZFCarrier V) (fun i => P (localMap i))
  have hq : OneYTruth.realize N (GraphStepSigma.query K J) Empty.elim p := by
    apply (GraphStepSigma.realize_query_iff_matrix hV N hmem p).mpr
    refine ⟨w,?_⟩
    rw [he]
    exact h.2.2
  have hfixed : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val := by
    intro i
    fin_cases i <;> first | exact hp 0 | exact hp 1 | exact hp 2 | exact hp 3 | exact hp 4 | exact hp 5 | exact hp 6 | exact hp 7 | exact hp 8 | exact hp 9 | exact hp 10 | exact hp 11 | exact hp 12
  have hval := GraphStepSigma.query_sound hV hVL N hmem κ s.2.val s.2.property s.1 U p hfixed hs hq
  change (P 16).val = PredecessorGraph.step s.1 U.val FormulaCode.ordinalIndexCode
    κ.toZFSet (P 17).val at hval
  have hr : (P 17).val = TowerRestriction.restrict (P 15).val (P 13).val := h.2.1
  rw [hr,hs] at hval
  rw [graphInputStep_code_eq_predecessorStep]
  exact hval

theorem entryCertificate_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 15 → ZFCarrier V) (B : ZFCarrier V) (T : ZFSet.{u})
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 2 i)).val = (fixedParameters κ U i).val)
    (he : (p 14).val = ZFSet.pair (stageCode s) T)
    (hc : Satisfies ZFMem entryCertificate (snoc (fun i => (p i).val) B.val)) :
    T = graphInputStep κ U.val (stageCode s) (TowerRestriction.restrict (stageCode s) (p 13).val) := by
  obtain ⟨w,hw,hC⟩ := (satisfies_entryCertificate _ _).mp hc
  let wV : Fin 24 → ZFCarrier V := fun i => ⟨w i,hV.mem_trans (hw i) B.property⟩
  let P : Fin 39 → ZFCarrier V := Fin.append p wV
  have hraw : (fun i => (P i).val) = Fin.append (fun i => (p i).val) w := by
    funext i
    refine Fin.addCases (m := 15) (n := 24) (fun j => ?_) (fun j => ?_) i
    · simp only [P,Fin.append_left]
    · simp only [P,wV,Fin.append_right]
  rw [← hraw] at hC
  have hpair : (P 14).val = ZFSet.pair (P 15).val (P 16).val := hC.1
  have hcomponents := ZFSet.pair_inj.mp (hpair.symm.trans he)
  have hp' : ∀ i : Fin 13, (P (Fin.castAdd 26 i)).val = (fixedParameters κ U i).val := by
    intro i
    change (Fin.append p wV (Fin.castAdd 24 (Fin.castAdd 2 i))).val = _
    rw [Fin.append_left]
    exact hp i
  have hval := entryChecks_sound hV hVL N hmem κ U s P hp' hcomponents.1 hC
  rwa [hcomponents.2] at hval

end OneYTruth.TowerSigma
