import OneYTruth.TowerEntrySoundness
import OneYTruth.TowerGraphUniqueness

/-! Soundness of the whole tower's genuine Sigma-one graph certificate.
Every source and local predecessor is checked; no schema is used. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula Constructible.Model
open ExternalTower GraphStepMatrix CodedPaths

universe u v

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (p : Fin 14 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p i.castSucc).val = (fixedParameters κ U i).val)
    (hq : OneYTruth.realize N (query K J) Empty.elim p) : (p 13).val = @graph κ U.val := by
  obtain ⟨D,C,B,hC,hD,hcovers,hentries⟩ := (realize_query hV N hmem p).mp hq
  have hκ : (p 1).val = κ.toZFSet := hp 1
  have hOmega : (p 5).val = Ordinal.omega0.toZFSet := hp 5
  have hsource : D.val = stageSet κ := by
    rw [hD,hC]
    change InternalProducts.pairProduct (p 5).val (insert (p 1).val (p 1).val) = _
    rw [hκ,hOmega,← Ordinal.toZFSet_succ,← stageSet_eq_product]
  have total (s : Stage κ) : ∃ T, ZFSet.pair (stageCode s) T ∈ (p 13).val := by
    obtain ⟨e,heg,he⟩ := hcovers.1 (stageCode s) (hsource.symm ▸ stageCode_mem_stageSet s)
    obtain ⟨T,hT⟩ := he
    exact ⟨T,hT ▸ heg⟩
  have junk (e : ZFSet.{u}) (he : e ∈ (p 13).val) :
      ∃ s : Stage κ, ∃ T, e = ZFSet.pair (stageCode s) T := by
    obtain ⟨x,hx,hcomp⟩ := hcovers.2 e he
    rw [hsource] at hx
    obtain ⟨s,hs⟩ := ZFSet.mem_range.mp hx
    obtain ⟨T,hT⟩ := hcomp
    exact ⟨s,T,by rw [hs]; exact hT⟩
  apply TowerRestriction.graph_eq_of_steps U.val (p 13).val total junk
  intro s T hT
  let e : ZFCarrier V := ⟨ZFSet.pair (stageCode s) T,hV.mem_trans hT (p 13).property⟩
  have hfix : ∀ i : Fin 13,
      ((Fin.snoc p e : Fin 15 → ZFCarrier V) (Fin.castAdd 2 i)).val = (fixedParameters κ U i).val := by
    intro i
    change ((Fin.snoc p e : Fin 15 → ZFCarrier V) i.castSucc.castSucc).val = _
    rw [Fin.snoc_castSucc]
    exact hp i
  have hval : val (Fin.snoc p e) = snoc (fun i => (p i).val) e.val := by
    exact val_snoc p e
  apply entryCertificate_sound hV hVL N hmem κ U s (Fin.snoc p e) B T hfix rfl
  rw [show (fun i => ((Fin.snoc p e : Fin 15 → ZFCarrier V) i).val) =
    snoc (fun i => (p i).val) e.val from hval]
  exact hentries e.val hT

end OneYTruth.TowerSigma
