import OneYTruth.TowerSigmaComplete
import OneYTruth.SigmaFiniteConjunction

/-! A genuine Sigma-one query for a single canonical truth set. It binds
and verifies the complete tower, then performs a bounded literal lookup. -/

namespace OneYTruth.TowerPoint

open Constructible Constructible.Delta0Formula Constructible.Model CodedPaths
open FirstOrder FirstOrder.Language ExternalTower GraphStepMatrix InternalClosure

universe u v w

/-- Graph, block code, height code, output. -/
def lookupFormula : Delta0Formula 4 :=
  .boundedEx 0 (.conj (pathEqAt [false,false] 4 1)
    (.conj (pathEqAt [false,true] 4 2) (pathEqAt [true] 4 3)))

theorem follows_entry_iff (e k η T : ZFSet.{u}) :
    (Follows [false,false] e k ∧ Follows [false,true] e η ∧ Follows [true] e T) ↔
      e = ZFSet.pair (ZFSet.pair k η) T := by
  constructor
  · rintro ⟨⟨a,⟨b,he⟩,ha⟩,hη,hT⟩
    rw [he] at hη hT
    have hT' : b = T := by simpa [Follows,component_pair] using hT
    have hη' : Follows [true] a η := by simpa only [follows_pair,Bool.false_eq_true,if_false] using hη
    obtain ⟨k',hk,hkk⟩ := ha
    obtain ⟨d,hd⟩ := hk
    subst k'
    rw [hd] at hη'
    have hηd : d = η := by simpa [Follows,component_pair] using hη'
    rw [he,hd,hηd,hT']
  · intro h
    rw [h]
    simp [Follows,component_pair]

theorem satisfies_lookup (g k η T : ZFSet.{u}) :
    Satisfies ZFMem lookupFormula ![g,k,η,T] ↔ ZFSet.pair (ZFSet.pair k η) T ∈ g := by
  simp only [lookupFormula,Satisfies,satisfies_pathEqAt]
  change (∃ e ∈ g,Follows [false,false] e k ∧ Follows [false,true] e η ∧ Follows [true] e T) ↔ _
  simp only [follows_entry_iff]
  exact ⟨fun ⟨e,he,heq⟩ => heq ▸ he,fun he => ⟨_,he,rfl⟩⟩

def towerMap : Fin 14 → Fin 17 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,16]

noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u}
    (renameScope towerMap (TowerSigma.query K J))
    (renameScope ![16,13,14,(15 : Fin 17)] (ofConstructibleDeltaZero K J lookupFormula))
    ((TowerSigma.query_isSigmaOne K J).renameScope _)
    (.deltaZero ((ofConstructibleDeltaZero_isDeltaZero K J lookupFormula).renameScope _))

/-- Fixed thirteen tower sources, block code, height code, candidate truth set. -/
noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 16 :=
  (body.{u,v} K J).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 16 → ZFCarrier V) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔
      ∃ g : ZFCarrier V,
        realize N (TowerSigma.query K J) Empty.elim
          (Fin.snoc (fun i : Fin 13 => p (Fin.castAdd 3 i)) g) ∧
        ZFSet.pair (ZFSet.pair (p 13).val (p 14).val) (p 15).val ∈ g.val := by
  rw [query,realize_scoped_ex]
  apply exists_congr
  intro g
  rw [body,realize_sigmaConjFormula,realize_renameScope,realize_renameScope]
  have ht : Fin.snoc p g ∘ towerMap = Fin.snoc (fun i : Fin 13 => p (Fin.castAdd 3 i)) g := by
    funext i
    fin_cases i <;> simp [towerMap,Function.comp_def,Fin.snoc,Fin.castLT]
  have hl : Fin.snoc p g ∘ ![16,13,14,(15 : Fin 17)] = ![g,p 13,p 14,p 15] := by
    funext i
    fin_cases i <;> simp [Function.comp_def,Fin.snoc,Fin.castLT]
  rw [ht,hl]
  apply and_congr_right
  intro _
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
  exact satisfies_lookup g.val (p 13).val (p 14).val (p 15).val

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 16 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hk : (p 13).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 14).val = s.2.val.toZFSet)
    (hq : realize N (query.{u+1,v} K J) Empty.elim p) :
    (p 15).val = truth U.val s := by
  obtain ⟨g,hg,he⟩ := (realize_query hV N hmem p).mp hq
  have hg' := TowerSigma.query_sound hV hVL N hmem κ U _
    (fun i => by simpa only [Fin.snoc_castSucc] using hp i) hg
  change g.val = @graph κ U.val at hg'
  rw [hg',hk,hη] at he
  obtain ⟨t,ht⟩ := ZFSet.mem_range.mp he
  have hparts := ZFSet.pair_inj.mp ht
  have hts : t = s := stageCode_injective hparts.1
  exact hparts.2.symm.trans (congrArg (truth U.val) hts)

theorem query_complete {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 16 → ZFCarrier (LStageZF β))
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hk : (p 13).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 14).val = s.2.val.toZFSet) (hS : (p 15).val = truth U.val s) :
    realize N (query.{u+1,v} K J) Empty.elim p := by
  have hf (i : Fin 13) : (fixedParameters κ U i).val ∈ LStageZF β :=
    hp i ▸ (p (Fin.castAdd 3 i)).property
  have hU : U.val ∈ LStageZF β := hf 0
  let g : ZFCarrier (LStageZF β) := ⟨@graph κ U.val,graph_mem_of_adequate hβ hκβ hU⟩
  apply (realize_query (LStageZF_isTransitive β) N hmem p).mpr
  refine ⟨g,?_,?_⟩
  · apply TowerSigma.query_complete hβ hκβ N hmem hCol hSep U _
      (fun i => by simpa only [Fin.snoc_castSucc] using hp i) rfl
  · rw [hk,hη,hS]
    exact ZFSet.mem_range_self (f := fun t : Stage κ => ZFSet.pair (stageCode t) (truth U.val t)) s

theorem realize_query_iff {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 16 → ZFCarrier (LStageZF β))
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hk : (p 13).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 14).val = s.2.val.toZFSet) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔ (p 15).val = truth U.val s := by
  constructor
  · exact query_sound (LStageZF_isTransitive β)
      (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)) N hmem κ U s p hp hk hη
  · exact query_complete hβ hκβ N hmem hCol hSep U s p hp hk hη

end OneYTruth.TowerPoint
