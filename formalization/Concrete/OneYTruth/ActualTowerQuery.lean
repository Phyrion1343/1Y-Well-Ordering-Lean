import OneYTruth.FixedTowerSources
import OneYTruth.TowerSigmaComplete
import OneYTruth.FiniteWitnessReflection

/-! Complete tower normalization from five primitive parameters. The code
universe, assignments, lookup, tags, domain, local witnesses, and whole graph
are checked inside one genuine Sigma-one formula. -/

namespace OneYTruth.ActualTowerQuery

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open InternalClosure ExternalTower GraphStepMatrix

universe u v

/-- U, kappa, omega, zero, graph; code universe, assignments, lookup, six tags. -/
def fixedMap : Fin 13 → Fin 14 := ![0,1,5,6,7,2,3,8,9,10,11,12,13]
def towerMap : Fin 14 → Fin 14 := ![0,1,5,6,7,2,3,8,9,10,11,12,13,4]

noncomputable def fixedAt (K : Nat) (J : Type v) :=
  renameScope fixedMap (FixedTowerSources.query.{u,v} K J)
def towerAt (K : Nat) (J : Type v) := renameScope towerMap (TowerSigma.query K J)
theorem fixedAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (fixedAt.{u,v} K J) :=
  (FixedTowerSources.query_isSigmaOne K J).renameScope _
theorem towerAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (towerAt K J) :=
  (TowerSigma.query_isSigmaOne K J).renameScope _

noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u} (fixedAt.{u,v} K J) (towerAt K J)
    (fixedAt_isSigmaOne K J) (towerAt_isSigmaOne K J)
theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_body {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 14 → A) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      realize N (FixedTowerSources.query.{u,v} K J) Empty.elim (p ∘ fixedMap) ∧
      realize N (TowerSigma.query K J) Empty.elim (p ∘ towerMap) := by
  rw [body,realize_sigmaConjFormula,fixedAt,towerAt,realize_renameScope,realize_renameScope]

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 5 :=
  existsSuffix 9 (body.{u,v} K J)
theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  existsSuffix_isSigmaOne _ (body_isSigmaOne K J)

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (p : Fin 5 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hκ : (p 1).val = κ.toZFSet)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅)
    (h : realize N (query.{u+1,v} K J) Empty.elim p) : (p 4).val = @graph κ U.val := by
  obtain ⟨w,hw⟩ := (realize_existsSuffix (m := 9) N (body.{u+1,v} K J) p).mp h
  let q := Fin.append p w
  obtain ⟨hf,ht⟩ := (realize_body N q).mp hw
  have hfixed := FixedTowerSources.query_sound hV N hmem κ U (q ∘ fixedMap) hU hκ hOmega hZero hf
  apply TowerSigma.query_sound hV hVL N hmem κ U (q ∘ towerMap) ?_ ht
  intro i
  have hi : towerMap i.castSucc = fixedMap i := by fin_cases i <;> rfl
  simpa only [Function.comp_apply,hi] using hfixed i

theorem realize_query_iff {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (U : LCarrier.{u}) (p : Fin 5 → ZFCarrier (LStageZF β))
    (hU : (p 0).val = U.val) (hκ : (p 1).val = κ.toZFSet)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔ (p 4).val = @graph κ U.val := by
  have hV := LStageZF_isTransitive β
  have hVL : ∀ x ∈ LStageZF β, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  constructor
  · exact query_sound hV hVL N hmem κ U p hU hκ hOmega hZero
  · intro hg
    have hκβ : κ < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (hκ ▸ (p 1).property)
    have hpair : ∀ x ∈ LStageZF β, ∀ y ∈ LStageZF β, ZFSet.pair x y ∈ LStageZF β :=
      fun _ hx _ hy => orderedPair_mem_LStageZF_of_isSuccLimit hβ.2.1 hx hy
    have hUnion : ∀ x ∈ LStageZF β, ZFSet.sUnion x ∈ LStageZF β :=
      fun _ hx => sUnion_mem_LStageZF_of_isSuccLimit hβ.2.1 hx
    have h0 : (∅ : ZFSet.{u}) ∈ LStageZF β := hZero ▸ (p 3).property
    have hm := InternalActualStep.fixedParameters_mem hV N hmem hCol hSep hpair hUnion
      (hOmega ▸ (p 2).property) κ U (hκ ▸ (p 1).property) (hU ▸ (p 0).property)
    let f : Fin 13 → ZFCarrier (LStageZF β) := fun i => ⟨(fixedParameters κ U i).val,hm i⟩
    let w : Fin 9 → ZFCarrier (LStageZF β) := ![f 2,f 3,f 4,f 7,f 8,f 9,f 10,f 11,f 12]
    let q := Fin.append p w
    have hf : ∀ i, (q (fixedMap i)).val = (fixedParameters κ U i).val := by
      intro i
      fin_cases i <;> first | exact hU | exact hκ | exact hOmega | exact hZero | rfl
    apply (realize_existsSuffix (m := 9) N (body.{u+1,v} K J) p).mpr
    refine ⟨w,(realize_body N q).mpr ⟨?_,?_⟩⟩
    · exact FixedTowerSources.actual_query hV N hmem hCol hSep hpair hUnion h0 κ U (q ∘ fixedMap) hf
    · apply TowerSigma.query_complete hβ hκβ N hmem hCol hSep U (q ∘ towerMap) ?_ hg
      intro i
      have hi : towerMap i.castSucc = fixedMap i := by fin_cases i <;> rfl
      simpa only [Function.comp_apply,hi] using hf i

end OneYTruth.ActualTowerQuery

#print axioms OneYTruth.ActualTowerQuery.query_isSigmaOne
#print axioms OneYTruth.ActualTowerQuery.query_sound
#print axioms OneYTruth.ActualTowerQuery.realize_query_iff
