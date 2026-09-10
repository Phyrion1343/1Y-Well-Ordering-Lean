import OneYTruth.ActualTowerQuery
import OneYTruth.TowerPointCertificate

/-! Canonical satisfaction from seven primitive parameters. All syntax,
assignment, lookup, graph and local certificate sources are quantified and
verified within the formula; no canonical Sat equality is a hypothesis. -/

namespace OneYTruth.ActualTruthQuery

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open InternalClosure ExternalTower

universe u v

/-- U, kappa, omega, zero, block code, height code, Sat; existential graph. -/
noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u}
    (renameScope ![0,1,2,3,(7 : Fin 8)] (ActualTowerQuery.query.{u,v} K J))
    (renameScope ![7,4,5,(6 : Fin 8)] (ofConstructibleDeltaZero K J TowerPoint.lookupFormula))
    ((ActualTowerQuery.query_isSigmaOne K J).renameScope _)
    (.deltaZero ((ofConstructibleDeltaZero_isDeltaZero K J TowerPoint.lookupFormula).renameScope _))

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 7 :=
  (body.{u,v} K J).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 7 → ZFCarrier V) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔
      ∃ g : ZFCarrier V,
        realize N (ActualTowerQuery.query.{u+1,v} K J) Empty.elim ![p 0,p 1,p 2,p 3,g] ∧
        ZFSet.pair (ZFSet.pair (p 4).val (p 5).val) (p 6).val ∈ g.val := by
  rw [query,realize_scoped_ex]
  apply exists_congr
  intro g
  rw [body,realize_sigmaConjFormula,realize_renameScope,realize_renameScope]
  have ht : Fin.snoc p g ∘ ![0,1,2,3,(7 : Fin 8)] = ![p 0,p 1,p 2,p 3,g] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  have hl : Fin.snoc p g ∘ ![7,4,5,(6 : Fin 8)] = ![g,p 4,p 5,p 6] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  rw [ht,hl]
  apply and_congr_right
  intro _
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
  exact TowerPoint.satisfies_lookup g.val (p 4).val (p 5).val (p 6).val

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ : Ordinal.{u}) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 7 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hκ : (p 1).val = κ.toZFSet)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅)
    (hk : (p 4).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 5).val = s.2.val.toZFSet)
    (hq : realize N (query.{u+1,v} K J) Empty.elim p) :
    (p 6).val = truth U.val s := by
  obtain ⟨g,hg,he⟩ := (realize_query hV N hmem p).mp hq
  have hg' := ActualTowerQuery.query_sound hV hVL N hmem κ U _ hU hκ hOmega hZero hg
  change g.val = @graph κ U.val at hg'
  rw [hg',hk,hη] at he
  obtain ⟨t,ht⟩ := ZFSet.mem_range.mp he
  have hparts := ZFSet.pair_inj.mp ht
  have hts : t = s := stageCode_injective hparts.1
  exact hparts.2.symm.trans (congrArg (truth U.val) hts)

theorem realize_query_iff {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u}) (s : Stage κ)
    (p : Fin 7 → ZFCarrier (LStageZF β))
    (hU : (p 0).val = U.val) (hκ : (p 1).val = κ.toZFSet)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅)
    (hk : (p 4).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 5).val = s.2.val.toZFSet) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔ (p 6).val = truth U.val s := by
  have hV := LStageZF_isTransitive β
  have hVL : ∀ x ∈ LStageZF β, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  constructor
  · exact query_sound hV hVL N hmem κ U s p hU hκ hOmega hZero hk hη
  · intro hS
    have hκβ : κ < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (hκ ▸ (p 1).property)
    let g : ZFCarrier (LStageZF β) := ⟨@graph κ U.val,
      graph_mem_of_adequate hβ hκβ (hU ▸ (p 0).property)⟩
    apply (realize_query hV N hmem p).mpr
    refine ⟨g,?_,?_⟩
    · exact (ActualTowerQuery.realize_query_iff hβ N hmem hCol hSep U _ hU hκ hOmega hZero).mpr rfl
    · rw [hk,hη,hS]
      exact ZFSet.mem_range_self (f := fun t : Stage κ => ZFSet.pair (stageCode t) (truth U.val t)) s

end OneYTruth.ActualTruthQuery

#print axioms OneYTruth.ActualTruthQuery.query_isSigmaOne
#print axioms OneYTruth.ActualTruthQuery.query_sound
#print axioms OneYTruth.ActualTruthQuery.realize_query_iff
