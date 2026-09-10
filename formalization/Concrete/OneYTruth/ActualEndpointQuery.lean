import OneYTruth.ActualStageTruthQuery
import OneYTruth.InternalActualTruth
import OneYTruth.SourceEndpointRelation

/-! Genuine Sigma-one comparison with the current endpoint. Only the five
raw parameters a, omega, zero, block code and height code remain. Neither
the current ambient endpoint nor its truth set is an internal parameter. -/

namespace OneYTruth.ActualEndpointQuery

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open InternalClosure ExternalTower RootSemantics EndpointComparison

universe u v

/-- a, omega, zero, block code, height code; U, smaller Sat. -/
noncomputable def sources (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u+1}
    (renameScope ![0,1,2,(5 : Fin 7)] (ActualStageQuery.query.{u,v} K J))
    (renameScope ![5,0,1,2,3,4,(6 : Fin 7)] (ActualTruthQuery.query.{u+1,v} K J))
    ((ActualStageQuery.query_isSigmaOne K J).renameScope _)
    ((ActualTruthQuery.query_isSigmaOne K J).renameScope _)

theorem sources_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (sources.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

noncomputable def query {K : Nat} {J : Type v}
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint) :
    (language K J).BoundedFormula Empty 5 :=
  (sigmaConjFormula.{v,u+1} (sources.{u,v} K J)
    (renameScope ![4,5,1,2,3,(6 : Fin 7)] (SourceEndpointComparison.query.{u+1,v} endpoint hEndpoint))
    (sources_isSigmaOne K J) ((SourceEndpointComparison.query_isSigmaOne endpoint hEndpoint).renameScope _)).ex.ex

theorem query_isSigmaOne {K : Nat} {J : Type v}
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint) :
    IsSigmaOne (query.{u,v} endpoint hEndpoint) :=
  .ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _))

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V))
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint)
    (p : Fin 5 → ZFCarrier V) :
    realize N (query.{u,v} endpoint hEndpoint) Empty.elim p ↔
      ∃ U S : ZFCarrier V,
        (realize N (ActualStageQuery.query.{u,v} K J) Empty.elim ![p 0,p 1,p 2,U] ∧
          realize N (ActualTruthQuery.query.{u+1,v} K J) Empty.elim ![U,p 0,p 1,p 2,p 3,p 4,S]) ∧
        realize N (SourceEndpointComparison.query.{u+1,v} endpoint hEndpoint) Empty.elim ![p 4,U,p 1,p 2,p 3,S] := by
  rw [query,realize_scoped_ex]
  apply exists_congr
  intro U
  rw [realize_scoped_ex]
  apply exists_congr
  intro S
  rw [realize_sigmaConjFormula,sources,realize_sigmaConjFormula]
  simp only [realize_renameScope]
  have hs : Fin.snoc (Fin.snoc p U) S ∘ ![0,1,2,(5 : Fin 7)] = ![p 0,p 1,p 2,U] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  have ht : Fin.snoc (Fin.snoc p U) S ∘ ![5,0,1,2,3,4,(6 : Fin 7)] = ![U,p 0,p 1,p 2,p 3,p 4,S] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  have hc : Fin.snoc (Fin.snoc p U) S ∘ ![4,5,1,2,3,(6 : Fin 7)] = ![p 4,U,p 1,p 2,p 3,S] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  rw [hs,ht,hc]

theorem sound_values {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint)
    (a : Ordinal.{u}) (s : Stage a) (p : Fin 5 → ZFCarrier V)
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅)
    (hk : (p 3).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 4).val = s.2.val.toZFSet)
    (hq : realize N (query.{u,v} endpoint hEndpoint) Empty.elim p) :
    ∃ U S : ZFCarrier V, U.val = LStageZF a ∧ S.val = truth (LStageZF a) s ∧
      realize N (SourceEndpointComparison.query.{u+1,v} endpoint hEndpoint) Empty.elim ![p 4,U,p 1,p 2,p 3,S] := by
  obtain ⟨U,S,⟨hU,hS⟩,hc⟩ := (realize_query N endpoint hEndpoint p).mp hq
  have he := ActualStageQuery.query_sound hV hVL N hmem a _ ha hOmega hZero hU
  let UL : LCarrier.{u} := ⟨LStageZF a,LStageZF_mem_L a⟩
  exact ⟨U,S,he,ActualTruthQuery.query_sound hV hVL N hmem a UL s _ he ha hOmega hZero hk hη hS,hc⟩

theorem complete_of_comparison {K : Nat} {J : Type v} {β a : Ordinal.{u}}
    (hβ : Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint)
    (s : Stage a) (p : Fin 5 → ZFCarrier (LStageZF β))
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅)
    (hk : (p 3).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 4).val = s.2.val.toZFSet)
    (hc : ∀ U S : ZFCarrier (LStageZF β), U.val = LStageZF a → S.val = truth (LStageZF a) s →
      realize N (SourceEndpointComparison.query.{u+1,v} endpoint hEndpoint) Empty.elim ![p 4,U,p 1,p 2,p 3,S]) :
    realize N (query.{u,v} endpoint hEndpoint) Empty.elim p := by
  have haβ : a < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
    (ha ▸ (p 0).property)
  let U : ZFCarrier (LStageZF β) := ⟨LStageZF a,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 haβ⟩
  let S : ZFCarrier (LStageZF β) := ⟨truth (LStageZF a) s,truth_LStage_mem_of_adequate hβ haβ s⟩
  let UL : LCarrier.{u} := ⟨LStageZF a,LStageZF_mem_L a⟩
  apply (realize_query N endpoint hEndpoint p).mpr
  exact ⟨U,S,⟨(ActualStageQuery.realize_query_iff hβ N hmem a _ ha hOmega hZero).mpr rfl,
    (ActualTruthQuery.realize_query_iff hβ N hmem hCol hSep UL s _ rfl ha hOmega hZero hk hη).mpr rfl⟩,
    hc U S rfl rfl⟩

noncomputable def namedComparison {K : Nat} {J : Type v} (η : J) :=
  query.{u,v} (namedQuery (k := K) η) (.rel _ _)

noncomputable def diagonalComparison {K : Nat} {J : Type v} (k : Fin K) :=
  query.{u,v} (diagonalQuery (I := J) k) (.rel _ _)

theorem namedComparison_isSigmaOne {K : Nat} {J : Type v} (η : J) :
    IsSigmaOne (namedComparison.{u,v} (K := K) η) := query_isSigmaOne _ _

theorem diagonalComparison_isSigmaOne {K : Nat} {J : Type v} (k : Fin K) :
    IsSigmaOne (diagonalComparison.{u,v} (J := J) k) := query_isSigmaOne _ _

end OneYTruth.ActualEndpointQuery
