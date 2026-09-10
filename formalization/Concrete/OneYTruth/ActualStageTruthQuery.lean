import OneYTruth.ActualTruthQuery
import OneYTruth.ActualStageQuery

/-! A canonical local truth-set certificate with only ordinal and finite
primitive parameters. The constructible domain is verified inside the query. -/

namespace OneYTruth.ActualStageTruthQuery

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open InternalClosure ExternalTower

universe u v

/-- a, omega, zero, block code, height code, Sat; existential U=L_a. -/
noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u+1}
    (renameScope ![0,1,2,(6 : Fin 7)] (ActualStageQuery.query.{u,v} K J))
    (renameScope ![6,0,1,2,3,4,(5 : Fin 7)] (ActualTruthQuery.query.{u+1,v} K J))
    ((ActualStageQuery.query_isSigmaOne K J).renameScope _)
    ((ActualTruthQuery.query_isSigmaOne K J).renameScope _)

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 6 :=
  (body.{u,v} K J).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (p : Fin 6 → ZFCarrier V) :
    realize N (query.{u,v} K J) Empty.elim p ↔
      ∃ U : ZFCarrier V,
        realize N (ActualStageQuery.query.{u,v} K J) Empty.elim ![p 0,p 1,p 2,U] ∧
        realize N (ActualTruthQuery.query.{u+1,v} K J) Empty.elim ![U,p 0,p 1,p 2,p 3,p 4,p 5] := by
  rw [query,realize_scoped_ex]
  apply exists_congr
  intro U
  rw [body,realize_sigmaConjFormula,realize_renameScope,realize_renameScope]
  have hs : Fin.snoc p U ∘ ![0,1,2,(6 : Fin 7)] = ![p 0,p 1,p 2,U] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  have ht : Fin.snoc p U ∘ ![6,0,1,2,3,4,(5 : Fin 7)] = ![U,p 0,p 1,p 2,p 3,p 4,p 5] := by
    funext i
    fin_cases i <;> simp [Fin.snoc,Fin.castLT]
  rw [hs,ht]

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (a : Ordinal.{u}) (s : Stage a) (p : Fin 6 → ZFCarrier V)
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅)
    (hk : (p 3).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 4).val = s.2.val.toZFSet)
    (hq : realize N (query.{u,v} K J) Empty.elim p) :
    (p 5).val = truth (LStageZF a) s := by
  obtain ⟨U,hU,hT⟩ := (realize_query N p).mp hq
  have he := ActualStageQuery.query_sound hV hVL N hmem a _ ha hOmega hZero hU
  let UL : LCarrier.{u} := ⟨LStageZF a,LStageZF_mem_L a⟩
  exact ActualTruthQuery.query_sound hV hVL N hmem a UL s _ he ha hOmega hZero hk hη hT

theorem realize_query_iff {K : Nat} {J : Type v} {β a : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (s : Stage a) (p : Fin 6 → ZFCarrier (LStageZF β))
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅)
    (hk : (p 3).val = Constructible.FiniteSequenceZF.natCode s.1)
    (hη : (p 4).val = s.2.val.toZFSet) :
    realize N (query.{u,v} K J) Empty.elim p ↔ (p 5).val = truth (LStageZF a) s := by
  have hV := LStageZF_isTransitive β
  have hVL : ∀ x ∈ LStageZF β, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  constructor
  · exact query_sound hV hVL N hmem a s p ha hOmega hZero hk hη
  · intro hS
    have haβ : a < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (ha ▸ (p 0).property)
    let U : ZFCarrier (LStageZF β) := ⟨LStageZF a,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 haβ⟩
    let UL : LCarrier.{u} := ⟨LStageZF a,LStageZF_mem_L a⟩
    apply (realize_query N p).mpr
    refine ⟨U,?_,?_⟩
    · exact (ActualStageQuery.realize_query_iff hβ N hmem a _ ha hOmega hZero).mpr rfl
    · exact (ActualTruthQuery.realize_query_iff hβ N hmem hCol hSep UL s _
        rfl ha hOmega hZero hk hη).mpr hS

end OneYTruth.ActualStageTruthQuery

#print axioms OneYTruth.ActualStageTruthQuery.query_isSigmaOne
#print axioms OneYTruth.ActualStageTruthQuery.query_sound
#print axioms OneYTruth.ActualStageTruthQuery.realize_query_iff
