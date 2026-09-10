import OneYTruth.ActualAdequacyCertificateInternal
import OneYTruth.ActualStageQuery

/-! Actual adequacy from exactly three primitive parameters: a, omega, empty.
The canonical domain L_a is existentially certified along with every source,
truth graph, schema bundle, and field bound. -/

namespace OneYTruth.ActualAdequateQuery

open Constructible Constructible.Model FirstOrder FirstOrder.Language InternalClosure

universe u v

noncomputable def adequacyAt (K : Nat) (J : Type v) :=
  renameScope ![3,0,1,(2 : Fin 4)] (ActualAdequacyCertificate.query.{u,v} K J)

theorem adequacyAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (adequacyAt.{u,v} K J) :=
  (ActualAdequacyCertificate.query_isSigmaOne K J).renameScope _

noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u+1} (ActualStageQuery.query.{u,v} K J) (adequacyAt.{u,v} K J)
    (ActualStageQuery.query_isSigmaOne K J) (adequacyAt_isSigmaOne K J)

theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_body {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (p : Fin 4 → ZFCarrier V) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      realize N (ActualStageQuery.query.{u,v} K J) Empty.elim p ∧
      realize N (ActualAdequacyCertificate.query.{u,v} K J) Empty.elim ![p 3,p 0,p 1,p 2] := by
  rw [body,realize_sigmaConjFormula,adequacyAt,realize_renameScope]
  have he : p ∘ ![3,0,1,(2 : Fin 4)] = ![p 3,p 0,p 1,p 2] := by
    funext i; fin_cases i <;> rfl
  rw [he]

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 3 :=
  (body.{u,v} K J).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (body_isSigmaOne K J)

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (a : Ordinal.{u}) (p : Fin 3 → ZFCarrier V)
    (ha : (p 0).val = a.toZFSet) (hW : (p 1).val = Ordinal.omega0.toZFSet)
    (h0 : (p 2).val = ∅) (h : realize N (query.{u,v} K J) Empty.elim p) :
    RootSemantics.Adequate a := by
  obtain ⟨U,hU⟩ := (realize_scoped_ex N (body.{u,v} K J) p).mp h
  obtain ⟨hstage,hAdeq⟩ := (realize_body N (Fin.snoc p U)).mp hU
  have hUL : U.val = LStageZF a := ActualStageQuery.query_sound hV hVL N hmem a (Fin.snoc p U) ha hW h0 hstage
  exact ActualAdequacyCertificate.query_sound hV hVL N hmem a ![U,p 0,p 1,p 2] hUL ha hW h0 hAdeq

theorem realize_query_iff {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (a : Ordinal.{u}) (p : Fin 3 → ZFCarrier (LStageZF β))
    (ha : (p 0).val = a.toZFSet) (hW : (p 1).val = Ordinal.omega0.toZFSet) (h0 : (p 2).val = ∅) :
    realize N (query.{u,v} K J) Empty.elim p ↔ RootSemantics.Adequate a := by
  constructor
  · exact query_sound (LStageZF_isTransitive β)
      (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)) N hmem a p ha hW h0
  · intro hAdeq
    have hab : a < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (ha ▸ (p 0).property)
    let U : ZFCarrier (LStageZF β) := ⟨LStageZF a,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 hab⟩
    apply (realize_scoped_ex N (body.{u,v} K J) p).mpr
    refine ⟨U,(realize_body N (Fin.snoc p U)).mpr ⟨?_,?_⟩⟩
    · exact (ActualStageQuery.realize_query_iff hβ N hmem a (Fin.snoc p U) ha hW h0).mpr rfl
    · exact ActualAdequacyCertificate.query_complete hβ N hmem hCol hSep a ![U,p 0,p 1,p 2] rfl ha hW h0 hAdeq

end OneYTruth.ActualAdequateQuery

#print axioms OneYTruth.ActualAdequateQuery.query_isSigmaOne
#print axioms OneYTruth.ActualAdequateQuery.query_sound
#print axioms OneYTruth.ActualAdequateQuery.realize_query_iff
