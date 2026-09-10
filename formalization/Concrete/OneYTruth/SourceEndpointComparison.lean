import OneYTruth.EndpointRelation
import OneYTruth.SigmaNodeSourceCertificate
import OneYTruth.SigmaNodeBounds

/-! Endpoint comparison with the complete Sigma-node source bound and checked
inside the formula. The smaller satisfaction set remains an explicit input;
its canonical equality is not replaced by an arbitrary candidate truth set. -/

namespace OneYTruth.SourceEndpointComparison

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language InternalClosure InternalNodes SigmaComparison
open EndpointComparison

universe u v w

/-- Alphabet, smaller domain, omega, empty, language-index code, smaller Sat;
then the existential complete Sigma-node source. -/
noncomputable def sourceQuery (K : Nat) (J : Type w) :=
  renameScope ![0, 1, 2, 3, 4, (6 : Fin 7)] (SigmaNodeSourceCertificate.query.{u, w} K J)

def comparisonQuery {K : Nat} {J : Type w}
    (endpoint : (language K J).BoundedFormula Empty 6) :=
  renameScope ![1, 6, 5, (0 : Fin 7)] (comparison endpoint)

theorem sourceQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (sourceQuery.{u, w} K J) :=
  (SigmaNodeSourceCertificate.query_isSigmaOne K J).renameScope _

theorem comparisonQuery_isSigmaOne {K : Nat} {J : Type w}
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint) :
    IsSigmaOne (comparisonQuery endpoint) :=
  .deltaZero ((comparison_isDeltaZero hEndpoint).renameScope _)

noncomputable def query {K : Nat} {J : Type w}
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint) :
    (language K J).BoundedFormula Empty 6 :=
  (sigmaConjFormula.{w, u} (sourceQuery.{u, w} K J) (comparisonQuery endpoint)
    (sourceQuery_isSigmaOne K J) (comparisonQuery_isSigmaOne endpoint hEndpoint)).ex

theorem query_isSigmaOne {K : Nat} {J : Type w}
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint) :
    IsSigmaOne (query.{u, w} endpoint hEndpoint) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {K : Nat} {J : Type w} {T : Type u}
    (N : Interpretation K J T) (endpoint : (language K J).BoundedFormula Empty 6)
    (hEndpoint : IsDeltaZero endpoint) (p : Fin 6 → T) :
    realize N (query.{u, w} endpoint hEndpoint) Empty.elim p ↔
      ∃ nodes : T, realize N (SigmaNodeSourceCertificate.query.{u, w} K J) Empty.elim
          ![p 0, p 1, p 2, p 3, p 4, nodes] ∧
        realize N (comparison endpoint) Empty.elim ![p 1, nodes, p 5, p 0] := by
  rw [query, realize_scoped_ex]
  apply exists_congr; intro nodes
  rw [realize_sigmaConjFormula, sourceQuery, comparisonQuery, realize_renameScope, realize_renameScope]
  have hs : Fin.snoc p nodes ∘ ![0, 1, 2, 3, 4, (6 : Fin 7)] =
      ![p 0, p 1, p 2, p 3, p 4, nodes] := by funext i; fin_cases i <;> rfl
  have hc : Fin.snoc p nodes ∘ ![1, 6, 5, (0 : Fin 7)] =
      ![p 1, nodes, p 5, p 0] := by funext i; fin_cases i <;> rfl
  rw [hs, hc]

theorem query_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (endpoint : (language K J).BoundedFormula Empty 6)
    (hEndpoint : IsDeltaZero endpoint) {code : I → ZFSet.{u}}
    (A U : LCarrier.{u}) (hA : A.val = ZFSet.range code) (p : Fin 6 → ZFCarrier V)
    (hAlphabet : (p 0).val = A.val) (hU : (p 1).val = U.val)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅) (hk : (p 4).val = natCode k)
    (h : realize N (query.{u+1, w} endpoint hEndpoint) Empty.elim p) :
    ∃ nodes : ZFCarrier V, nodes.val = sigmaNodes (k := k) code U.val ∧
      realize N (comparison endpoint) Empty.elim ![p 1, nodes, p 5, p 0] := by
  obtain ⟨nodes, hs, hc⟩ := (realize_query N endpoint hEndpoint p).mp h
  exact ⟨nodes, SigmaNodeSourceCertificate.query_sound hV N hmem A U hA
    ![p 0, p 1, p 2, p 3, p 4, nodes] hAlphabet hU hOmega hZero hk hs, hc⟩

theorem query_complete {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (endpoint : (language K J).BoundedFormula Empty 6) (hEndpoint : IsDeltaZero endpoint)
    {code : I → ZFSet.{u}} (A U : LCarrier.{u}) (hA : A.val = ZFSet.range code)
    (p : Fin 6 → ZFCarrier V) (hAlphabet : (p 0).val = A.val) (hU : (p 1).val = U.val)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅) (hk : (p 4).val = natCode k)
    (nodes : ZFCarrier V) (hnodes : nodes.val = sigmaNodes (k := k) code U.val)
    (hc : realize N (comparison endpoint) Empty.elim ![p 1, nodes, p 5, p 0]) :
    realize N (query.{u+1, w} endpoint hEndpoint) Empty.elim p := by
  apply (realize_query N endpoint hEndpoint p).mpr
  refine ⟨nodes, ?_, hc⟩
  exact (SigmaNodeSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty A U hA
    ![p 0, p 1, p 2, p 3, p 4, nodes] hAlphabet hU hOmega hZero hk).mpr hnodes

noncomputable def namedComparison {K : Nat} {J : Type w} (η : J) :=
  query.{u, w} (namedQuery (k := K) η) (.rel _ _)

noncomputable def diagonalComparison {K : Nat} {J : Type w} (j : Fin K) :=
  query.{u, w} (diagonalQuery (I := J) j) (.rel _ _)

theorem namedComparison_isSigmaOne {K : Nat} {J : Type w} (η : J) :
    IsSigmaOne (namedComparison.{u, w} (K := K) η) := query_isSigmaOne _ _

theorem diagonalComparison_isSigmaOne {K : Nat} {J : Type w} (j : Fin K) :
    IsSigmaOne (diagonalComparison.{u, w} (J := J) j) := query_isSigmaOne _ _

end OneYTruth.SourceEndpointComparison

#print axioms OneYTruth.SourceEndpointComparison.query_sound
#print axioms OneYTruth.SourceEndpointComparison.query_complete
#print axioms OneYTruth.SourceEndpointComparison.namedComparison_isSigmaOne
