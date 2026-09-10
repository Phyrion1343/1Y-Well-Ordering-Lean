import OneYTruth.SyntaxSourceCertificate
import OneYTruth.AssignmentSourceCertificate
import OneYTruth.SigmaNodeCertificate
import OneYTruth.InternalSourceSets

/-! A single genuine Sigma-one query for all Sigma-one formula/assignment
nodes from primitive sources. Syntax, assignments, product, and matching
scope are all checked internally; no canonical complete source is a premise. -/

namespace OneYTruth.SigmaNodeSourceCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FirstOrder FirstOrder.Language
open InternalClosure InternalNodes InternalProducts SigmaComparison

universe u v w

/-- A, U, omega, zero, natCode(k), nodes; Sigma codes, assignments, product. -/
noncomputable def syntaxQuery (K : Nat) (J : Type w) :=
  renameScope ![0, 2, 3, 4, (6 : Fin 9)] (SyntaxSourceCertificate.query.{u, w} .sigma K J)

noncomputable def assignmentsQuery (K : Nat) (J : Type w) :=
  renameScope ![1, 2, 3, (7 : Fin 9)] (AssignmentSourceCertificate.query.{u, w} K J)

def nodesQuery (K : Nat) (J : Type w) :=
  renameScope ![6, 7, 8, (5 : Fin 9)] (SigmaNodeCertificate.mixedFormula K J)

theorem syntaxQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (syntaxQuery.{u, w} K J) :=
  (SyntaxSourceCertificate.query_isSigmaOne .sigma K J).renameScope _

theorem assignmentsQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (assignmentsQuery.{u, w} K J) :=
  (AssignmentSourceCertificate.query_isSigmaOne K J).renameScope _

theorem nodesQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (nodesQuery K J) :=
  .deltaZero ((SigmaNodeCertificate.mixedFormula_isDeltaZero K J).renameScope _)

noncomputable def sourcesQuery (K : Nat) (J : Type w) :=
  sigmaConjFormula.{w, u} (syntaxQuery.{u, w} K J) (assignmentsQuery.{u, w} K J)
    (syntaxQuery_isSigmaOne K J) (assignmentsQuery_isSigmaOne K J)

theorem sourcesQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (sourcesQuery.{u, w} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

noncomputable def query (K : Nat) (J : Type w) : (language K J).BoundedFormula Empty 6 :=
  (sigmaConjFormula.{w, u} (sourcesQuery.{u, w} K J) (nodesQuery K J)
    (sourcesQuery_isSigmaOne K J) (nodesQuery_isSigmaOne K J)).ex.ex.ex

theorem query_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (query.{u, w} K J) :=
  .ex (.ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _)))

theorem realize_query {K : Nat} {J : Type w} {T : Type u}
    (N : Interpretation K J T) (p : Fin 6 → T) :
    realize N (query.{u, w} K J) Empty.elim p ↔
      ∃ S A B : T,
        (realize N (SyntaxSourceCertificate.query.{u, w} .sigma K J) Empty.elim ![p 0, p 2, p 3, p 4, S] ∧
          realize N (AssignmentSourceCertificate.query.{u, w} K J) Empty.elim ![p 1, p 2, p 3, A]) ∧
        realize N (SigmaNodeCertificate.mixedFormula K J) Empty.elim ![S, A, B, p 5] := by
  rw [query, realize_scoped_ex]
  apply exists_congr; intro S
  rw [realize_scoped_ex]
  apply exists_congr; intro A
  rw [realize_scoped_ex]
  apply exists_congr; intro B
  rw [realize_sigmaConjFormula, sourcesQuery, realize_sigmaConjFormula,
    syntaxQuery, assignmentsQuery, nodesQuery, realize_renameScope, realize_renameScope, realize_renameScope]
  have hs : Fin.snoc (Fin.snoc (Fin.snoc p S) A) B ∘ ![0, 2, 3, 4, (6 : Fin 9)] =
      ![p 0, p 2, p 3, p 4, S] := by funext i; fin_cases i <;> rfl
  have ha : Fin.snoc (Fin.snoc (Fin.snoc p S) A) B ∘ ![1, 2, 3, (7 : Fin 9)] =
      ![p 1, p 2, p 3, A] := by funext i; fin_cases i <;> rfl
  have hn : Fin.snoc (Fin.snoc (Fin.snoc p S) A) B ∘ ![6, 7, 8, (5 : Fin 9)] =
      ![S, A, B, p 5] := by funext i; fin_cases i <;> rfl
  rw [hs, ha, hn]

theorem query_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {code : I → ZFSet.{u}}
    (A U : LCarrier.{u}) (hA : A.val = ZFSet.range code) (p : Fin 6 → ZFCarrier V)
    (hAlphabet : (p 0).val = A.val) (hU : (p 1).val = U.val)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅) (hk : (p 4).val = natCode k)
    (h : realize N (query.{u+1, w} K J) Empty.elim p) : (p 5).val = sigmaNodes (k := k) code U.val := by
  obtain ⟨S, As, B, ⟨hS, hAs⟩, hNodes⟩ := (realize_query N p).mp h
  have hs : S.val = sigmaCodes (k := k) code := SyntaxSourceCertificate.query_sound .sigma hV N hmem
    A hA ![p 0, p 2, p 3, p 4, S] hAlphabet hOmega hZero hk hS
  have ha : As.val = assignmentCodes U.val := AssignmentSourceCertificate.query_sound hV N hmem
    U ![p 1, p 2, p 3, As] hU hOmega hZero hAs
  exact ((SigmaNodeCertificate.realize_iff_canonical hV N hmem code U.val ![S, As, B, p 5] hs ha).mp hNodes).2

theorem realize_query_iff {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {code : I → ZFSet.{u}} (A U : LCarrier.{u}) (hA : A.val = ZFSet.range code)
    (p : Fin 6 → ZFCarrier V) (hAlphabet : (p 0).val = A.val) (hU : (p 1).val = U.val)
    (hOmega : (p 2).val = Ordinal.omega0.toZFSet) (hZero : (p 3).val = ∅) (hk : (p 4).val = natCode k) :
    realize N (query.{u+1, w} K J) Empty.elim p ↔ (p 5).val = sigmaNodes (k := k) code U.val := by
  constructor
  · exact query_sound hV N hmem A U hA p hAlphabet hU hOmega hZero hk
  · intro hout
    have hW : Ordinal.omega0.toZFSet ∈ V := hOmega ▸ (p 2).property
    have hAV : A.val ∈ V := hAlphabet ▸ (p 0).property
    have hUV : U.val ∈ V := hU ▸ (p 1).property
    have hSV := InternalSyntaxCodes.sigmaCodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hW A hA hAV
    have hAsV := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hW U hUV
    let S : ZFCarrier V := ⟨sigmaCodes (k := k) code, hSV⟩
    let As : ZFCarrier V := ⟨assignmentCodes U.val, hAsV⟩
    have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
    have hBV := pairProduct_mem hV N hmem (hRep 1 (pairFormula K J))
      (hRep 1 (mixedSliceGraphFormula K J)) hpair hUnion hSV hAsV
    let B : ZFCarrier V := ⟨pairProduct S.val As.val, hBV⟩
    apply (realize_query N p).mpr
    refine ⟨S, As, B, ⟨?_, ?_⟩, ?_⟩
    · exact (SyntaxSourceCertificate.realize_query_iff .sigma hV N hmem hCol hSep hpair hUnion hempty
        A hA ![p 0, p 2, p 3, p 4, S] hAlphabet hOmega hZero hk).mpr rfl
    · exact (AssignmentSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
        U ![p 1, p 2, p 3, As] hU hOmega hZero).mpr rfl
    · exact (SigmaNodeCertificate.realize_iff_canonical hV N hmem code U.val ![S, As, B, p 5] rfl rfl).mpr ⟨rfl, hout⟩

end OneYTruth.SigmaNodeSourceCertificate

#print axioms OneYTruth.SigmaNodeSourceCertificate.query_sound
#print axioms OneYTruth.SigmaNodeSourceCertificate.realize_query_iff
#print axioms OneYTruth.SigmaNodeSourceCertificate.query_isSigmaOne
