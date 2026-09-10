import OneYTruth.SigmaFiniteConjunction
import OneYTruth.CodeUniverseCertificate
import OneYTruth.AssignmentCertificate

/-! A complete assignment-source certificate from the actual domain alone.
The code-universe witness is quantified and checked, not assumed correct. -/

namespace OneYTruth.AssignmentSourceCertificate

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open InternalClosure InternalProducts InternalNodes ConstructibleCodeUniverse

universe u v

def boundQuery (k : Nat) (I : Type v) :=
  renameScope ![0, 1, 2, (4 : Fin 5)] (CodeUniverseCertificate.query k I)

def assignmentsQuery (k : Nat) (I : Type v) :=
  renameScope ![4, 0, 1, 2, (3 : Fin 5)] (AssignmentGrammar.assignmentQuery k I)

theorem boundQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (boundQuery k I) :=
  (CodeUniverseCertificate.query_isSigmaOne k I).renameScope _

theorem assignmentsQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (assignmentsQuery k I) :=
  (AssignmentGrammar.assignmentQuery_isSigmaOne k I).renameScope _

/-- Parameters U,omega,zero,candidate; one additional witness is the code universe. -/
noncomputable def query (k : Nat) (I : Type v) : (language k I).BoundedFormula Empty 4 :=
  (sigmaConjFormula.{v, u} (boundQuery k I) (assignmentsQuery k I)
    (boundQuery_isSigmaOne k I) (assignmentsQuery_isSigmaOne k I)).ex

theorem query_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (query.{u, v} k I) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {k : Nat} {I : Type v} {A : Type u}
    (M : Interpretation k I A) (p : Fin 4 → A) :
    realize M (query.{u, v} k I) Empty.elim p ↔
      ∃ B : A, realize M (CodeUniverseCertificate.query k I) Empty.elim ![p 0, p 1, p 2, B] ∧
        realize M (AssignmentGrammar.assignmentQuery k I) Empty.elim ![B, p 0, p 1, p 2, p 3] := by
  rw [query, realize_scoped_ex]
  apply exists_congr
  intro B
  rw [realize_sigmaConjFormula, boundQuery, assignmentsQuery, realize_renameScope, realize_renameScope]
  have hleft : Fin.snoc p B ∘ ![0, 1, 2, (4 : Fin 5)] = ![p 0, p 1, p 2, B] := by
    funext i; fin_cases i <;> rfl
  have hright : Fin.snoc p B ∘ ![4, 0, 1, 2, (3 : Fin 5)] = ![B, p 0, p 1, p 2, p 3] := by
    funext i; fin_cases i <;> rfl
  rw [hleft, hright]

theorem query_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅)
    (h : realize N (query.{u+1, v} k I) Empty.elim p) : (p 3).val = assignmentCodes U.val := by
  obtain ⟨B, hB, hAs⟩ := (realize_query N p).mp h
  have hb : B.val = (codeUniverse U).val := CodeUniverseCertificate.query_sound hV N hmem
    ![p 0, p 1, p 2, B] hOmega hZero U hU hB
  exact AssignmentGrammar.assignmentQuery_sound hV N hmem U ![B, p 0, p 1, p 2, p 3]
    hb hU hOmega hZero hAs

theorem realize_query_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅) :
    realize N (query.{u+1, v} k I) Empty.elim p ↔ (p 3).val = assignmentCodes U.val := by
  constructor
  · exact query_sound hV N hmem U p hU hOmega hZero
  · intro hout
    have hB := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty
      (hOmega ▸ (p 1).property) U (hU ▸ (p 0).property)
    let B : ZFCarrier V := ⟨(codeUniverse U).val, hB⟩
    apply (realize_query N p).mpr
    refine ⟨B, ?_, ?_⟩
    · apply (CodeUniverseCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
        ![p 0, p 1, p 2, B] hOmega hZero U hU).mpr
      rfl
    · exact (AssignmentGrammar.realize_assignmentQuery_iff hV N hmem hCol hSep hpair hUnion hempty U
        ![B, p 0, p 1, p 2, p 3] rfl hU hOmega hZero).mpr hout

end OneYTruth.AssignmentSourceCertificate
