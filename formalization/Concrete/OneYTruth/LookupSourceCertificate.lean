import OneYTruth.AssignmentSourceCertificate
import OneYTruth.InternalAssignmentLookup
import OneYTruth.BoundedFilterGraph

/-! A complete lookup-source query from only the actual domain, omega, and
empty set. Assignment sources and both product bounds are quantified and
checked internally, rather than accepted as source-parameter hypotheses. -/

namespace OneYTruth.LookupSourceCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open FirstOrder FirstOrder.Language InternalClosure InternalProducts InternalNodes
open AssignmentLookup BoundedFilterGraph

universe u v

/-- U, omega, zero, candidate; assignments, omega-times-U, lookup bound. -/
def boundsFormula : Delta0Formula 7 :=
  .conj (productAt 5 1 0) (productAt 6 4 5)

def boundsQuery (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I boundsFormula

noncomputable def assignmentsQuery (k : Nat) (I : Type v) :=
  renameScope ![0, 1, 2, (4 : Fin 7)] (AssignmentSourceCertificate.query.{u, v} k I)

def graphQuery (k : Nat) (I : Type v) :=
  renameScope ![6, 4, 1, 0, 2, (3 : Fin 7)] (lookupQuery k I)

theorem boundsQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (boundsQuery k I) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

theorem assignmentsQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (assignmentsQuery.{u, v} k I) :=
  (AssignmentSourceCertificate.query_isSigmaOne k I).renameScope _

theorem graphQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (graphQuery k I) :=
  (lookupQuery_isSigmaOne k I).renameScope _

noncomputable def sourceAndGraph (k : Nat) (I : Type v) :=
  sigmaConjFormula.{v, u} (assignmentsQuery.{u, v} k I) (graphQuery k I)
    (assignmentsQuery_isSigmaOne k I) (graphQuery_isSigmaOne k I)

theorem sourceAndGraph_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (sourceAndGraph.{u, v} k I) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

noncomputable def query (k : Nat) (I : Type v) : (language k I).BoundedFormula Empty 4 :=
  (sigmaConjFormula.{v, u} (boundsQuery k I) (sourceAndGraph.{u, v} k I)
    (boundsQuery_isSigmaOne k I) (sourceAndGraph_isSigmaOne k I)).ex.ex.ex

theorem query_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (query.{u, v} k I) :=
  .ex (.ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _)))

theorem realize_query {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 4 → ZFCarrier V) :
    realize N (query.{u+1, v} k I) Empty.elim p ↔
      ∃ A D B : ZFCarrier V,
        (D.val = pairProduct (p 1).val (p 0).val ∧ B.val = pairProduct A.val D.val) ∧
        realize N (AssignmentSourceCertificate.query.{u+1, v} k I) Empty.elim ![p 0, p 1, p 2, A] ∧
        realize N (lookupQuery k I) Empty.elim ![B, A, p 1, p 0, p 2, p 3] := by
  rw [query, realize_scoped_ex]
  apply exists_congr
  intro A
  rw [realize_scoped_ex]
  apply exists_congr
  intro D
  rw [realize_scoped_ex]
  apply exists_congr
  intro B
  rw [realize_sigmaConjFormula, sourceAndGraph, realize_sigmaConjFormula,
    assignmentsQuery, graphQuery, realize_renameScope, realize_renameScope]
  have hleft : Fin.snoc (Fin.snoc (Fin.snoc p A) D) B ∘ ![0, 1, 2, (4 : Fin 7)] =
      ![p 0, p 1, p 2, A] := by funext i; fin_cases i <;> rfl
  have hright : Fin.snoc (Fin.snoc (Fin.snoc p A) D) B ∘ ![6, 4, 1, 0, 2, (3 : Fin 7)] =
      ![B, A, p 1, p 0, p 2, p 3] := by funext i; fin_cases i <;> rfl
  rw [hleft, hright]
  apply and_congr_left
  intro _
  rw [boundsQuery, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  change (Satisfies ZFMem (productAt 5 1 0) _ ∧ Satisfies ZFMem (productAt 6 4 5) _) ↔ _
  rw [satisfies_productAt, satisfies_productAt]
  rfl

theorem query_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅)
    (h : realize N (query.{u+1, v} k I) Empty.elim p) : (p 3).val = lookupSet U.val := by
  obtain ⟨A, D, B, ⟨hD, hB⟩, hA, hL⟩ := (realize_query hV N hmem p).mp h
  have ha : A.val = assignmentCodes U.val := AssignmentSourceCertificate.query_sound hV N hmem U ![p 0, p 1, p 2, A]
    hU hOmega hZero hA
  have hb : B.val = lookupBound U.val := by
    rw [hB, ha, hD, hU, hOmega]
    rfl
  exact lookupQuery_sound hV N hmem U ![B, A, p 1, p 0, p 2, p 3]
    hb ha hOmega hU hZero hL

theorem realize_query_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅) :
    realize N (query.{u+1, v} k I) Empty.elim p ↔ (p 3).val = lookupSet U.val := by
  constructor
  · exact query_sound hV N hmem U p hU hOmega hZero
  · intro hout
    have hOmegaV : Ordinal.omega0.toZFSet ∈ V := hOmega ▸ (p 1).property
    have hUV : U.val ∈ V := hU ▸ (p 0).property
    have hAV := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmegaV U hUV
    have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
    have hp {S T : ZFSet.{u}} (hS : S ∈ V) (hT : T ∈ V) : pairProduct S T ∈ V :=
      pairProduct_mem hV N hmem (hRep 1 (pairFormula k I))
        (hRep 1 (mixedSliceGraphFormula k I)) hpair hUnion hS hT
    let A : ZFCarrier V := ⟨assignmentCodes U.val, hAV⟩
    let D : ZFCarrier V := ⟨pairProduct Ordinal.omega0.toZFSet U.val, hp hOmegaV hUV⟩
    let B : ZFCarrier V := ⟨pairProduct A.val D.val, hp A.property D.property⟩
    apply (realize_query hV N hmem p).mpr
    refine ⟨A, D, B, ⟨?_, rfl⟩, ?_, ?_⟩
    · change pairProduct Ordinal.omega0.toZFSet U.val = _
      rw [hU, hOmega]
    · exact (AssignmentSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty U
        ![p 0, p 1, p 2, A] hU hOmega hZero).mpr rfl
    · exact (realize_lookupQuery_iff hV N hmem hCol hSep hpair hUnion hempty U
        ![B, A, p 1, p 0, p 2, p 3] rfl rfl hOmega hU hZero).mpr hout

end OneYTruth.LookupSourceCertificate

#print axioms OneYTruth.LookupSourceCertificate.query_sound
#print axioms OneYTruth.LookupSourceCertificate.realize_query_iff
#print axioms OneYTruth.LookupSourceCertificate.query_isSigmaOne
