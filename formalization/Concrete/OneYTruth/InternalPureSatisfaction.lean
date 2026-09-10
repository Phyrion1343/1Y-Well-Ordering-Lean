import OneYTruth.PureSatisfactionSource
import OneYTruth.InternalGraphInput
import OneYTruth.InternalSyntaxCodes

/-! The actual complete pure satisfaction certificate belongs to the ambient
domain under its real Separation and Collection schemas. -/

namespace OneYTruth.PureSatisfactionSource

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open InternalClosure InternalNodes AssignmentLookup SyntaxDiagram PureSatisfactionMatrix

universe u v

section

variable {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V)

include hV N hmem hCol hSep hpair hUnion hOmega

theorem actual_mem (U : LCarrier.{u}) (hU : U.val ∈ V) : ∀ i, actual U.val i ∈ V := by
  have hn (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n,rfl⟩) hOmega
  have h0 : (∅ : ZFSet.{u}) ∈ V := by simpa [natCode] using hn 0
  have hi : Function.Injective (Empty.elim : Empty → ZFSet.{u}) := fun i => i.elim
  have hF := InternalSyntaxCodes.syntaxCodes_mem (k := 0) hV N hmem hCol hSep hpair hUnion h0 hOmega
    emptyLCarrier empty_range.symm h0
  have hA := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion h0 hOmega U hU
  have hL := AssignmentLookup.lookupSet_mem hV N hmem hCol hSep hpair hUnion h0 hOmega U hU
  obtain ⟨hNodes,hAtoms,hImp,hQuant,hChild⟩ := InternalDiagram.structural_sets_mem
    hV N hmem hCol hSep hpair hUnion (hn 5) (hn 6) hU
      (Empty.elim : Empty → ZFSet.{u}) hF hA
  have hProd {A B : ZFSet.{u}} (ha : A ∈ V) (hb : B ∈ V) : InternalProducts.pairProduct A B ∈ V :=
    InternalGraphInput.product_mem hV N hmem hCol hSep hpair hUnion ha hb
  have hParams : ∀ i, AtomicTruthFormula.parameters (Empty.elim : Empty → ZFSet.{u})
      (interpretation U.val) i ∈ V := by
    intro i
    fin_cases i <;> simp only [AtomicTruthFormula.parameters,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ,Matrix.cons_val_fin_one,empty_range,namedGraph_eq_empty,diagonalGraph_eq_empty]
    all_goals first | exact hU | exact hL | exact hA | exact hOmega | exact h0 | exact hn _
  have hTrue := InternalGraphInput.trueAtomSet_mem hV N hmem hSep hi
    (interpretation U.val) (fun _ _ => Iff.rfl) hParams hAtoms
  have hSat := satisfactionSet_mem_of_internal_sources hV N hmem hCol hSep hpair hUnion
    hOmega h0 (hn 5) (hn 6) hU hi hF hA (interpretation U.val) hTrue
  intro i
  fin_cases i <;> first
    | exact hU | exact hOmega | exact h0 | exact hSat | exact hn 1 | exact hn 2
    | exact hn 3 | exact hn 4 | exact hn 5 | exact hn 6 | exact hF | exact hA
    | exact hL | exact hNodes | exact hAtoms | exact hQuant | exact hImp | exact hChild
    | exact hTrue | exact hProd hF hA | exact hProd hNodes hNodes
    | exact hProd hNodes (hProd hNodes hNodes)

theorem actual_body (U : LCarrier.{u}) (p : Fin 22 → ZFCarrier V)
    (hp : ∀ i, (p i).val = actual U.val i) :
    realize N (body.{u+1,v} K J) Empty.elim p := by
  have hz : (p 2).val = (∅ : ZFSet.{u}) := hp 2
  have h0 : (∅ : ZFSet.{u}) ∈ V := hz ▸ (p 2).property
  apply (realize_body N p).mpr
  refine ⟨?_,?_,?_,?_⟩
  · exact (SyntaxSourceCertificate.realize_query_iff .full hV N hmem hCol hSep hpair hUnion h0
      emptyLCarrier empty_range.symm ![p 2,p 1,p 2,p 2,p 10]
      (hp 2) (hp 1) (hp 2) (show (p 2).val = natCode 0 by simpa [natCode] using hz)).mpr (hp 10)
  · exact (AssignmentSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion h0
      U ![p 0,p 1,p 2,p 11] (hp 0) (hp 1) (hp 2)).mpr (hp 11)
  · exact (LookupSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion h0
      U ![p 0,p 1,p 2,p 12] (hp 0) (hp 1) (hp 2)).mpr (hp 12)
  · rw [matrixAt,realize_ofConstructibleDeltaZero_absolute hV N hmem]
    rw [show Constructible.Delta0Formula.val p = actual U.val from funext hp,satisfies_matrix]
    exact actual_checks U.val

end

theorem realize_query_iff {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (U : LCarrier.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = U.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔
      (p 3).val = satisfactionSet Empty.elim (interpretation U.val) := by
  constructor
  · intro h
    have hs := query_sound hV N hmem U p hU hOmega hZero h
    rw [hU] at hs
    exact hs
  · intro hSat
    have hw := actual_mem hV N hmem hCol hSep hpair hUnion (hOmega ▸ (p 1).property)
      U (hU ▸ (p 0).property)
    let w : Fin 18 → ZFCarrier V := fun i => ⟨actual U.val (Fin.natAdd 4 i),hw _⟩
    apply (realize_existsSuffix (m := 18) N (body.{u+1,v} K J) p).mpr
    refine ⟨w,actual_body hV N hmem hCol hSep hpair hUnion
      (hOmega ▸ (p 1).property) U (Fin.append p w) ?_⟩
    intro i
    fin_cases i <;> first | exact hU | exact hOmega | exact hZero | exact hSat | rfl

end OneYTruth.PureSatisfactionSource

#print axioms OneYTruth.PureSatisfactionSource.query_isSigmaOne
#print axioms OneYTruth.PureSatisfactionSource.query_sound
#print axioms OneYTruth.PureSatisfactionSource.realize_query_iff
