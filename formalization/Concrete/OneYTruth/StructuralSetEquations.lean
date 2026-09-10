import OneYTruth.BoundedFilterGraph

/-! Exact pure Separation equations for the five canonical structural sets. -/

namespace OneYTruth.StructuralSetEquations

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language FormulaCode SyntaxDiagram InternalNodes InternalProducts
open BoundedFilterGraph AtomicCodeFormula QuantifiedCodeFormula
open ImplicationCodeFormula ChildrenCodeFormula

universe u v

theorem scopedPairs_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) :
    scopedPairs (k := k) U code =
      ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x])
        (pairProduct (syntaxCodes (k := k) code) (assignmentCodes U)) := by
  rw [scopedPairs_eq_filtered_crossCode]
  have h := filtered_range_eq_sep (crossCode (k := k) (U := U) code)
    (fun z => z.1.1 = z.2.1) matchingArityFormula ![] (fun z => by
      have he : snoc ![] (crossCode code z) = ![crossCode code z] := by
        funext i; fin_cases i; rfl
      rw [he]
      exact satisfies_matchingArityFormula code z)
  rw [crossCode_range] at h
  simpa only [show ∀ x : ZFSet.{u}, snoc ![] x = ![x] from fun x => by
    funext i; fin_cases i; rfl] using h

theorem atomSet_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) :
    atomSet (k := k) U code =
      ZFSet.sep (fun x => Satisfies ZFMem atomicFormula ![natCode 5, x])
        (scopedPairs (k := k) U code) := by
  have h := filtered_range_eq_sep (nodeCode (k := k) (U := U) code)
    (fun z => IsAtomic z.1.2) atomicFormula ![natCode 5] (fun z => by
      have he : snoc ![natCode 5] (nodeCode code z) = ![natCode 5, nodeCode code z] := by
        funext i; fin_cases i <;> rfl
      rw [he]
      exact satisfies_atomicFormula_code code z)
  have hr : ZFSet.range (nodeCode (k := k) (U := U) code) = scopedPairs (k := k) U code := by
    unfold nodeCode scopedPairs
    rfl
  rw [hr] at h
  simpa only [atomSet,
    show ∀ x : ZFSet.{u}, snoc ![natCode 5] x = ![natCode 5, x] from fun x => by
    funext i; fin_cases i <;> rfl] using h

theorem quantifiedSet_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) :
    quantifiedSet (k := k) U code =
      ZFSet.sep (fun x => Satisfies ZFMem quantifiedFormula ![natCode 6, x])
        (scopedPairs (k := k) U code) := by
  rw [quantifiedSet_eq_filtered_range]
  have h := filtered_range_eq_sep (nodeCode (k := k) (U := U) code)
    (fun z => IsQuantified z.1.2) quantifiedFormula ![natCode 6] (fun z => by
      have he : snoc ![natCode 6] (nodeCode code z) = ![natCode 6, nodeCode code z] := by
        funext i; fin_cases i <;> rfl
      rw [he]
      exact satisfies_quantifiedFormula_code code z)
  have hr : ZFSet.range (nodeCode (k := k) (U := U) code) = scopedPairs (k := k) U code := by
    unfold nodeCode scopedPairs
    rfl
  rw [hr] at h
  simpa only [
    show ∀ x : ZFSet.{u}, snoc ![natCode 6] x = ![natCode 6, x] from fun x => by
    funext i; fin_cases i <;> rfl] using h

theorem implicationSet_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) :
    implicationSet (k := k) U code =
      ZFSet.sep (fun x => Satisfies ZFMem implicationFormula ![natCode 5, x])
        (pairProduct (scopedPairs (k := k) U code)
          (pairProduct (scopedPairs (k := k) U code) (scopedPairs (k := k) U code))) := by
  rw [implicationSet_eq_filtered_triples]
  have h := filtered_range_eq_sep (tripleCode (k := k) (U := U) code)
    (ImplicationCodeFormula.Matches code) implicationFormula ![natCode 5] (fun z => by
      have he : snoc ![natCode 5] (tripleCode code z) = ![natCode 5, tripleCode code z] := by
        funext i; fin_cases i <;> rfl
      rw [he]
      exact satisfies_implicationFormula_codes code z)
  rw [tripleCode_range] at h
  simpa only [show ∀ x : ZFSet.{u}, snoc ![natCode 5] x = ![natCode 5, x] from fun x => by
    funext i; fin_cases i <;> rfl] using h

theorem childrenSet_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) :
    childrenSet (k := k) U code =
      ZFSet.sep (fun x => Satisfies ZFMem childrenFormula ![natCode 6, U, x])
        (pairProduct (scopedPairs (k := k) U code) (scopedPairs (k := k) U code)) := by
  rw [childrenSet_eq_filtered_pairs]
  have h := filtered_range_eq_sep (edgeCode (k := k) (U := U) code)
    (ChildrenCodeFormula.Matches code) childrenFormula ![natCode 6, U] (fun z => by
      have he : snoc ![natCode 6, U] (edgeCode code z) = ![natCode 6, U, edgeCode code z] := by
        funext i; fin_cases i <;> rfl
      rw [he]
      exact satisfies_childrenFormula_codes code z)
  rw [edgeCode_range] at h
  simpa only [show ∀ x : ZFSet.{u}, snoc ![natCode 6, U] x = ![natCode 6, U, x] from fun x => by
    funext i; fin_cases i <;> rfl] using h

end OneYTruth.StructuralSetEquations
