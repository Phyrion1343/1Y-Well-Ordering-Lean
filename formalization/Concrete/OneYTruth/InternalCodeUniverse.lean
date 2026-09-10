import OneYTruth.InternalUniformIteration
import OneYTruth.ConstructibleDiagramSources

/-! # Actual finite-code closures inside an adequate transitive domain -/

namespace OneYTruth.InternalCodeUniverse

open Constructible Constructible.Delta0Formula Constructible.Model Constructible.Godel
open InternalClosure InternalProducts ConstructibleCodeUniverse ConstructibleListCodes

universe u v

theorem F2_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {A B : ZFSet.{u}} (hA : A ∈ V) (hB : B ∈ V) : F2 A B ∈ V := by
  rw [← ConstructibleDiagramSources.pairProduct_eq_F2]
  have hr := hasReplacement_of_collection_separation N hmem hCol hSep
  exact pairProduct_mem hV N hmem (hr 1 (pairFormula k I))
    (hr 1 (mixedSliceGraphFormula k I)) hpair hUnion hA hB

theorem codeUniverse_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (A : LCarrier.{u}) (hA : A.val ∈ V) :
    (codeUniverse A).val ∈ V := by
  apply InternalIteration.uniformUnion_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    pairStepFormula ![emptyLCarrier] (by intro i; fin_cases i; exact hempty) pairStep
    ?_ pairStepL (fun _ => rfl) pairStep_defines ?_ (seed A)
    (binaryUnion_mem hV hpair hUnion hA hOmega)
  · intro S T
    have ht : snoc (snoc (fun i => (![emptyLCarrier] i : LCarrier.{u}).val) S) T =
        ![∅, S, T] := by funext i; fin_cases i <;> rfl
    rw [ht]
    exact satisfies_pairStepFormula (∅ : ZFSet.{u}) S T
  · intro S hS
    exact insert_mem hV hpair hUnion hempty (binaryUnion_mem hV hpair hUnion hS
      (F2_mem hV N hmem hCol hSep hpair hUnion hS hS))

theorem listCodes_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (U : LCarrier.{u}) (hU : U.val ∈ V) :
    listCodes U.val ∈ V := by
  rw [← internalListCodes_eq U]
  apply InternalIteration.uniformUnion_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    listStepFormula ![U, emptyLCarrier] (by intro i; fin_cases i; exact hU; exact hempty)
    (listStep U.val) ?_ (listStepL U) (fun _ => rfl) (listStep_defines U) ?_ emptyLCarrier hempty
  · intro S T
    have ht : snoc (snoc (fun i => (![U, emptyLCarrier] i : LCarrier.{u}).val) S) T =
        ![U.val, ∅, S, T] := by funext i; fin_cases i <;> rfl
    rw [ht]
    exact satisfies_listStepFormula U.val (∅ : ZFSet.{u}) S T
  · intro S hS
    exact insert_mem hV hpair hUnion hempty (F2_mem hV N hmem hCol hSep hpair hUnion hU hS)

end OneYTruth.InternalCodeUniverse

#print axioms OneYTruth.InternalCodeUniverse.codeUniverse_mem
#print axioms OneYTruth.InternalCodeUniverse.listCodes_mem
