import OneYTruth.ConstructibleAssignmentLookup
import OneYTruth.AssignmentCertificate

/-! # Internal lookup existence and its complete Sigma-one candidate check

The lookup bound is the actual assignment/omega/domain product. The
bounded lookup grammar's complete union is identified with all genuine
assignment-index-value records before internal existence is asserted.
-/

namespace OneYTruth.AssignmentLookup

open Constructible Constructible.Delta0Formula Constructible.Model
open Constructible.FiniteSequenceZF InternalNodes InternalProducts InternalClosure
open InternalBoundedIteration

universe u v

theorem allStages_eq_lookupSet (U : LCarrier.{u}) :
    (parametricUniformOmegaUnion (lookupFamily U)).val = lookupSet U.val := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨m, hm⟩ := (mem_parametricUniformOmegaUnion_iff (lookupFamily U)
      ⟨z, mem_L_of_mem hz (parametricUniformOmegaUnion (lookupFamily U)).property⟩).mp hz
    exact lookupStages_sound U m hm
  · intro hz
    obtain ⟨⟨n, xs, i⟩, rfl⟩ := ZFSet.mem_range.mp hz
    have h := lookupStages_complete U n xs i
    exact (mem_parametricUniformOmegaUnion_iff (lookupFamily U)
      ⟨_, mem_L_of_mem h (lookupStages U n).property⟩).mpr ⟨n, h⟩

theorem union_eq_lookupSet (U : LCarrier.{u}) :
    ZFSet.sUnion (InternalIteration.family (step lookupFormula 0 (fun i => (lookupParams U i).val)) ∅) =
      lookupSet U.val :=
  (InternalBoundedIteration.union_eq_L lookupFormula 0 (lookupParams U) emptyLCarrier).trans
    (allStages_eq_lookupSet U)

theorem lookupSet_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (U : LCarrier.{u}) (hU : U.val ∈ V) :
    lookupSet U.val ∈ V := by
  have hA := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  have hp {A B : ZFSet.{u}} (ha : A ∈ V) (hb : B ∈ V) : pairProduct A B ∈ V :=
    pairProduct_mem hV N hmem (hRep 1 (pairFormula k I))
      (hRep 1 (mixedSliceGraphFormula k I)) hpair hUnion ha hb
  have hB : lookupBound U.val ∈ V := hp hA (hp hOmega hU)
  rw [← allStages_eq_lookupSet U]
  apply InternalBoundedIteration.allStages_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    lookupFormula 0 (lookupParams U) _ emptyLCarrier hempty
  intro i
  fin_cases i
  · exact hB
  · exact hA
  · exact hOmega
  · exact hU

theorem lookupSet_mem_LStageZF {k : Nat} {I : Type v} {θ : Ordinal.{u}}
    (hθ : Order.IsSuccLimit θ) (hωθ : Ordinal.omega0 < θ)
    (N : Interpretation k I (ZFCarrier (LStageZF θ))) (hmem : N.mem = zfCarrierMem (LStageZF θ))
    (hCol : HasCollection N) (hSep : HasSeparation N) {U : ZFSet.{u}} (hU : U ∈ LStageZF θ) :
    lookupSet U ∈ LStageZF θ :=
  lookupSet_mem (LStageZF_isTransitive θ) N hmem hCol hSep
    (fun _ ha _ hb => orderedPair_mem_LStageZF_of_isSuccLimit hθ ha hb)
    (fun _ ha => sUnion_mem_LStageZF_of_isSuccLimit hθ ha)
    (by simpa [natCode] using natCode_mem_LStageZF_of_isSuccLimit hθ 0)
    (ordinal_toZFSet_mem_LStageZF_of_lt hωθ) ⟨U, mem_L_of_mem hU (LStageZF_mem_L θ)⟩ hU

/-- Bound, assignments, omega, domain, zero, candidate lookup graph. -/
def lookupQuery (k : Nat) (I : Type v) :=
  grammarQueryAt k I lookupFormula 0 ![0, 1, 2, 3] 4 2 4 (5 : Fin 6)

theorem lookupQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (lookupQuery k I) :=
  grammarQueryAt_isSigmaOne k I _ _ _ _ _ _ _

theorem lookupQuery_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (U : LCarrier.{u}) (s : Fin 6 → ZFCarrier V)
    (hB : (s 0).val = lookupBound U.val) (hA : (s 1).val = assignmentCodes U.val)
    (hOmega : (s 2).val = Ordinal.omega0.toZFSet) (hU : (s 3).val = U.val) (hZero : (s 4).val = ∅)
    (h : OneYTruth.realize N (lookupQuery k I) Empty.elim s) : (s 5).val = lookupSet U.val := by
  have hh := grammarQueryAt_sound hV N hmem lookupFormula 0 ![0, 1, 2, 3]
    4 2 4 (5 : Fin 6) s hOmega hZero h
  have hp : (fun i : Fin 4 => (s (![0, 1, 2, 3] i)).val) = fun i => (lookupParams U i).val := by
    funext i
    fin_cases i
    · exact hB
    · exact hA
    · exact hOmega
    · exact hU
  rwa [hp, hZero, union_eq_lookupSet] at hh

theorem realize_lookupQuery_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (U : LCarrier.{u}) (s : Fin 6 → ZFCarrier V)
    (hB : (s 0).val = lookupBound U.val) (hA : (s 1).val = assignmentCodes U.val)
    (hOmega : (s 2).val = Ordinal.omega0.toZFSet) (hU : (s 3).val = U.val)
    (hZero : (s 4).val = ∅) :
    OneYTruth.realize N (lookupQuery k I) Empty.elim s ↔ (s 5).val = lookupSet U.val := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    lookupFormula 0 ![0, 1, 2, 3] 4 2 4 (5 : Fin 6) s hOmega hZero
  have hp : (fun i : Fin 4 => (s (![0, 1, 2, 3] i)).val) = fun i => (lookupParams U i).val := by
    funext i
    fin_cases i
    · exact hB
    · exact hA
    · exact hOmega
    · exact hU
  rw [hp, hZero, union_eq_lookupSet] at hh
  exact hh

end OneYTruth.AssignmentLookup

#print axioms OneYTruth.AssignmentLookup.lookupSet_mem_LStageZF
#print axioms OneYTruth.AssignmentLookup.realize_lookupQuery_iff
#print axioms OneYTruth.AssignmentLookup.lookupQuery_isSigmaOne
#print axioms OneYTruth.AssignmentLookup.lookupQuery_sound
