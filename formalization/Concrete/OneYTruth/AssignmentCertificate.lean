import OneYTruth.AssignmentGrammar
import OneYTruth.BoundedGrammarSoundness

/-! # A genuine Sigma-one check for the complete assignment-code set

The five parameters are the verified code universe, the actual domain,
omega, zero, and a candidate assignment-code set. The candidate is not
accepted merely because its elements look like codes: the full grammar
history and both directions of its complete range are certified.
-/

namespace OneYTruth.AssignmentGrammar

open Constructible Constructible.Model Constructible.Delta0Formula
open ConstructibleAssignmentCodes InternalNodes InternalClosure
open InternalBoundedIteration ConstructibleCodeUniverse

universe u v

theorem union_eq_assignmentCodes (U : LCarrier.{u}) :
    ZFSet.sUnion (InternalIteration.family (step ruleFormula 0 (fun i => (params U i).val)) ∅) =
      assignmentCodes U.val := by
  have h := InternalBoundedIteration.union_eq_L ruleFormula 0 (params U) emptyLCarrier
  exact h.trans ((allStages_eq_sequenceCodes U).trans (assignmentCodes_eq_sequenceCodes U.val).symm)

def assignmentQuery (k : Nat) (I : Type v) :=
  grammarQueryAt k I ruleFormula 0 ![0, 1, 2, 3] 3 2 3 (4 : Fin 5)

theorem assignmentQuery_isSigmaOne (k : Nat) (I : Type v) : IsSigmaOne (assignmentQuery k I) :=
  grammarQueryAt_isSigmaOne k I _ _ _ _ _ _ _

theorem assignmentQuery_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (U : LCarrier.{u}) (s : Fin 5 → ZFCarrier V)
    (hB : (s 0).val = (codeUniverse U).val) (hU : (s 1).val = U.val)
    (hOmega : (s 2).val = Ordinal.omega0.toZFSet) (hZero : (s 3).val = ∅)
    (h : OneYTruth.realize N (assignmentQuery k I) Empty.elim s) :
    (s 4).val = assignmentCodes U.val := by
  have hh := grammarQueryAt_sound hV N hmem ruleFormula 0 ![0, 1, 2, 3]
    3 2 3 (4 : Fin 5) s hOmega hZero h
  have hp : (fun i : Fin 4 => (s (![0, 1, 2, 3] i)).val) = fun i => (params U i).val := by
    funext i
    fin_cases i
    · exact hB
    · exact hU
    · exact hOmega
    · exact hZero
  rwa [hp, hZero, union_eq_assignmentCodes] at hh

theorem realize_assignmentQuery_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (U : LCarrier.{u}) (s : Fin 5 → ZFCarrier V)
    (hB : (s 0).val = (codeUniverse U).val) (hU : (s 1).val = U.val)
    (hOmega : (s 2).val = Ordinal.omega0.toZFSet) (hZero : (s 3).val = ∅) :
    OneYTruth.realize N (assignmentQuery k I) Empty.elim s ↔ (s 4).val = assignmentCodes U.val := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    ruleFormula 0 ![0, 1, 2, 3] 3 2 3 (4 : Fin 5) s hOmega hZero
  have hp : (fun i : Fin 4 => (s (![0, 1, 2, 3] i)).val) = fun i => (params U i).val := by
    funext i
    fin_cases i
    · exact hB
    · exact hU
    · exact hOmega
    · exact hZero
  rw [hp, hZero, union_eq_assignmentCodes] at hh
  exact hh

end OneYTruth.AssignmentGrammar

#print axioms OneYTruth.AssignmentGrammar.realize_assignmentQuery_iff
#print axioms OneYTruth.AssignmentGrammar.assignmentQuery_isSigmaOne
#print axioms OneYTruth.AssignmentGrammar.assignmentQuery_sound
