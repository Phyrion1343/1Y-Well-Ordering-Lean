/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepOperationsLCarrier

/-!
# The five textbook E branches over L

This file assembles the exact `LCarrier` operation semantics into the five
constructor clauses of the textbook recursion for `E`, followed by its exact
fallback clause.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Atomic branches -/

@[simp]
theorem satisfies_stepBranchZero_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchZero
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n ∧
        output.1 = textbookDInCodeZF a.1
          (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchZero]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hassign (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 0 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        0 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 0 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        0 true a key history output m n i j).mp hguard
    have hvalue : output.1 = textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfies_formula5At_lCarrier] at houtput
      simpa only [textbookDInCodeZF_natCode] using
        (satisfies_dInOutputFormula_lCarrier_natCode_iff
          n i j a output).mp houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 0, ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        0 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfies_formula5At_lCarrier]
      apply (satisfies_dInOutputFormula_lCarrier_natCode_iff
        n i j a output).mpr
      simpa only [textbookDInCodeZF_natCode] using houtput

@[simp]
theorem satisfies_stepBranchOne_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchOne
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n ∧
        output.1 = textbookDEqCodeZF a.1
          (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchOne]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hassign (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 1 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        1 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 1 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        1 true a key history output m n i j).mp hguard
    have hvalue : output.1 = textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfies_formula5At_lCarrier] at houtput
      simpa only [textbookDEqCodeZF_natCode] using
        (satisfies_dEqOutputFormula_lCarrier_natCode_iff
          n i j a output).mp houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 1, ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        1 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfies_formula5At_lCarrier]
      apply (satisfies_dEqOutputFormula_lCarrier_natCode_iff
        n i j a output).mpr
      simpa only [textbookDEqCodeZF_natCode] using houtput

/-! ## Relative-complement branch -/

@[simp]
theorem satisfies_stepBranchTwo_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchTwo
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 2 ∧
        output.1 = relativeDifferenceZF
          (ZFSet.funs (natCode n) a.1)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n))) := by
  rw [TextbookEFormula.stepBranchTwo]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet lookupKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] lookupKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hremovedAssignment
      (iSet jSet tagSet lookupKey removed : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey] removed =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed] := by
    funext k
    fin_cases k <;> rfl
  have hspaceAssignment
      (iSet jSet tagSet lookupKey removed space : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed] space =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed, space] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, lookupKey, hpair,
      removed, hlookup, space, hspace, hdifference⟩
    rw [hfields] at hguard hpair hlookup hspace hdifference
    rw [hkeyAssignment] at hpair hlookup hspace hdifference
    rw [hremovedAssignment] at hlookup hspace hdifference
    rw [hspaceAssignment] at hspace hdifference
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 2 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        2 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 2 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        2 false a key history output m n i j).mp hguard
    have hlookupKey : lookupKey.1 =
        ZFSet.pair (natCode i) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hpair
      simpa using hpair
    have hremoved : removed.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hlookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history lookupKey removed).mp hlookup
      simpa only [hlookupKey] using hvalue
    have hspaceValue : space.1 = ZFSet.funs (natCode n) a.1 := by
      rw [satisfies_formula3At_lCarrier] at hspace
      exact (satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
        n a space).mp hspace
    have hvalue : output.1 =
        relativeDifferenceZF (ZFSet.funs (natCode n) a.1)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n))) := by
      rw [satisfies_formula3At_lCarrier] at hdifference
      have hraw :=
        (satisfies_relativeDifferenceOutputFormula_lCarrier
          space removed output).mp hdifference
      simpa only [hspaceValue, hremoved] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let lookupKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) (natCode n),
        orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n)⟩
    let removed : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 lookupKey.1,
        uniqueGraphLookupZF_mem_L history.2 lookupKey.2⟩
    let space : LCarrier.{u} :=
      ⟨ZFSet.funs (natCode n) a.1, by
        change textbookTupleSpace a.1 n ∈ L
        exact textbookTupleSpace_mem_L a.2 n⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 2,
      ?_, lookupKey, ?_, removed, ?_, space, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        2 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hkeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change lookupKey.1 = ZFSet.pair (natCode i) (natCode n)
      rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history lookupKey removed).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfies_formula3At_lCarrier]
      exact (satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
        n a space).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfies_formula3At_lCarrier]
      apply (satisfies_relativeDifferenceOutputFormula_lCarrier
        space removed output).mpr
      simpa only [space, removed, lookupKey] using houtput

/-! ## Intersection branch -/

@[simp]
theorem satisfies_stepBranchThree_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchThree
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 3 ∧
        output.1 = intersectionZF
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n)))
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode j) (natCode n))) := by
  rw [TextbookEFormula.stepBranchThree]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hleftKeyAssignment
      (iSet jSet tagSet leftKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] leftKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey] := by
    funext k
    fin_cases k <;> rfl
  have hleftValueAssignment
      (iSet jSet tagSet leftKey leftValue : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey] leftValue =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue] := by
    funext k
    fin_cases k <;> rfl
  have hrightKeyAssignment
      (iSet jSet tagSet leftKey leftValue rightKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue] rightKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] := by
    funext k
    fin_cases k <;> rfl
  have hrightValueAssignment
      (iSet jSet tagSet leftKey leftValue rightKey rightValue :
        LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] rightValue =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey, rightValue] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, leftKey, hleftPair,
      leftValue, hleftLookup, rightKey, hrightPair,
      rightValue, hrightLookup, hintersection⟩
    rw [hfields] at hguard hleftPair hleftLookup hrightPair hrightLookup
    rw [hfields] at hintersection
    rw [hleftKeyAssignment] at hleftPair hleftLookup hrightPair hrightLookup
    rw [hleftKeyAssignment] at hintersection
    rw [hleftValueAssignment] at hleftLookup hrightPair hrightLookup
    rw [hleftValueAssignment] at hintersection
    rw [hrightKeyAssignment] at hrightPair hrightLookup hintersection
    rw [hrightValueAssignment] at hrightLookup hintersection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 3 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        3 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 3 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        3 false a key history output m n i j).mp hguard
    have hleftKey : leftKey.1 =
        ZFSet.pair (natCode i) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hleftPair
      simpa using hleftPair
    have hleftValue : leftValue.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hleftLookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history leftKey leftValue).mp hleftLookup
      simpa only [hleftKey] using hvalue
    have hrightKey : rightKey.1 =
        ZFSet.pair (natCode j) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hrightPair
      simpa using hrightPair
    have hrightValue : rightValue.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode j) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hrightLookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history rightKey rightValue).mp hrightLookup
      simpa only [hrightKey] using hvalue
    have hvalue : output.1 = intersectionZF
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)))
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode j) (natCode n))) := by
      rw [satisfies_formula3At_lCarrier] at hintersection
      have hraw :=
        (satisfies_intersectionOutputFormula_lCarrier
          leftValue rightValue output).mp hintersection
      simpa only [hleftValue, hrightValue] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let leftKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) (natCode n),
        orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n)⟩
    let leftValue : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 leftKey.1,
        uniqueGraphLookupZF_mem_L history.2 leftKey.2⟩
    let rightKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode j) (natCode n),
        orderedPair_mem_L (natCode_mem_L j) (natCode_mem_L n)⟩
    let rightValue : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 rightKey.1,
        uniqueGraphLookupZF_mem_L history.2 rightKey.2⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 3,
      ?_, leftKey, ?_, leftValue, ?_, rightKey, ?_, rightValue, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        3 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hleftKeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change leftKey.1 = ZFSet.pair (natCode i) (natCode n)
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history leftKey leftValue).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, satisfies_kuratowskiPairEqAt_lCarrier]
      change rightKey.1 = ZFSet.pair (natCode j) (natCode n)
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history rightKey rightValue).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfies_formula3At_lCarrier]
      apply (satisfies_intersectionOutputFormula_lCarrier
        leftValue rightValue output).mpr
      simpa only [leftValue, leftKey, rightValue, rightKey] using houtput

/-! ## Existential-projection branch -/

@[simp]
theorem satisfies_stepBranchFour_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchFour
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 4 ∧
        output.1 = textbookExistsProjCodeZF a.1 (natCode n)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  rw [TextbookEFormula.stepBranchFour]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hsuccAssignment
      (iSet jSet tagSet succN : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] succN =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet succN lookupKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN] lookupKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hrelationAssignment
      (iSet jSet tagSet succN lookupKey relation : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey] relation =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey, relation] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, succN, hsucc,
      lookupKey, hpair, relation, hlookup, hprojection⟩
    rw [hfields] at hguard hsucc hpair hlookup hprojection
    rw [hsuccAssignment] at hsucc hpair hlookup hprojection
    rw [hkeyAssignment] at hpair hlookup hprojection
    rw [hrelationAssignment] at hlookup hprojection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 4 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        4 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 4 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        4 false a key history output m n i j).mp hguard
    have hsuccN : succN.1 = (natCode (n + 1) : ZFSet.{u}) := by
      rw [satisfies_successorAt_lCarrier] at hsucc
      change succN.1 = insert (natCode n) (natCode n) at hsucc
      exact hsucc.trans (natCode_succ_eq_insert n).symm
    have hlookupKey : lookupKey.1 =
        ZFSet.pair (natCode i) (natCode (n + 1)) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hpair
      change lookupKey.1 = ZFSet.pair (natCode i) succN.1 at hpair
      simpa only [hsuccN] using hpair
    have hrelation : relation.1 = uniqueGraphLookupZF history.1
        (ZFSet.pair (natCode i) (natCode (n + 1))) := by
      rw [satisfies_formula3At_lCarrier] at hlookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history lookupKey relation).mp hlookup
      simpa only [hlookupKey] using hvalue
    have hvalue : output.1 = textbookExistsProjCodeZF a.1 (natCode n)
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
      rw [satisfies_formula4At_lCarrier] at hprojection
      have hraw :=
        (satisfies_existsProjOutputFormula_lCarrier_natCode_iff
          n a relation output).mp hprojection
      simpa only [hrelation] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let succN : LCarrier.{u} :=
      ⟨natCode (n + 1), natCode_mem_L (n + 1)⟩
    let lookupKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) succN.1,
        orderedPair_mem_L (natCode_mem_L i) succN.2⟩
    let relation : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 lookupKey.1,
        uniqueGraphLookupZF_mem_L history.2 lookupKey.2⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 4,
      ?_, succN, ?_, lookupKey, ?_, relation, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        4 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hsuccAssignment, satisfies_successorAt_lCarrier]
      change (natCode (n + 1) : ZFSet.{u}) =
        insert (natCode n) (natCode n)
      exact natCode_succ_eq_insert n
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change lookupKey.1 = ZFSet.pair (natCode i) succN.1
      rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history lookupKey relation).mpr rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfies_formula4At_lCarrier]
      apply (satisfies_existsProjOutputFormula_lCarrier_natCode_iff
        n a relation output).mpr
      simpa only [relation, lookupKey, succN] using houtput

/-! ## Exact combination of the five clauses and fallback -/

@[simp]
theorem satisfies_anyCodeGuard_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.anyCodeGuard
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      TextbookEFormula.TextbookEGuard m n := by
  simp only [TextbookEFormula.anyCodeGuard, FOFormula.satisfies_disj,
    satisfies_codeGuard_lCarrier_standard]
  simp [TextbookEFormula.TextbookEGuard]

@[simp]
theorem satisfies_stepFallback_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepFallback
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ¬ TextbookEFormula.TextbookEGuard m n ∧
        output.1 = (∅ : ZFSet.{u}) := by
  rw [TextbookEFormula.stepFallback]
  change
    (¬ FOFormula.Satisfies LMem TextbookEFormula.anyCodeGuard
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      FOFormula.Satisfies LMem
          (Delta0Formula.emptyDeltaAt (3 : Fin 7)).toFO
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n]) <-> _
  rw [satisfies_anyCodeGuard_lCarrier_standard,
    satisfies_emptyDeltaAt_lCarrier]
  change
    (¬ TextbookEFormula.TextbookEGuard m n ∧
      output.1 = (∅ : ZFSet.{u})) <-> _
  rfl

@[simp]
theorem satisfies_stepBranches_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (.disj TextbookEFormula.stepBranchZero <|
          .disj TextbookEFormula.stepBranchOne <|
          .disj TextbookEFormula.stepBranchTwo <|
          .disj TextbookEFormula.stepBranchThree <|
          .disj TextbookEFormula.stepBranchFour
            TextbookEFormula.stepFallback)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      TextbookEFormula.TextbookEBranchResult
        a.1 history.1 output.1 m n := by
  simp only [FOFormula.satisfies_disj,
    satisfies_stepBranchZero_lCarrier_standard,
    satisfies_stepBranchOne_lCarrier_standard,
    satisfies_stepBranchTwo_lCarrier_standard,
    satisfies_stepBranchThree_lCarrier_standard,
    satisfies_stepBranchFour_lCarrier_standard,
    satisfies_stepFallback_lCarrier_standard]
  rfl

/-! ## Exact one-step graph semantics -/

@[simp]
theorem satisfies_textbookEStepBody_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEStepBody
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      key.1 = ZFSet.pair (natCode m) (natCode n) ∧
        output.1 = textbookEStep a.1
          (ZFSet.pair (natCode m) (natCode n)) history.1 := by
  rw [TextbookEFormula.textbookEStepBody]
  change
    (FOFormula.Satisfies LMem
          (Model.standardOmegaAt (4 : Fin 7))
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier m) omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier n) omegaLCarrier ∧
      FOFormula.Satisfies LMem
          (Delta0Formula.kuratowskiPairEqAt
            (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      FOFormula.Satisfies LMem
          (.disj TextbookEFormula.stepBranchZero <|
            .disj TextbookEFormula.stepBranchOne <|
            .disj TextbookEFormula.stepBranchTwo <|
            .disj TextbookEFormula.stepBranchThree <|
            .disj TextbookEFormula.stepBranchFour
              TextbookEFormula.stepFallback)
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n]) <-> _
  rw [satisfies_standardOmegaAt_lCarrier,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_stepBranches_lCarrier_standard]
  change
    (omegaLCarrier = omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier m) omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier n) omegaLCarrier ∧
      key.1 = ZFSet.pair (natCode m) (natCode n) ∧
      TextbookEFormula.TextbookEBranchResult
        a.1 history.1 output.1 m n) <-> _
  rw [TextbookEFormula.textbookEBranchResult_iff_step]
  simp only [lmem_textbookNatCode_omegaLCarrier, true_and]

/-- Exact graph semantics of the textbook one-step operation over `L`.  The
domain conjunct is explicit, so the formula is false off `omega × omega`. -/
@[simp]
theorem satisfies_textbookEStepFormula_lCarrier_iff
    (a key history output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEStepFormula
        ![a, key, history, output] <->
      key.1 ∈ TextbookEDomain ∧
        output.1 = textbookEStep a.1 key.1 history.1 := by
  rw [TextbookEFormula.textbookEStepFormula]
  simp only [FOFormula.Satisfies]
  have hassign (omega mSet nSet : LCarrier.{u}) :
      snoc (snoc (snoc ![a, key, history, output] omega) mSet) nSet =
        ![a, key, history, output, omega, mSet, nSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨omega, mSet, nSet, hbody⟩
    rw [hassign] at hbody
    have homega : omega = omegaLCarrier := by
      have h :=
        (satisfies_standardOmegaAt_lCarrier (4 : Fin 7)
          ![a, key, history, output, omega, mSet, nSet]).mp hbody.1
      change omega = omegaLCarrier at h
      exact h
    subst omega
    have hmOmega : mSet.1 ∈
        (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.2.1
    have hnOmega : nSet.1 ∈
        (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.2.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode mSet.1).mp
      hmOmega with ⟨m, hm⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nSet.1).mp
      hnOmega with ⟨n, hn⟩
    have hmSet : mSet =
        TextbookNatFormula.textbookNatCodeLCarrier m := Subtype.ext hm
    have hnSet : nSet =
        TextbookNatFormula.textbookNatCodeLCarrier n := Subtype.ext hn
    subst mSet
    subst nSet
    have hstandard :=
      (satisfies_textbookEStepBody_lCarrier_standard
        a key history output m n).mp hbody
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨natCode m,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩,
        natCode n,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩,
        hstandard.1⟩
    · simpa only [hstandard.1] using hstandard.2
  · rintro ⟨hkeyDomain, houtput⟩
    rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
      ⟨m, n, _hdecode, hkey⟩
    refine ⟨omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n, ?_⟩
    rw [hassign]
    apply (satisfies_textbookEStepBody_lCarrier_standard
      a key history output m n).mpr
    exact ⟨hkey, by simpa only [hkey] using houtput⟩

end

end Model

end Constructible
