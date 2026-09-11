/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteTupleAbsolute

/-!
# Bounded formulas for standard finite ordinals

This file provides the natural-number literals needed by the textbook
enumeration of definable relations.  The literal for zero says that its
designated coordinate has no members.  Recursively, the literal for `k + 1`
chooses, bounded by that coordinate, a predecessor satisfying the literal for
`k` and asserts that the coordinate is its von Neumann successor.

Consequently every quantifier is bounded.  These formulas do not define
addition or multiplication, and their semantics refers to the standard
von Neumann codes `natCode k`.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

namespace Delta0Formula

/-- `emptyDeltaAt i` says that coordinate `i` has no members. -/
def emptyDeltaAt {n : Nat} (i : Fin n) : Delta0Formula n :=
  .boundedAll i (.neg (.eq (Fin.last n) (Fin.last n)))

/-- Ambient semantics of the bounded empty-set formula. -/
@[simp]
theorem satisfies_emptyDeltaAt {n : Nat} (i : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (emptyDeltaAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  simp only [emptyDeltaAt, satisfies_boundedAll, Satisfies,
    snoc_last]
  constructor
  · intro h
    apply ZFSet.eq_empty _ |>.mpr
    intro x hx
    exact h x hx True.intro
  · intro hzero x hx _htrue
    rw [hzero] at hx
    exact ZFSet.notMem_empty x hx

/--
The bounded formula saying that coordinate `i` is the standard von Neumann
ordinal `k`.  In the successor clause the predecessor witness is bounded by
the proposed successor itself.
-/
def natLiteralDeltaAt : (k : Nat) -> {n : Nat} ->
    Fin n -> Delta0Formula n
  | 0, _, i => emptyDeltaAt i
  | k + 1, n, i =>
      .boundedEx i
        (.conj
          (natLiteralDeltaAt k (Fin.last n))
          (successorAt i.castSucc (Fin.last n)))

/-- Ambient semantics of a bounded standard-natural-number literal. -/
@[simp]
theorem satisfies_natLiteralDeltaAt (k : Nat) {n : Nat} (i : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (natLiteralDeltaAt k i) s <->
      s i = (natCode k : ZFSet.{u}) := by
  induction k generalizing n with
  | zero =>
      rw [natLiteralDeltaAt, satisfies_emptyDeltaAt]
      simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
  | succ k ih =>
      simp only [natLiteralDeltaAt, Satisfies, ih,
        satisfies_successorAt, snoc_last, snoc_castSucc]
      constructor
      · rintro ⟨x, _hx, rfl, hsuccessor⟩
        exact hsuccessor.trans (natCode_succ_eq_insert k).symm
      · intro hsuccessor
        refine ⟨(natCode k : ZFSet.{u}), ?_, rfl, ?_⟩
        · rw [hsuccessor, natCode_succ_eq_insert]
          exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
        · exact hsuccessor.trans (natCode_succ_eq_insert k)

/-- Ambient first-order semantics after forgetting boundedness annotations. -/
@[simp]
theorem satisfies_natLiteralDeltaAt_toFO (k : Nat) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies ZFMem (natLiteralDeltaAt k i).toFO s <->
      s i = (natCode k : ZFSet.{u}) := by
  rw [satisfies_toFO, satisfies_natLiteralDeltaAt]

end Delta0Formula

namespace Model

noncomputable section

/-- Every standard natural-number code belongs to a transitive ZF model. -/
theorem natCode_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (k : Nat) :
    (natCode k : ZFSet.{u}) ∈ M := by
  simpa only [natCode] using
    natOrdinal_mem_of_isTransitiveZFModel hM k

/--
Restricted satisfaction over any transitive set has exactly the same
standard-literal semantics, provided every free coordinate lies in the set.
-/
theorem satisfiesIn_natLiteralDeltaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) (k : Nat)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt k i).toFO s <->
      s i = (natCode k : ZFSet.{u}) := by
  rw [satisfiesIn_delta0_iff hM
      (Delta0Formula.natLiteralDeltaAt k i) s hs,
    Delta0Formula.satisfies_natLiteralDeltaAt_toFO]

end

end Model

end Constructible
