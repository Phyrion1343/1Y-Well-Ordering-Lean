/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistory

/-!
# Finite canonical-history bounds

The canonical history through a finite ordinal is hereditarily finite.  This
is the base input needed when the first infinite limit is treated separately:
the evaluator prefix contains `omega`, so that full prefix cannot be used as
parameters over `L_omega` itself.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-! ## Finite constructible levels -/

/-- Every finite constructible level is itself an element of `L_omega`.
This is genuine internal membership, not only inclusion in `L_omega`. -/
theorem LStageZF_natCast_mem_LStageZF_omega (n : Nat) :
    LStageZF (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  LStageZF_mem_LStageZF_of_lt_isSuccLimit
    Ordinal.isSuccLimit_omega0 (Ordinal.natCast_lt_omega0 n)

/-- The actual Goedel-definability output of a finite level is again an
element of `L_omega`; extensionally it is the next finite level. -/
theorem godelDef_LStageZF_natCast_mem_LStageZF_omega (n : Nat) :
    Godel.godelDef (LStageZF (n : Ordinal.{u})) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rw [← Godel.DefZF_eq_godelDef
      (LStageZF_isTransitive (n : Ordinal.{u})),
    ← LStageZF_succ]
  apply LStageZF_mem_LStageZF_of_lt_isSuccLimit
    Ordinal.isSuccLimit_omega0
  exact Ordinal.isSuccLimit_omega0.succ_lt
    (Ordinal.natCast_lt_omega0 n)

/-- Consequently, every member of the finite-level Goedel output is already
available inside `L_omega`. -/
theorem godelDef_LStageZF_natCast_subset_LStageZF_omega (n : Nat) :
    Godel.godelDef (LStageZF (n : Ordinal.{u})) ⊆
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  (LStageZF_isTransitive (Ordinal.omega0 : Ordinal.{u})).subset_of_mem
    (godelDef_LStageZF_natCast_mem_LStageZF_omega n)

/-- The empty canonical history already belongs to `L_omega`. -/
theorem canonicalBareHistory_zero_mem_LStageZF_omega :
    canonicalBareHistory (0 : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rw [canonicalBareHistory_eq_insert_top]
  have hbelow :
      canonicalBareHistoryBelow (0 : Ordinal.{u}) = (∅ : ZFSet.{u}) := by
    apply ZFSet.ext
    intro entry
    constructor
    · intro hentry
      rcases mem_canonicalBareHistoryBelow_iff.mp hentry with
        ⟨ordinal, hordinal, _hentry⟩
      exact (not_lt_of_ge bot_le hordinal).elim
    · intro hentry
      exact (ZFSet.notMem_empty entry hentry).elim
  rw [hbelow]
  apply insert_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
  · exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      Ordinal.isSuccLimit_omega0 (Ordinal.natCast_lt_omega0 0)
  · exact empty_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0

/-- Every finite canonical history is an element of `L_omega`, not merely a
subset of that level. -/
theorem canonicalBareHistory_natCast_mem_LStageZF_omega (n : Nat) :
    canonicalBareHistory (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  induction n with
  | zero => simpa using canonicalBareHistory_zero_mem_LStageZF_omega
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one,
        canonicalBareHistory_succ]
      apply insert_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
      · exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
          Ordinal.isSuccLimit_omega0
          (Ordinal.natCast_lt_omega0 (n + 1))
      · exact ih

/-- Every canonical history indexed strictly below `omega` belongs to
`L_omega`. -/
theorem canonicalBareHistory_mem_LStageZF_omega_of_lt_omega
    {ordinal : Ordinal.{u}} (hordinal : ordinal < Ordinal.omega0) :
    canonicalBareHistory ordinal ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rcases Ordinal.lt_omega0.mp hordinal with ⟨n, rfl⟩
  exact canonicalBareHistory_natCast_mem_LStageZF_omega n

end

end Constructible.Model
