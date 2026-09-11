/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals

/-!
# An abstract core for constructible condensation

This file isolates the final order-theoretic step of a condensation argument.
For a transitive set `M`, `ordinalHeight M` is the supremum of the successors
of the ranks of the ordinal members of `M`.  Consequently, the ordinals in
`M` are exactly the von Neumann codes below this height.

The final theorem identifies `M` with the constructible level at its ordinal
height, under three explicit closure hypotheses:

* ordinal successors of members remain in `M`;
* every member of `M` occurs in a constructible level indexed by an ordinal
  belonging to `M`;
* every constructible level indexed by an ordinal belonging to `M` is itself
  an element of `M`.

These hypotheses are the interface that a later Skolem-hull and Mostowski
collapse development must establish.  No elementarity or collapse theorem is
asserted in this file.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/--
The ordinal height of a set is the supremum of the successor ranks of its
ordinal members.  The zero contribution from non-ordinal members lets us use
the small type `ZFCarrier M` directly as the indexing type.
-/
noncomputable def ordinalHeight (M : ZFSet.{u}) : Ordinal.{u} :=
  by
    classical
    exact iSup fun x : ZFCarrier M =>
      if x.1.IsOrdinal then Order.succ x.1.rank else 0

/-- Every ordinal member of `M` has index below `ordinalHeight M`. -/
theorem lt_ordinalHeight_of_mem {M : ZFSet.{u}} {alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ M) :
    alpha < ordinalHeight M := by
  classical
  let x : ZFCarrier M := ⟨alpha.toZFSet, halpha⟩
  have hx := Ordinal.le_iSup
    (fun y : ZFCarrier M =>
      if y.1.IsOrdinal then Order.succ y.1.rank else 0) x
  have hsucc : Order.succ alpha ≤ ordinalHeight M := by
    simpa [ordinalHeight, x, ZFSet.isOrdinal_toZFSet] using hx
  exact (Order.lt_succ alpha).trans_le hsucc

/--
For a transitive `M`, every index below its ordinal height is represented by
an ordinal member of `M`.
-/
theorem ordinal_toZFSet_mem_of_lt_ordinalHeight {M : ZFSet.{u}}
    (htrans : M.IsTransitive) {alpha : Ordinal.{u}}
    (halpha : alpha < ordinalHeight M) :
    alpha.toZFSet ∈ M := by
  classical
  rw [ordinalHeight, Ordinal.lt_iSup_iff] at halpha
  rcases halpha with ⟨x, hx⟩
  by_cases hord : x.1.IsOrdinal
  · simp only [if_pos hord] at hx
    have hle : alpha ≤ x.1.rank := Order.lt_succ_iff.mp hx
    rcases hle.eq_or_lt with heq | hlt
    · have hcode : alpha.toZFSet = x.1 := by
        rw [heq, hord.toZFSet_rank_eq]
      simpa only [hcode] using x.2
    · have hmem : alpha.toZFSet ∈ x.1 := by
        rw [← hord.toZFSet_rank_eq]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt
      exact htrans.mem_trans hmem x.2
  · simp only [if_neg hord] at hx
    exact (not_lt_of_ge bot_le hx).elim

/-- In a transitive set, ordinal membership is exactly boundedness by height. -/
theorem ordinal_toZFSet_mem_iff_lt_ordinalHeight {M : ZFSet.{u}}
    (htrans : M.IsTransitive) (alpha : Ordinal.{u}) :
    alpha.toZFSet ∈ M ↔ alpha < ordinalHeight M := by
  constructor
  · exact lt_ordinalHeight_of_mem
  · exact ordinal_toZFSet_mem_of_lt_ordinalHeight htrans

/-- Closure of the ordinal members of `M` under ordinal successor. -/
def OrdinalSuccessorClosed (M : ZFSet.{u}) : Prop :=
  ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ M →
    (Order.succ alpha).toZFSet ∈ M

/--
Every member of `M` occurs in a constructible level whose ordinal index is
itself represented in `M`.
-/
def InternallyStageCovered (M : ZFSet.{u}) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ M →
    ∃ alpha : Ordinal.{u}, alpha.toZFSet ∈ M ∧ x ∈ LStageZF alpha

/-- `M` contains every constructible level indexed by one of its ordinals. -/
def ContainsInternalLStages (M : ZFSet.{u}) : Prop :=
  ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ M → LStageZF alpha ∈ M

/--
Successor closure makes every nonzero ordinal height a limit ordinal.  The
zero case is deliberately excluded: it is needed when `M` has no ordinal
members at all.
-/
theorem ordinalHeight_isSuccLimit_of_ne_zero {M : ZFSet.{u}}
    (htrans : M.IsTransitive) (hsucc : OrdinalSuccessorClosed M)
    (hne : ordinalHeight M ≠ 0) :
    Order.IsSuccLimit (ordinalHeight M) := by
  rw [Ordinal.isSuccLimit_iff]
  refine ⟨hne, Order.isSuccPrelimit_of_succ_lt ?_⟩
  intro alpha halpha
  have halphaM : alpha.toZFSet ∈ M :=
    (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mpr halpha
  exact (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans
    (Order.succ alpha)).mp (hsucc alpha halphaM)

/-- Stage coverage gives the easy inclusion `M ⊆ L_(ordinalHeight M)`. -/
theorem subset_LStageZF_ordinalHeight_of_internallyStageCovered
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hcover : InternallyStageCovered M) :
    M ⊆ LStageZF (ordinalHeight M) := by
  intro x hx
  rcases hcover x hx with ⟨alpha, halphaM, hxStage⟩
  exact LStageZF_mono
    ((ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mp
      halphaM).le hxStage

/--
If `M` is successor closed and contains all of its internally indexed
constructible levels, then `L_(ordinalHeight M) ⊆ M`.
-/
theorem LStageZF_ordinalHeight_subset_of_containsInternalLStages
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hsucc : OrdinalSuccessorClosed M)
    (hstages : ContainsInternalLStages M) :
    LStageZF (ordinalHeight M) ⊆ M := by
  intro x hx
  by_cases hzero : ordinalHeight M = 0
  · rw [hzero, LStageZF_zero] at hx
    exact (ZFSet.notMem_empty x hx).elim
  · have hlimit :=
      ordinalHeight_isSuccLimit_of_ne_zero htrans hsucc hzero
    rcases (mem_LStageZF_limit_iff hlimit).mp hx with
      ⟨alpha, halpha, hxStage⟩
    have halphaM : alpha.toZFSet ∈ M :=
      (ordinal_toZFSet_mem_iff_lt_ordinalHeight htrans alpha).mpr halpha
    exact htrans.mem_trans hxStage (hstages alpha halphaM)

/--
Abstract condensation core.  A transitive set satisfying the three explicit
closure conditions above is exactly the constructible level at its ordinal
height.

This is only the last step of condensation.  Applying it to a Mostowski
collapse still requires separate proofs that the collapse satisfies each of
the three hypotheses.
-/
theorem eq_LStageZF_ordinalHeight_of_condensationCore
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hsucc : OrdinalSuccessorClosed M)
    (hcover : InternallyStageCovered M)
    (hstages : ContainsInternalLStages M) :
    M = LStageZF (ordinalHeight M) := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (subset_LStageZF_ordinalHeight_of_internallyStageCovered htrans hcover)
    (LStageZF_ordinalHeight_subset_of_containsInternalLStages
      htrans hsucc hstages)

end ZFC

end Constructible
