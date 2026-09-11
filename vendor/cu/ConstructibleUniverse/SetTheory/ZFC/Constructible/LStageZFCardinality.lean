/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefZFCardinality
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals

/-!
# Cardinality of the constructible hierarchy

This file formalizes Proposition 1(II) of Section 6.8 of Wang Fangting,
*Axiomatic Set Theory*.  For every ordinal `alpha`,

`card (LStageZF alpha) <= max aleph0 alpha.card`.

The proof follows the hierarchy recursion.  The successor case uses the
formula-and-parameter enumeration bound for `DefZF`.  In the limit case the
actual internally represented `limitUnionZF` is identified with a
`ZFSet.iUnion` indexed by the ordinals below the limit, and its cardinality is
estimated directly by `ZFSet.lift_card_iUnion_le_sum_card`.

Finally, `alpha.toZFSet` is contained in `LStageZF alpha`.  Since its
cardinality is `alpha.card`, the upper bound is an equality whenever `alpha`
is infinite.
-/

@[expose] public section

open Set
open scoped Cardinal

universe u

namespace Constructible

noncomputable section

/-- The replacement-based limit construction is extensionally the actual
`ZFSet.iUnion` of the preceding stages. -/
theorem limitUnionZF_eq_iUnion (l : Ordinal.{u})
    (Xs : (beta : Ordinal.{u}) -> beta < l -> ZFSet.{u}) :
    limitUnionZF l Xs =
      ZFSet.iUnion (fun beta : Set.Iio l => Xs beta.1 beta.2) := by
  ext x
  rw [mem_limitUnionZF_iff, ZFSet.mem_iUnion]
  constructor
  · rintro ⟨beta, hbeta, hx⟩
    exact ⟨⟨beta, hbeta⟩, hx⟩
  · rintro ⟨beta, hx⟩
    exact ⟨beta.1, beta.2, hx⟩

/-- Every level of the constructible hierarchy has cardinality bounded by
the maximum of `aleph0` and the cardinality of its ordinal index. -/
theorem card_LStageZF_le_max (alpha : Ordinal.{u}) :
    ZFSet.card (LStageZF alpha) ≤
      max Cardinal.aleph0 alpha.card := by
  induction alpha using Ordinal.limitRecOn with
  | zero =>
      simp only [LStageZF_zero, ZFSet.card_empty]
      exact bot_le
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one, LStageZF_succ]
      apply (card_DefZF_le_max (LStageZF alpha)).trans
      apply max_le
      · exact le_max_left _ _
      · exact ih.trans
          (max_le_max le_rfl
            (Ordinal.card_le_card (Order.le_succ alpha)))
  | limit l hl ih =>
      rw [LStageZF_limit hl, limitUnionZF_eq_iUnion]
      let kappa : Cardinal.{u} := max Cardinal.aleph0 l.card
      have hkappa : Cardinal.aleph0 ≤ kappa := le_max_left _ _
      refine Cardinal.lift_le.{u + 1, u}.mp ?_
      show Cardinal.lift.{u + 1, u}
          (ZFSet.card (ZFSet.iUnion
            (fun beta : Set.Iio l => LStageZF beta.1))) ≤
        Cardinal.lift.{u + 1, u} kappa
      calc
        Cardinal.lift.{u + 1, u}
            (ZFSet.card (ZFSet.iUnion
              (fun beta : Set.Iio l => LStageZF beta.1)))
            ≤ Cardinal.sum (fun beta : Set.Iio l =>
                ZFSet.card (LStageZF beta.1)) :=
          ZFSet.lift_card_iUnion_le_sum_card
        _ ≤ Cardinal.sum (fun _ : Set.Iio l => kappa) :=
          Cardinal.sum_le_sum _ _ fun beta =>
            (ih beta.1 beta.2).trans
              (max_le_max le_rfl
                (Ordinal.card_le_card beta.2.le))
        _ = Cardinal.lift.{u + 1, u} l.card *
            Cardinal.lift.{u + 1, u} kappa := by
          rw [Cardinal.sum_const, Cardinal.mk_Iio_ordinal]
          simp only [Cardinal.lift_lift]
        _ ≤ Cardinal.lift.{u + 1, u} kappa :=
          Cardinal.mul_le_of_le
            (Cardinal.aleph0_le_lift.mpr hkappa)
            (Cardinal.lift_monotone (le_max_right _ _)) le_rfl

/-- The von Neumann code of an ordinal gives the converse cardinal bound. -/
theorem card_ordinal_le_card_LStageZF (alpha : Ordinal.{u}) :
    alpha.card ≤ ZFSet.card (LStageZF alpha) := by
  rw [← Ordinal.card_toZFSet alpha]
  exact ZFSet.card_mono (ordinal_stage_invariants alpha).2

/-- For every infinite ordinal, its constructible level has exactly the same
cardinality.  This is Proposition 1(II) in its standard infinite form. -/
theorem card_LStageZF_eq_of_aleph0_le (alpha : Ordinal.{u})
    (halpha : Cardinal.aleph0 ≤ alpha.card) :
    ZFSet.card (LStageZF alpha) = alpha.card := by
  apply le_antisymm
  · exact (card_LStageZF_le_max alpha).trans_eq (max_eq_right halpha)
  · exact card_ordinal_le_card_LStageZF alpha

end

end Constructible
