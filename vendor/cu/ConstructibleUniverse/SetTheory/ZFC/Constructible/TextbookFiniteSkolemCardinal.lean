/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteSkolemIteration
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal bound for the finite Skolem iteration

This file proves the cardinal estimate for the textbook finite-fragment
Skolem construction.  If `seed` is the initial set, every finite pass, every
natural-number stage, and the final omega union have cardinality at most

`max aleph0 (ZFSet.card seed)`.

The one-formula image is constructed by `ZFSet.range` from an external Lean
function.  Its estimate therefore uses `ZFSet.lift_card_range_le`, through the
already proved theorem `lift_card_textbookFormulaSkolemImage_le`; it does not
use `ZFSet.card_image_le` and does not assert a `Definable₁` instance for the
external Skolem function.

The tuple type lives one universe above `ZFSet.card seed`.  The first proof
below consequently performs the finite-power estimate after lifting to that
universe and descends only after both sides have the same lift.
-/

@[expose] public section

open Set
open scoped Cardinal

universe u

namespace Constructible

noncomputable section

/-- The range of one textbook Skolem function has cardinality at most the
infinite closure of the cardinality of its parameter set. -/
theorem card_textbookFormulaSkolemImage_le_max
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U)
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1)) :
    ZFSet.card (textbookFormulaSkolemImage seed U hseed default phi) ≤
      max Cardinal.aleph0 (ZFSet.card seed) := by
  refine Cardinal.lift_le.{u + 1, u}.mp ?_
  show Cardinal.lift.{u + 1, u} (ZFSet.card
      (textbookFormulaSkolemImage seed U hseed default phi)) ≤
    Cardinal.lift.{u + 1, u}
      (max Cardinal.aleph0 (ZFSet.card seed))
  calc
    Cardinal.lift.{u + 1, u} (ZFSet.card
        (textbookFormulaSkolemImage seed U hseed default phi))
        ≤ Cardinal.lift.{u, u + 1}
            (Cardinal.mk.{u + 1} (Tuple (ZFCarrier seed) n)) :=
      lift_card_textbookFormulaSkolemImage_le hseed default phi
    _ = Cardinal.mk.{u + 1} (Tuple (ZFCarrier seed) n) := by
      rw [Cardinal.lift_id'.{u, u + 1}]
    _ ≤ max (Cardinal.mk.{u + 1} (ZFCarrier seed)) Cardinal.aleph0 := by
      rw [Cardinal.mk_arrow]
      simpa only [Cardinal.lift_id'.{0, u + 1},
        Cardinal.lift_mk_fin] using
        (Cardinal.power_nat_le_max
          (c := Cardinal.mk.{u + 1} (ZFCarrier seed)) (n := n))
    _ = max (Cardinal.lift.{u + 1, u} (ZFSet.card seed))
        Cardinal.aleph0 := by
      rw [ZFSet.cardinalMk_coe_sort]
    _ = Cardinal.lift.{u + 1, u}
        (max Cardinal.aleph0 (ZFSet.card seed)) := by
      simp only [Cardinal.lift_max, Cardinal.lift_aleph0]
      rw [max_comm]

/-- A one-formula step preserves every displayed infinite cardinal bound. -/
theorem card_textbookFormulaSkolemStep_le_of_le
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U)
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    {kappa : Cardinal.{u}} (hkappa : Cardinal.aleph0 ≤ kappa)
    (hcard : ZFSet.card seed ≤ kappa) :
    ZFSet.card (textbookFormulaSkolemStep seed U hseed default phi) ≤
      kappa := by
  calc
    ZFSet.card (textbookFormulaSkolemStep seed U hseed default phi)
        ≤ ZFSet.card seed +
            ZFSet.card (textbookFormulaSkolemImage seed U hseed default phi) :=
      ZFSet.card_union_le
    _ ≤ kappa := Cardinal.add_le_of_le hkappa hcard
      ((card_textbookFormulaSkolemImage_le_max hseed default phi).trans
        (max_le hkappa hcard))

/-- In particular, a one-formula step has the exact textbook maximum bound. -/
theorem card_textbookFormulaSkolemStep_le_max
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U)
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1)) :
    ZFSet.card (textbookFormulaSkolemStep seed U hseed default phi) ≤
      max Cardinal.aleph0 (ZFSet.card seed) := by
  exact card_textbookFormulaSkolemStep_le_of_le hseed default phi
    (le_max_left _ _) (le_max_right _ _)

/-- A finite sequential pass preserves an arbitrary infinite cardinal bound
on its input. -/
theorem card_textbookSkolemPass_le_of_le
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    {kappa : Cardinal.{u}} (hkappa : Cardinal.aleph0 ≤ kappa)
    (hcard : ZFSet.card seed.1 ≤ kappa) :
    ZFSet.card (textbookSkolemPass U default matrices seed).1 ≤ kappa := by
  induction matrices generalizing seed with
  | nil => exact hcard
  | cons matrix rest ih =>
      apply ih (seed := textbookFormulaSkolemStepIn U default matrix seed)
      exact card_textbookFormulaSkolemStep_le_of_le
        seed.2 default matrix.2 hkappa hcard

/-- A finite pass has cardinality at most the infinite closure of the
cardinality of its original seed. -/
theorem card_textbookSkolemPass_le_max
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    ZFSet.card (textbookSkolemPass U default matrices seed).1 ≤
      max Cardinal.aleph0 (ZFSet.card seed.1) := by
  exact card_textbookSkolemPass_le_of_le U default matrices seed
    (le_max_left _ _) (le_max_right _ _)

/-- Every natural-number stage has the same bound determined by the initial
seed. -/
theorem card_textbookSkolemStage_le_max
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) (stage : Nat) :
    ZFSet.card (textbookSkolemStage U default matrices seed stage).1 ≤
      max Cardinal.aleph0 (ZFSet.card seed.1) := by
  induction stage with
  | zero => exact le_max_right _ _
  | succ stage ih =>
      exact card_textbookSkolemPass_le_of_le U default matrices
        (textbookSkolemStage U default matrices seed stage)
        (le_max_left _ _) ih

/-- The actual `ZFSet.iUnion` of all natural-number stages satisfies the same
cardinal bound. -/
theorem card_textbookSkolemOmegaUnion_le_max
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    ZFSet.card (textbookSkolemOmegaUnion U default matrices seed) ≤
      max Cardinal.aleph0 (ZFSet.card seed.1) := by
  let kappa : Cardinal.{u} :=
    max Cardinal.aleph0 (ZFSet.card seed.1)
  have hkappa : Cardinal.aleph0 ≤ kappa := le_max_left _ _
  let stages : Nat → ZFSet.{u} := fun stage =>
    (textbookSkolemStage U default matrices seed stage).1
  calc
    ZFSet.card (textbookSkolemOmegaUnion U default matrices seed)
        = ZFSet.card (ZFSet.iUnion stages) := by
      rfl
    _ ≤ Cardinal.sum (fun stage : Nat => ZFSet.card (stages stage)) := by
      simpa only [Cardinal.lift_id'] using
        (ZFSet.lift_card_iUnion_le_sum_card (f := stages))
    _ ≤ Cardinal.sum (fun _ : Nat => kappa) :=
      Cardinal.sum_le_sum _ _ fun stage =>
        card_textbookSkolemStage_le_max U default matrices seed stage
    _ = kappa := by
      rw [Cardinal.sum_const]
      simp only [Cardinal.mk_nat, Cardinal.lift_aleph0,
        Cardinal.lift_id']
      exact Cardinal.aleph0_mul_eq hkappa

/-- If the initial seed is infinite, retaining the seed turns the textbook
upper bound into an exact cardinality equality. -/
theorem card_textbookSkolemOmegaUnion_eq_of_aleph0_le
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U)
    (hseedInfinite : Cardinal.aleph0 ≤ ZFSet.card seed.1) :
    ZFSet.card (textbookSkolemOmegaUnion U default matrices seed) =
      ZFSet.card seed.1 := by
  apply le_antisymm
  · simpa only [max_eq_right hseedInfinite] using
      card_textbookSkolemOmegaUnion_le_max U default matrices seed
  · exact ZFSet.card_mono
      (seed_subset_textbookSkolemOmegaUnion U default matrices seed)

/-- External subtype-cardinality form of the textbook hull bound.  This is
the precise meaning of `#Hull ≤ max aleph0 #seed` for the two internally
represented `ZFSet`s. -/
theorem cardinalMk_textbookSkolemOmegaUnion_le_max
    (U : ZFSet.{u}) (default : ZFCarrier U)
    (matrices : List ExistentialMatrix) (seed : ZFSubset U) :
    Cardinal.mk (ZFCarrier
        (textbookSkolemOmegaUnion U default matrices seed)) ≤
      max Cardinal.aleph0 (Cardinal.mk (ZFCarrier seed.1)) := by
  have hLift :
      Cardinal.lift.{u + 1, u}
          (ZFSet.card (textbookSkolemOmegaUnion U default matrices seed)) ≤
        Cardinal.lift.{u + 1, u}
          (max Cardinal.aleph0 (ZFSet.card seed.1)) :=
    Cardinal.lift_monotone
      (card_textbookSkolemOmegaUnion_le_max U default matrices seed)
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_max,
    Cardinal.lift_aleph0] using hLift

end

end Constructible
