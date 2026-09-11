/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentElementarity
public import Mathlib.SetTheory.ZFC.Cardinal

/-!
# The textbook Skolem function for one existential formula

This file implements one exact component of the finite-fragment construction
in Section 6.3 of Wang Fangting, *Axiomatic Set Theory*.

Fix a set-sized structure `U`, a matrix `phi(params, y)`, and an element
`default` of `U`.  The associated total Skolem function sends a parameter
tuple to the `WellOrderingRel`-least witness in `U` when the witness fiber is
nonempty, and to `default` otherwise.  Thus the empty-fiber branch is part of
the definition, just as in the textbook.

For a set `seed subseteq U`, `textbookFormulaSkolemImage` collects the values
of this function on all tuples from `seed` by `ZFSet.range`.  It is an actual
`ZFSet`, but the function and its well-order are external Lean objects.  No
claim is made here that their graphs belong to `L`; the finite-fragment
reflection theorem does not require that stronger assertion.

This file treats one existential formula only.  It does not yet form the
finite family of all existential subformulas, iterate it through omega, or
state the final cardinal bound.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- The least element of a nonempty ambient set in the fixed metatheoretic
well-order.  This is the default value used in Wang's Section 6.3 when a
Skolem witness fiber is empty. -/
noncomputable def textbookSkolemDefault (U : ZFSet.{u})
    (hU : Nonempty (ZFCarrier U)) : ZFCarrier U := by
  letI : Nonempty (ZFCarrier U) := hU
  exact (IsWellFounded.wf : WellFounded
    (WellOrderingRel : ZFCarrier U -> ZFCarrier U -> Prop)).min
      Set.univ Set.univ_nonempty

/-- The textbook default is minimal in the fixed well-order. -/
theorem textbookSkolemDefault_minimal (U : ZFSet.{u})
    (hU : Nonempty (ZFCarrier U)) (z : ZFCarrier U) :
    ¬WellOrderingRel z (textbookSkolemDefault U hU) := by
  letI : Nonempty (ZFCarrier U) := hU
  unfold textbookSkolemDefault
  exact (IsWellFounded.wf : WellFounded
    (WellOrderingRel : ZFCarrier U -> ZFCarrier U -> Prop)).not_lt_min
      Set.univ (Set.mem_univ z)

/-- The witness fiber of `phi(params, y)` inside the set-sized structure `U`. -/
def formulaWitnessCandidates (U : ZFSet.{u}) {n : Nat}
    (phi : FOFormula (n + 1)) (params : Tuple (ZFCarrier U) n) :
    Set (ZFCarrier U) :=
  {y | FOFormula.Satisfies (zfCarrierMem U) phi (snoc params y)}

/--
The textbook total Skolem value for one existential formula.  A nonempty
fiber contributes its least witness in the fixed metatheoretic well-order;
an empty fiber contributes the displayed default element of `U`.
-/
noncomputable def textbookSkolemValue (U : ZFSet.{u})
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U) n) : ZFCarrier U := by
  classical
  exact if h : (formulaWitnessCandidates U phi params).Nonempty then
      (IsWellFounded.wf : WellFounded
        (WellOrderingRel : ZFCarrier U -> ZFCarrier U -> Prop)).min
          (formulaWitnessCandidates U phi params) h
    else
      default

/-- On a nonempty fiber, the selected value is a genuine witness. -/
theorem textbookSkolemValue_mem_candidates (U : ZFSet.{u})
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U) n)
    (h : (formulaWitnessCandidates U phi params).Nonempty) :
    textbookSkolemValue U default phi params ∈
      formulaWitnessCandidates U phi params := by
  rw [textbookSkolemValue, dif_pos h]
  exact WellFounded.min_mem _ _ _

/-- On an empty fiber, the total Skolem function has exactly its default value. -/
theorem textbookSkolemValue_eq_default (U : ZFSet.{u})
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U) n)
    (h : ¬(formulaWitnessCandidates U phi params).Nonempty) :
    textbookSkolemValue U default phi params = default := by
  rw [textbookSkolemValue, dif_neg h]

/-- The chosen nonempty-fiber witness is least in `WellOrderingRel`. -/
theorem textbookSkolemValue_minimal (U : ZFSet.{u})
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U) n)
    (h : (formulaWitnessCandidates U phi params).Nonempty)
    {z : ZFCarrier U} (hz : z ∈ formulaWitnessCandidates U phi params) :
    ¬WellOrderingRel z (textbookSkolemValue U default phi params) := by
  rw [textbookSkolemValue, dif_pos h]
  exact WellFounded.not_lt_min _ _ hz

/-- Existence of a witness implies satisfaction by the selected value. -/
theorem textbookSkolemValue_satisfies_of_exists (U : ZFSet.{u})
    (default : ZFCarrier U) {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U) n)
    (hexists : ∃ y : ZFCarrier U,
      FOFormula.Satisfies (zfCarrierMem U) phi (snoc params y)) :
    FOFormula.Satisfies (zfCarrierMem U) phi
      (snoc params (textbookSkolemValue U default phi params)) := by
  have hnonempty : (formulaWitnessCandidates U phi params).Nonempty :=
    hexists
  exact textbookSkolemValue_mem_candidates U default phi params hnonempty

/-- Regard a tuple from `seed` as a tuple from `U`. -/
def liftSeedTuple {seed U : ZFSet.{u}} (hseed : seed ⊆ U) {n : Nat}
    (params : Tuple (ZFCarrier seed) n) : Tuple (ZFCarrier U) n :=
  fun i => ⟨(params i).1, hseed (params i).2⟩

@[simp]
theorem liftSeedTuple_val {seed U : ZFSet.{u}} (hseed : seed ⊆ U)
    {n : Nat} (params : Tuple (ZFCarrier seed) n) (i : Fin n) :
    (liftSeedTuple hseed params i).1 = (params i).1 :=
  rfl

/-- Values of the textbook Skolem function on all parameter tuples in `seed`. -/
noncomputable def textbookFormulaSkolemImage
    (seed U : ZFSet.{u}) (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) : ZFSet.{u} :=
  ZFSet.range fun params : Tuple (ZFCarrier seed) n =>
    (textbookSkolemValue U default phi (liftSeedTuple hseed params)).1

@[simp]
theorem mem_textbookFormulaSkolemImage_iff
    {seed U x : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) :
    x ∈ textbookFormulaSkolemImage seed U hseed default phi ↔
      ∃ params : Tuple (ZFCarrier seed) n,
        (textbookSkolemValue U default phi
          (liftSeedTuple hseed params)).1 = x := by
  simp [textbookFormulaSkolemImage]

/-- The Skolem image is no larger than its parameter-tuple domain. -/
theorem lift_card_textbookFormulaSkolemImage_le
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) :
    Cardinal.lift.{u + 1, u} (ZFSet.card
      (textbookFormulaSkolemImage seed U hseed default phi)) ≤
      Cardinal.lift.{u, u + 1}
        (Cardinal.mk (Tuple (ZFCarrier seed) n)) := by
  simpa only [textbookFormulaSkolemImage] using
    (ZFSet.lift_card_range_le
      (f := fun params : Tuple (ZFCarrier seed) n =>
        (textbookSkolemValue U default phi
          (liftSeedTuple hseed params)).1))

/-- One exact textbook step retains the seed and adjoins the Skolem range. -/
noncomputable def textbookFormulaSkolemStep
    (seed U : ZFSet.{u}) (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) : ZFSet.{u} :=
  seed ∪ textbookFormulaSkolemImage seed U hseed default phi

/-- Every member of the seed remains in the one-formula step. -/
theorem seed_subset_textbookFormulaSkolemStep
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) :
    seed ⊆ textbookFormulaSkolemStep seed U hseed default phi := by
  intro x hx
  exact ZFSet.mem_union.mpr (Or.inl hx)

/-- Every value adjoined by the one-formula step is still a member of `U`. -/
theorem textbookFormulaSkolemStep_subset
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1)) :
    textbookFormulaSkolemStep seed U hseed default phi ⊆ U := by
  intro x hx
  rcases ZFSet.mem_union.mp hx with hxSeed | hxImage
  · exact hseed hxSeed
  · rcases (mem_textbookFormulaSkolemImage_iff hseed default phi).mp hxImage with
      ⟨params, hvalue⟩
    rw [← hvalue]
    exact (textbookSkolemValue U default phi
      (liftSeedTuple hseed params)).2

/--
Every seed-parameter instance which has a witness in `U` has the selected
witness in the one-formula step.  This is the exact one-function closure fact
used in the textbook Tarski--Vaught argument.
-/
theorem exists_witness_mem_textbookFormulaSkolemStep
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier seed) n)
    (hexists : ∃ y : ZFCarrier U,
      FOFormula.Satisfies (zfCarrierMem U) phi
        (snoc (liftSeedTuple hseed params) y)) :
    ∃ y : ZFCarrier U,
      y.1 ∈ textbookFormulaSkolemStep seed U hseed default phi ∧
        FOFormula.Satisfies (zfCarrierMem U) phi
          (snoc (liftSeedTuple hseed params) y) := by
  let y := textbookSkolemValue U default phi (liftSeedTuple hseed params)
  refine ⟨y, ?_, textbookSkolemValue_satisfies_of_exists
    U default phi (liftSeedTuple hseed params) hexists⟩
  exact ZFSet.mem_union.mpr (Or.inr (by
    apply (mem_textbookFormulaSkolemImage_iff hseed default phi).mpr
    exact ⟨params, rfl⟩))

/--
Raw `SatisfiesIn` form of the one-formula closure theorem.  This is the form
used by `ClosesWithin`; it is equivalent to the subtype theorem above, not a
new satisfaction notion.
-/
theorem exists_witnessIn_mem_textbookFormulaSkolemStep
    {seed U : ZFSet.{u}} (hseed : seed ⊆ U) (default : ZFCarrier U)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple ZFSet.{u} n) (hparams : ∀ i, params i ∈ seed)
    (hexists : Model.SatisfiesIn (U : Set ZFSet.{u}) (.ex phi) params) :
    ∃ y : ZFSet.{u},
      y ∈ textbookFormulaSkolemStep seed U hseed default phi ∧
        Model.SatisfiesIn (U : Set ZFSet.{u}) phi (snoc params y) := by
  let paramsSeed : Tuple (ZFCarrier seed) n :=
    fun i => ⟨params i, hparams i⟩
  let paramsU := liftSeedTuple hseed paramsSeed
  have hparamsVal : (fun i => (paramsU i).1) = params := by
    funext i
    rfl
  rcases hexists with ⟨x, hxU, hxSat⟩
  let xU : ZFCarrier U := ⟨x, hxU⟩
  have hxSubtype :
      FOFormula.Satisfies (zfCarrierMem U) phi (snoc paramsU xU) := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (U : Set ZFSet.{u}) phi (snoc paramsU xU)).mpr
    simpa only [Model.subtypeVal_snoc, hparamsVal, xU] using hxSat
  rcases exists_witness_mem_textbookFormulaSkolemStep
      hseed default phi paramsSeed ⟨xU, hxSubtype⟩ with
    ⟨yU, hyStep, hySubtype⟩
  refine ⟨yU.1, hyStep, ?_⟩
  have hyRaw := (Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) phi (snoc paramsU yU)).mp hySubtype
  simpa only [Model.subtypeVal_snoc, hparamsVal] using hyRaw

end

end Constructible
