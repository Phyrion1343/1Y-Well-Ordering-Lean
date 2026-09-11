/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookSetWellFounded

/-!
# Textbook predecessor closure for set-like class relations

This file formalizes Definition 3 and Propositions 1--2 of Section 6.1 in
Wang Fangting, *Axiomatic Set Theory*.

For a set-like class relation `R` on `A`, `displayedPredecessors A R hsetLike x`
is the displayed set

`{y in A | ClassRel R y x}`.

Starting with this set as `p_0(x)`, the next layer is the union of the
displayed predecessor sets of all members of the current layer.  The closure
is the union of all finite layers.  Both unions below are actual `ZFSet`s;
neither is merely an external `Set ZFSet`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Displayed predecessor sets -/

/-- A chosen actual set displaying the predecessors of `x` in `A`.

Outside `A` its value is defined to be empty.  All mathematical uses below
are at points of `A`, where `HasSetPredecessorsOn` gives the exact membership
description. -/
noncomputable def displayedPredecessors
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  by
    classical
    exact if hx : x ∈ A then Classical.choose (hsetLike x hx) else ∅

/-- The chosen set has exactly the predecessor members asserted by
set-likeness. -/
theorem displayedPredecessors_spec
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    IsPredecessorSet A R x (displayedPredecessors A R hsetLike x) := by
  unfold displayedPredecessors
  rw [dif_pos hx]
  exact Classical.choose_spec (hsetLike x hx)

/-- A displayed predecessor set is extensionally unique.  Thus the ambient
`Classical.choose` in `displayedPredecessors` does not add an object-level
choice principle: it selects the unique set whose existence is already part
of set-likeness. -/
theorem isPredecessorSet_unique
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {x predecessors₁ predecessors₂ : ZFSet.{u}}
    (h₁ : IsPredecessorSet A R x predecessors₁)
    (h₂ : IsPredecessorSet A R x predecessors₂) :
    predecessors₁ = predecessors₂ := by
  apply ZFSet.ext
  intro y
  exact (h₁ y).trans (h₂ y).symm

/-- Any set with the required predecessor semantics is the chosen displayed
predecessor set. -/
theorem eq_displayedPredecessors_of_isPredecessorSet
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x predecessors : ZFSet.{u}}
    (hx : x ∈ A) (hpredecessors : IsPredecessorSet A R x predecessors) :
    predecessors = displayedPredecessors A R hsetLike x :=
  isPredecessorSet_unique hpredecessors
    (displayedPredecessors_spec hsetLike hx)

/-- The arbitrary totalization of the displayed predecessor operation is
empty away from its intended domain. -/
theorem displayedPredecessors_eq_empty_of_not_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∉ A) :
    displayedPredecessors A R hsetLike x = ∅ := by
  simp [displayedPredecessors, hx]

/-- Every member of a displayed predecessor set is in the relation's
domain. -/
theorem displayedPredecessors_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (displayedPredecessors A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro y hy
  exact (displayedPredecessors_spec hsetLike hx y).mp hy |>.1

/-! ## The finite predecessor layers and their union -/

/-- The textbook finite predecessor layers:

* `p_0(x)` is the displayed predecessor set of `x`;
* `p_(n+1)(x)` is the union of the predecessor sets of members of `p_n(x)`.

The indexed union ranges over the actual members of `p_n(x)`, so every layer
is an actual `ZFSet`. -/
noncomputable def predecessorLayer
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    Nat → ZFSet.{u}
  | 0 => displayedPredecessors A R hsetLike x
  | n + 1 => ZFSet.iUnion fun y : ZFCarrier (predecessorLayer A R hsetLike x n) =>
      displayedPredecessors A R hsetLike y.1

@[simp]
theorem predecessorLayer_zero
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    predecessorLayer A R hsetLike x 0 =
      displayedPredecessors A R hsetLike x := rfl

@[simp]
theorem predecessorLayer_succ
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) (n : Nat) :
    predecessorLayer A R hsetLike x (n + 1) =
      ZFSet.iUnion fun y : ZFCarrier (predecessorLayer A R hsetLike x n) =>
        displayedPredecessors A R hsetLike y.1 := rfl

/-- Every finite predecessor layer remains inside `A`. -/
theorem predecessorLayer_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    ∀ n, (predecessorLayer A R hsetLike x n : Set ZFSet.{u}) ⊆ A := by
  intro n
  induction n with
  | zero =>
      exact displayedPredecessors_subset hsetLike hx
  | succ n ih =>
      intro z hz
      change z ∈ predecessorLayer A R hsetLike x (n + 1) at hz
      rw [predecessorLayer_succ] at hz
      rcases ZFSet.mem_iUnion.mp hz with ⟨y, hzy⟩
      have hyA : y.1 ∈ A := ih y.2
      exact (displayedPredecessors_spec hsetLike hyA z).mp hzy |>.1

/-- Exact membership semantics of a successor predecessor layer. -/
theorem mem_predecessorLayer_succ_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x z : ZFSet.{u}}
    (hx : x ∈ A) (n : Nat) :
    z ∈ predecessorLayer A R hsetLike x (n + 1) ↔
      ∃ y, y ∈ predecessorLayer A R hsetLike x n ∧
        z ∈ A ∧ ClassRel R z y := by
  rw [predecessorLayer_succ, ZFSet.mem_iUnion]
  constructor
  · rintro ⟨y, hzy⟩
    have hyA : y.1 ∈ A := predecessorLayer_subset hsetLike hx n y.2
    exact ⟨y.1, y.2, (displayedPredecessors_spec hsetLike hyA z).mp hzy⟩
  · rintro ⟨y, hyLayer, hzA, hzy⟩
    let yLayer : ZFCarrier (predecessorLayer A R hsetLike x n) :=
      ⟨y, hyLayer⟩
    refine ⟨yLayer, ?_⟩
    exact (displayedPredecessors_spec hsetLike
      (predecessorLayer_subset hsetLike hx n hyLayer) z).mpr ⟨hzA, hzy⟩

/-- `cl(A,x,R)`: the actual set obtained by taking the union of all finite
predecessor layers.  `ZFSet.iUnion` is the set-sized union indexed by `Nat`,
the external index type corresponding to `n in omega` in the displayed
textbook construction. -/
noncomputable def predecessorClosure
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (predecessorLayer A R hsetLike x)

@[simp]
theorem mem_predecessorClosure_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {hsetLike : HasSetPredecessorsOn A R} {x z : ZFSet.{u}} :
    z ∈ predecessorClosure A R hsetLike x ↔
      ∃ n, z ∈ predecessorLayer A R hsetLike x n := by
  simp [predecessorClosure]

/-- The predecessor closure of a point of `A` is still a subset of `A`. -/
theorem predecessorClosure_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (predecessorClosure A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro z hz
  rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
  exact predecessorLayer_subset hsetLike hx n hzn

/-! ## Textbook Propositions 1 and 2 -/

/-- Textbook Proposition 1: if `y` belongs to `cl(A,x,R)`, then the displayed
predecessor set of `y` is contained in the same closure. -/
theorem displayedPredecessors_subset_predecessorClosure_of_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x y : ZFSet.{u}}
    (hx : x ∈ A) (hy : y ∈ predecessorClosure A R hsetLike x) :
    displayedPredecessors A R hsetLike y ⊆
      predecessorClosure A R hsetLike x := by
  intro z hz
  rcases mem_predecessorClosure_iff.mp hy with ⟨n, hyn⟩
  apply mem_predecessorClosure_iff.mpr
  refine ⟨n + 1, ?_⟩
  apply (mem_predecessorLayer_succ_iff hsetLike hx n).mpr
  have hyA : y ∈ A := predecessorLayer_subset hsetLike hx n hyn
  exact ⟨y, hyn, (displayedPredecessors_spec hsetLike hyA z).mp hz⟩

/-- Relation form of Proposition 1: the closure is downward closed under
`R`.  `IsRelationOn` supplies the fact that the lower endpoint is in `A`. -/
theorem predecessorClosure_downward_closed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y z : ZFSet.{u}}
    (hx : x ∈ A) (hy : y ∈ predecessorClosure A R hsetLike x)
    (hzy : ClassRel R z y) :
    z ∈ predecessorClosure A R hsetLike x := by
  have hyA : y ∈ A := predecessorClosure_subset hsetLike hx hy
  have hzPred : z ∈ displayedPredecessors A R hsetLike y :=
    (displayedPredecessors_spec hsetLike hyA z).mpr
      ⟨hrelation.left_mem hzy, hzy⟩
  exact displayedPredecessors_subset_predecessorClosure_of_mem
    hsetLike hx hy hzPred

/-- Textbook Proposition 2: an immediate predecessor has the smaller
predecessor closure. -/
theorem predecessorClosure_subset_of_rel
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y : ZFSet.{u}}
    (hyx : ClassRel R y x) :
    predecessorClosure A R hsetLike y ⊆
      predecessorClosure A R hsetLike x := by
  have hxA : x ∈ A := hrelation.right_mem hyx
  have hyA : y ∈ A := hrelation.left_mem hyx
  have hyLayerZero : y ∈ predecessorLayer A R hsetLike x 0 := by
    rw [predecessorLayer_zero]
    exact (displayedPredecessors_spec hsetLike hxA y).mpr ⟨hyA, hyx⟩
  have hyClosure : y ∈ predecessorClosure A R hsetLike x :=
    mem_predecessorClosure_iff.mpr ⟨0, hyLayerZero⟩
  have hlevels : ∀ n,
      predecessorLayer A R hsetLike y n ⊆
        predecessorClosure A R hsetLike x := by
    intro n
    induction n with
    | zero =>
        rw [predecessorLayer_zero]
        exact displayedPredecessors_subset_predecessorClosure_of_mem
          hsetLike hxA hyClosure
    | succ n ih =>
        intro z hz
        rcases (mem_predecessorLayer_succ_iff hsetLike hyA n).mp hz with
          ⟨s, hsn, hzA, hzs⟩
        have hsClosure : s ∈ predecessorClosure A R hsetLike x := ih hsn
        have hsA : s ∈ A := predecessorLayer_subset hsetLike hyA n hsn
        have hzPred : z ∈ displayedPredecessors A R hsetLike s :=
          (displayedPredecessors_spec hsetLike hsA z).mpr ⟨hzA, hzs⟩
        exact displayedPredecessors_subset_predecessorClosure_of_mem
          hsetLike hxA hsClosure hzPred
  intro z hz
  rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
  exact hlevels n hzn

end

end Constructible
