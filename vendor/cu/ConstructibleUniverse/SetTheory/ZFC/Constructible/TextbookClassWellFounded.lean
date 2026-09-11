/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPredecessorClosure

/-!
# Class minima from textbook set-well-foundedness

This file proves Theorem 1 of Section 6.1 in Wang Fangting,
*Axiomatic Set Theory*.  The definition of a well-founded class relation only
assumes minima for nonempty actual sets.  Set-likeness makes the finite
predecessor closure of a point an actual `ZFSet`; intersecting that closure
with an arbitrary nonempty external subclass then upgrades the conclusion to
all subclasses.

The file also records the textbook local recursion domain

`d_x = {x} union cl(A,x,R)`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## The general class-minimum theorem -/

/-- Every nonempty external subclass of `A` has an `R`-minimal member.  This
is the conclusion of the textbook's general induction theorem, not the
definition of `HasSetMinimaOn`. -/
def HasClassMinimaOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall X : Set ZFSet.{u}, X ⊆ A -> X.Nonempty ->
    exists x, x ∈ X ∧ forall y, y ∈ X -> Not (ClassRel R y x)

/-- Textbook Section 6.1, Theorem 1.  The only set to which
`HasSetMinimaOn` is applied is `X intersect cl(A,x,R)`, represented by
Separation from the actual predecessor closure. -/
theorem hasClassMinimaOn_of_isWellFoundedSetLikeOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) :
    HasClassMinimaOn A R := by
  rcases hR with ⟨hrelation, hsetMinima, hsetLike⟩
  intro X hXA hXnonempty
  rcases hXnonempty with ⟨x, hxX⟩
  have hxA : x ∈ A := hXA hxX
  by_cases hhasPredecessor : exists y, y ∈ X ∧ ClassRel R y x
  · let boundedBad : ZFSet.{u} :=
      (predecessorClosure A R hsetLike x).sep fun y => y ∈ X
    have hboundedSubset : forall y, y ∈ boundedBad -> y ∈ A := by
      intro y hy
      exact predecessorClosure_subset hsetLike hxA
        (ZFSet.mem_sep.mp hy).1
    have hboundedNonempty : exists y, y ∈ boundedBad := by
      rcases hhasPredecessor with ⟨y, hyX, hyx⟩
      have hyA : y ∈ A := hXA hyX
      have hyLayerZero :
          y ∈ predecessorLayer A R hsetLike x 0 := by
        rw [predecessorLayer_zero]
        exact (displayedPredecessors_spec hsetLike hxA y).mpr
          ⟨hyA, hyx⟩
      have hyClosure :
          y ∈ predecessorClosure A R hsetLike x :=
        mem_predecessorClosure_iff.mpr ⟨0, hyLayerZero⟩
      exact ⟨y, ZFSet.mem_sep.mpr ⟨hyClosure, hyX⟩⟩
    rcases hsetMinima boundedBad hboundedSubset hboundedNonempty with
      ⟨u, huBounded, huMinimal⟩
    have huClosure : u ∈ predecessorClosure A R hsetLike x :=
      (ZFSet.mem_sep.mp huBounded).1
    have huX : u ∈ X := (ZFSet.mem_sep.mp huBounded).2
    refine ⟨u, huX, ?_⟩
    intro v hvX hvu
    have hvClosure : v ∈ predecessorClosure A R hsetLike x :=
      predecessorClosure_downward_closed hrelation hsetLike hxA
        huClosure hvu
    exact huMinimal v (ZFSet.mem_sep.mpr ⟨hvClosure, hvX⟩) hvu
  · exact ⟨x, hxX, fun y hyX hyx => hhasPredecessor ⟨y, hyX, hyx⟩⟩

/-- After the textbook class-minimum theorem has been proved, its relation on
the Lean subtype of `A` is genuinely well-founded.  This is a derived bridge,
not a strengthening silently inserted into the definition. -/
theorem wellFounded_classRel_zfSubtype
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) :
    WellFounded (fun y x : {z : ZFSet.{u} // z ∈ A} =>
      ClassRel R y.1 x.1) := by
  apply WellFounded.wellFounded_iff_has_min.mpr
  intro s hs
  let X : Set ZFSet.{u} := Subtype.val '' s
  have hXA : X ⊆ A := by
    rintro z ⟨zA, _hzS, rfl⟩
    exact zA.2
  have hXnonempty : X.Nonempty := by
    rcases hs with ⟨zA, hzS⟩
    exact ⟨zA.1, ⟨zA, hzS, rfl⟩⟩
  rcases hasClassMinimaOn_of_isWellFoundedSetLikeOn hR X hXA
      hXnonempty with ⟨z, hzX, hzMinimal⟩
  rcases hzX with ⟨zA, hzS, rfl⟩
  refine ⟨zA, hzS, ?_⟩
  intro yA hyS hyz
  exact hzMinimal yA.1 ⟨yA, hyS, rfl⟩ hyz

/-! ## The local domain used in the recursion proof -/

/-- The textbook local recursion domain `d_x = {x} union cl(A,x,R)`. -/
noncomputable def localRecursionDomain
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  ({x} : ZFSet.{u}) ∪ predecessorClosure A R hsetLike x

@[simp]
theorem mem_localRecursionDomain_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {hsetLike : HasSetPredecessorsOn A R} {x y : ZFSet.{u}} :
    y ∈ localRecursionDomain A R hsetLike x ↔
      y = x ∨ y ∈ predecessorClosure A R hsetLike x := by
  simp [localRecursionDomain]

/-- The local domain is contained in `A` whenever its top point is in `A`. -/
theorem localRecursionDomain_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (localRecursionDomain A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro y hy
  rcases mem_localRecursionDomain_iff.mp hy with rfl | hyClosure
  · exact hx
  · exact predecessorClosure_subset hsetLike hx hyClosure

/-- Every predecessor of a point in `d_x` again belongs to `d_x`. -/
theorem localRecursionDomain_predecessorClosed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y z : ZFSet.{u}}
    (hx : x ∈ A)
    (hy : y ∈ localRecursionDomain A R hsetLike x)
    (hzy : ClassRel R z y) :
    z ∈ localRecursionDomain A R hsetLike x := by
  apply mem_localRecursionDomain_iff.mpr
  right
  rcases mem_localRecursionDomain_iff.mp hy with hyEq | hyClosure
  · subst y
    have hzA : z ∈ A := hrelation.left_mem hzy
    have hzLayerZero : z ∈ predecessorLayer A R hsetLike x 0 := by
      rw [predecessorLayer_zero]
      exact (displayedPredecessors_spec hsetLike hx z).mpr ⟨hzA, hzy⟩
    exact mem_predecessorClosure_iff.mpr ⟨0, hzLayerZero⟩
  · exact predecessorClosure_downward_closed hrelation hsetLike hx
      hyClosure hzy

end

end Constructible
