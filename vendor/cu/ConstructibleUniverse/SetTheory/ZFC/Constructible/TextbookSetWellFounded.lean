/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Absoluteness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RestrictionGraph

/-!
# Textbook set-well-founded and set-like class relations

This file formalizes the definitions used in Sections 6.1 and 6.2 of Wang
Fangting, *Axiomatic Set Theory*.

A class relation is well-founded on `A` when every nonempty **set** contained
in `A` has a minimal member.  This is deliberately not defined as Lean's
`WellFounded` on the whole external type: for a proper-class domain that would
quantify over arbitrary external subclasses and would be stronger than the
textbook definition.

Set-likeness is a separate condition saying that every predecessor class is
represented by an actual `ZFSet`.  The bad-point theorem below is the exact
minimal-counterexample argument used in the recursion absoluteness proof.
Its bad set is an ambient set; it is not asserted to belong to a model.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Standard class-relation definitions -/

/-- Evaluation of a binary class relation represented as two-coordinate
tuples.  The coordinate order is `(left,right)`. -/
def ClassRel (R : Set (Tuple ZFSet.{u} 2))
    (left right : ZFSet.{u}) : Prop :=
  ![left, right] ∈ R

/-- Every pair in `R` has both coordinates in `A`, i.e. `R` is a relation on
`A`. -/
def IsRelationOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall s, s ∈ R -> Model.TupleIn A s

/-- The left endpoint of a pair in a relation on `A` lies in `A`. -/
theorem IsRelationOn.left_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsRelationOn A R) {left right : ZFSet.{u}}
    (h : ClassRel R left right) : left ∈ A := by
  have htuple := hR ![left, right] h
  have hleft := htuple (0 : Fin 2)
  change left ∈ A at hleft
  exact hleft

/-- The right endpoint of a pair in a relation on `A` lies in `A`. -/
theorem IsRelationOn.right_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsRelationOn A R) {left right : ZFSet.{u}}
    (h : ClassRel R left right) : right ∈ A := by
  have htuple := hR ![left, right] h
  have hright := htuple (1 : Fin 2)
  change right ∈ A at hright
  exact hright

/-- Every nonempty actual set contained in `A` has an `R`-minimal member.
This is the textbook class-relation notion of well-foundedness. -/
def HasSetMinimaOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall z : ZFSet.{u},
    (forall x, x ∈ z -> x ∈ A) ->
    (exists x, x ∈ z) ->
    exists u, u ∈ z ∧ forall v, v ∈ z -> Not (ClassRel R v u)

/-- Every predecessor class of a point of `A` is represented by an actual
set.  This is the textbook notion of a set-like relation. -/
def HasSetPredecessorsOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall x, x ∈ A ->
    exists predecessors : ZFSet.{u}, forall y,
      y ∈ predecessors <-> y ∈ A ∧ ClassRel R y x

/-- A well-founded set-like relation in the exact textbook sense. -/
def IsWellFoundedSetLikeOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  IsRelationOn A R ∧ HasSetMinimaOn A R ∧ HasSetPredecessorsOn A R

/-- `predecessors` represents the full predecessor set of `x` in `A`. -/
def IsPredecessorSet (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2))
    (x predecessors : ZFSet.{u}) : Prop :=
  forall y, y ∈ predecessors <-> y ∈ A ∧ ClassRel R y x

/-- Textbook condition (III): every ambient predecessor of an argument from
`M` is again in `M`.  This condition remains separate from set-likeness. -/
def PredecessorsClosedIn (M A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall x, x ∈ M -> forall y, y ∈ A -> ClassRel R y x -> y ∈ M

/-- The actual ambient set representing the external class intersection
`A ∩ M`.  It is not asserted to be an element of `M`. -/
def modelIntersectionZF (M : ZFSet.{u})
    (A : Set ZFSet.{u}) : ZFSet.{u} :=
  M.sep fun x => x ∈ A

@[simp]
theorem mem_modelIntersectionZF_iff
    {M : ZFSet.{u}} {A : Set ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ modelIntersectionZF M A <-> x ∈ M ∧ x ∈ A := by
  exact ZFSet.mem_sep

/-! ## Comparison with Lean well-foundedness on an actual set -/

/-- On an actual set-sized domain, and only there, the textbook set-minimum
condition is equivalent to Lean well-foundedness of the subtype relation. -/
theorem hasSetMinimaOn_iff_wellFounded_zfCarrier
    (domain : ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2)) :
    HasSetMinimaOn (domain : Set ZFSet.{u}) R <->
      WellFounded fun y x : ZFCarrier domain => ClassRel R y.1 x.1 := by
  constructor
  · intro hmin
    apply WellFounded.wellFounded_iff_has_min.mpr
    intro s hs
    let represented : ZFSet.{u} := domain.sep fun x =>
      exists hx : x ∈ domain,
        (⟨x, hx⟩ : ZFCarrier domain) ∈ s
    have hrepresentedSubset : forall x, x ∈ represented -> x ∈ domain := by
      intro x hx
      exact (ZFSet.mem_sep.mp hx).1
    have hrepresentedNonempty : exists x, x ∈ represented := by
      rcases hs with ⟨x, hx⟩
      refine ⟨x.1, ZFSet.mem_sep.mpr ⟨x.2, ?_⟩⟩
      exact ⟨x.2, by simpa only [Subtype.coe_eta] using hx⟩
    rcases hmin represented hrepresentedSubset hrepresentedNonempty with
      ⟨m, hmRepresented, hmMinimal⟩
    have hmDomain : m ∈ domain := (ZFSet.mem_sep.mp hmRepresented).1
    let mD : ZFCarrier domain := ⟨m, hmDomain⟩
    have hmS : mD ∈ s := by
      rcases (ZFSet.mem_sep.mp hmRepresented).2 with ⟨hm', hm'S⟩
      have heq : (⟨m, hm'⟩ : ZFCarrier domain) = mD := Subtype.ext rfl
      simpa only [heq] using hm'S
    refine ⟨mD, hmS, ?_⟩
    intro x hxS hxRel
    have hxRepresented : x.1 ∈ represented := by
      refine ZFSet.mem_sep.mpr ⟨x.2, x.2, ?_⟩
      simpa only [Subtype.coe_eta] using hxS
    exact hmMinimal x.1 hxRepresented hxRel
  · intro hwf z hzSubset hzNonempty
    let s : Set (ZFCarrier domain) := {x | x.1 ∈ z}
    have hsNonempty : s.Nonempty := by
      rcases hzNonempty with ⟨x, hx⟩
      have hxDomain : x ∈ domain := hzSubset x hx
      exact ⟨⟨x, hxDomain⟩, hx⟩
    rcases hwf.has_min s hsNonempty with ⟨m, hmS, hmMinimal⟩
    refine ⟨m.1, hmS, ?_⟩
    intro x hx
    have hxDomain : x ∈ domain := hzSubset x hx
    let xD : ZFCarrier domain := ⟨x, hxDomain⟩
    exact hmMinimal xD hx

/-! ## The textbook bad-point argument -/

/-- If local agreement follows from agreement at all predecessors, then two
functions agree on any set-sized predecessor-closed domain.  The proof takes
an `R`-minimal member of the ambient set of bad points. -/
theorem agreeOn_of_hasSetMinimaOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hmin : HasSetMinimaOn A R)
    {domain : ZFSet.{u}}
    (hdom : forall x, x ∈ domain -> x ∈ A)
    (hclosed : forall ⦃x⦄, x ∈ domain ->
      forall ⦃y⦄, ClassRel R y x -> y ∈ domain)
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hlocal : forall x, x ∈ domain ->
      (forall y, ClassRel R y x -> F y = H y) ->
      F x = H x) :
    forall x, x ∈ domain -> F x = H x := by
  intro x hx
  by_contra hxBad
  let bad : ZFSet.{u} := domain.sep fun z => Not (F z = H z)
  have hbadSubset : forall z, z ∈ bad -> z ∈ A := by
    intro z hz
    exact hdom z (ZFSet.mem_sep.mp hz).1
  have hbadNonempty : exists z, z ∈ bad := by
    exact ⟨x, ZFSet.mem_sep.mpr ⟨hx, hxBad⟩⟩
  rcases hmin bad hbadSubset hbadNonempty with ⟨u, huBad, huMinimal⟩
  have huDomain : u ∈ domain := (ZFSet.mem_sep.mp huBad).1
  have huNe : Not (F u = H u) := (ZFSet.mem_sep.mp huBad).2
  have hpredAgree : forall y, ClassRel R y u -> F y = H y := by
    intro y hyu
    have hyDomain : y ∈ domain := hclosed huDomain hyu
    by_contra hyBad
    have hyInBad : y ∈ bad :=
      ZFSet.mem_sep.mpr ⟨hyDomain, hyBad⟩
    exact huMinimal y hyInBad hyu
  exact huNe (hlocal u huDomain hpredAgree)

/-- Two solutions of the same recursive equation agree on a set-sized
predecessor-closed domain.  Unlike the auxiliary theorem based on Lean's
global `WellFounded`, this proof uses exactly the textbook set-minimum
hypothesis and the displayed predecessor sets. -/
theorem recursionSolutions_agreeOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hmin : HasSetMinimaOn A R)
    {domain : ZFSet.{u}}
    (hdom : forall x, x ∈ domain -> x ∈ A)
    (hclosed : forall ⦃x⦄, x ∈ domain ->
      forall ⦃y⦄, ClassRel R y x -> y ∈ domain)
    {predecessors : ZFSet.{u} -> ZFSet.{u}}
    (hpredecessors : forall x, x ∈ domain ->
      IsPredecessorSet A R x (predecessors x))
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hF : forall x, x ∈ domain ->
      F x = step x (predecessorRestrictionGraph (predecessors x) F))
    (hH : forall x, x ∈ domain ->
      H x = step x (predecessorRestrictionGraph (predecessors x) H)) :
    forall x, x ∈ domain -> F x = H x := by
  apply agreeOn_of_hasSetMinimaOn hmin hdom hclosed
  intro x hx hpredAgree
  rw [hF x hx, hH x hx]
  apply congrArg (step x)
  apply predecessorRestrictionGraph_congr
  intro y hy
  have hyRel : ClassRel R y x :=
    (hpredecessors x hx y).mp hy |>.2
  exact hpredAgree y hyRel

/-- The minimal-counterexample part of the textbook recursion-absoluteness
argument on `A ∩ M`.  Conditions that produce the model-relative solution
and prove the recursive step absolute are deliberately not hidden here: this
theorem compares two solutions already satisfying the displayed equations. -/
theorem recursionSolutions_agreeOn_modelIntersection
    {M : ZFSet.{u}}
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hmin : HasSetMinimaOn A R)
    {predecessors : ZFSet.{u} -> ZFSet.{u}}
    (hpredecessors : forall x, x ∈ A ->
      IsPredecessorSet A R x (predecessors x))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hF : forall x, x ∈ modelIntersectionZF M A ->
      F x = step x (predecessorRestrictionGraph (predecessors x) F))
    (hH : forall x, x ∈ modelIntersectionZF M A ->
      H x = step x (predecessorRestrictionGraph (predecessors x) H)) :
    forall x, x ∈ A -> x ∈ M -> F x = H x := by
  have hdom : forall x, x ∈ modelIntersectionZF M A -> x ∈ A := by
    intro x hx
    exact (mem_modelIntersectionZF_iff.mp hx).2
  have hdomainClosed : forall ⦃x⦄, x ∈ modelIntersectionZF M A ->
      forall ⦃y⦄, ClassRel R y x ->
        y ∈ modelIntersectionZF M A := by
    intro x hx y hyx
    have hxM : x ∈ M := (mem_modelIntersectionZF_iff.mp hx).1
    have hyA : y ∈ A := hrelation.left_mem hyx
    have hyM : y ∈ M := hclosedIn x hxM y hyA hyx
    exact mem_modelIntersectionZF_iff.mpr ⟨hyM, hyA⟩
  have hagree := recursionSolutions_agreeOn hmin hdom hdomainClosed
    (fun x hx => hpredecessors x (hdom x hx)) hF hH
  intro x hxA hxM
  exact hagree x (mem_modelIntersectionZF_iff.mpr ⟨hxM, hxA⟩)

end

end Constructible
