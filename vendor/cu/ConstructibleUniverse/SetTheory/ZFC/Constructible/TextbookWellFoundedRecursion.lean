/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RestrictionGraph

/-!
# The uniqueness core of textbook well-founded recursion

This file isolates the semantic and uniqueness core used in Section 6.2,
Theorem 2 of Wang Fangting, *Axiomatic Set Theory*.

For an external function `f : ZFSet -> ZFSet` and an actual set `a` of
predecessors, `predecessorRestrictionGraph a f` is the actual `ZFSet`

`{ <y, f(y)> | y in a }`,

where ordered pairs are Kuratowski pairs.  Given an external domain `D`, an
actual predecessor set `pred x` at every point, and a recursion operator
`step`, the equation considered below is exactly

`f(x) = step x (f restricted to pred(x))`.

Under explicit predecessor closure and well-foundedness of the restricted
predecessor relation, two external functions satisfying this equation agree
on `D`.

This is not yet the textbook absoluteness theorem for recursion in a
transitive ZF model.  In particular, this file does not assert that a
restriction graph belongs to a given model, that `step` is absolute, or that
a solution of the recursion equation exists.  Those are separate model-
theoretic and internal-representation obligations.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Restricted recursion equations -/

/-- Every predecessor of a point of `domain` again belongs to `domain`.
This condition is deliberately separate from well-foundedness. -/
def PredecessorClosed (domain : Set ZFSet.{u})
    (pred : ZFSet.{u} -> ZFSet.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain ->
    ∀ ⦃y : ZFSet.{u}⦄, y ∈ pred x -> y ∈ domain

/-- The predecessor relation restricted to the displayed external domain.
Both endpoints are included explicitly; predecessor closure is what permits
an edge to be formed from membership in `pred x`. -/
def restrictedPredecessorRel (domain : Set ZFSet.{u})
    (pred : ZFSet.{u} -> ZFSet.{u}) (y x : ZFSet.{u}) : Prop :=
  x ∈ domain ∧ y ∈ domain ∧ y ∈ pred x

/-- The standard recursion equation on an external domain.  Its second
argument is an actual internal `ZFSet` graph, not an external `Set ZFSet`. -/
def SatisfiesRecursionEquationOn (domain : Set ZFSet.{u})
    (pred : ZFSet.{u} -> ZFSet.{u})
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (f : ZFSet.{u} -> ZFSet.{u}) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ domain ->
    f x = step x (predecessorRestrictionGraph (pred x) f)

/-- Uniqueness of solutions of the restricted well-founded recursion
equation.  This is only the semantic uniqueness argument: existence and all
model-absoluteness obligations remain explicit future hypotheses. -/
theorem satisfiesRecursionEquationOn_unique
    {domain : Set ZFSet.{u}} {pred : ZFSet.{u} -> ZFSet.{u}}
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {f g : ZFSet.{u} -> ZFSet.{u}}
    (hclosed : PredecessorClosed domain pred)
    (hwf : WellFounded (restrictedPredecessorRel domain pred))
    (hf : SatisfiesRecursionEquationOn domain pred step f)
    (hg : SatisfiesRecursionEquationOn domain pred step g) :
    ∀ x : ZFSet.{u}, x ∈ domain -> f x = g x := by
  intro x
  refine hwf.induction
    (C := fun x => x ∈ domain -> f x = g x) x ?_
  intro x ih hx
  rw [hf x hx, hg x hx]
  apply congrArg (step x)
  apply predecessorRestrictionGraph_congr
  intro y hy
  have hyDomain : y ∈ domain := hclosed hx hy
  exact ih y ⟨hx, hyDomain, hy⟩ hyDomain

end

end Constructible
