/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookSetWellFounded
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFFunctionGraph

/-!
# The semantic core of textbook recursion absoluteness

This file packages the final part of Section 6.2, Theorem 2 of Wang Fangting,
*Axiomatic Set Theory*.  It assumes that the model-relative recursive solution
`H` has already been produced and represented by a formula, transports both
recursive equations to the same ambient step function, and applies the
minimal-counterexample theorem on `A intersect M`.

The missing model-internal recursion-existence theorem is not hidden in a
definition or discharged by an external Lean choice.  Its exact outputs remain
visible as the hypotheses `hH`, `hHclosed`, and `hHgraph` below.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-! ## Unary presentation of the existing absoluteness definition -/

/-- The unary spelling of function absoluteness.  The formula assignment is
`(x,y)`, with the output in the last coordinate. -/
def UnaryFunctionAbsoluteTo (M A : Set ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) (graph : FOFormula 2) : Prop :=
  (forall x, x ∈ M -> x ∈ A -> F x ∈ M) ∧
    forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn M graph (snoc ![x] y) <->
        x ∈ A ∧ y = F x)

/-- The unary spelling is exactly the existing tuple-based
`FunctionAbsoluteTo`, not a new or weaker notion. -/
theorem unaryFunctionAbsoluteTo_iff_functionAbsoluteTo
    {M A : Set ZFSet.{u}} {F : ZFSet.{u} -> ZFSet.{u}}
    {graph : FOFormula 2} :
    UnaryFunctionAbsoluteTo M A F graph <->
      FunctionAbsoluteTo M (UnaryTupleDomain A)
        (fun s : Tuple ZFSet.{u} 1 => F (s 0)) graph := by
  constructor
  · rintro ⟨hclosed, hgraph⟩
    constructor
    · intro s hsM hsA
      exact hclosed (s 0) (hsM 0) hsA
    · intro s y hsM hyM
      exact hgraph (s 0) y (hsM 0) hyM
  · rintro ⟨hclosed, hgraph⟩
    constructor
    · intro x hxM hxA
      let s : Tuple ZFSet.{u} 1 := ![x]
      have hsM : TupleIn M s := by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change x ∈ M
        exact hxM
      have hsA : s ∈ UnaryTupleDomain A := by
        change x ∈ A
        exact hxA
      have hvalue := hclosed s hsM hsA
      change F x ∈ M at hvalue
      exact hvalue
    · intro x y hxM hyM
      let s : Tuple ZFSet.{u} 1 := ![x]
      have hsM : TupleIn M s := by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change x ∈ M
        exact hxM
      have hsemantic := hgraph s y hsM hyM
      change
        (SatisfiesIn M graph (snoc ![x] y) <->
          x ∈ A ∧ y = F x) at hsemantic
      exact hsemantic

/-! ## The final minimal-counterexample step -/

/-- Once a formula-represented model solution `H` has been constructed and
both recursions have the same ambient equation, the ambient recursive function
`F` is absolute to `M`. -/
theorem unaryFunctionAbsoluteTo_of_recursiveModelSolution
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
      H x = step x (predecessorRestrictionGraph (predecessors x) H))
    (graph : FOFormula 2)
    (hHclosed : forall x, x ∈ M -> x ∈ A -> H x ∈ M)
    (hHgraph : forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) graph (snoc ![x] y) <->
        x ∈ A ∧ y = H x)) :
    UnaryFunctionAbsoluteTo (M : Set ZFSet.{u}) A F graph := by
  have hagree := recursionSolutions_agreeOn_modelIntersection
    hrelation hmin hpredecessors hclosedIn hF hH
  constructor
  · intro x hxM hxA
    rw [hagree x hxA hxM]
    exact hHclosed x hxM hxA
  · intro x y hxM hyM
    rw [hHgraph x y hxM hyM]
    constructor
    · rintro ⟨hxA, hyH⟩
      have hxAgree : F x = H x := hagree x hxA hxM
      exact ⟨hxA, hyH.trans hxAgree.symm⟩
    · rintro ⟨hxA, hyF⟩
      have hxAgree : F x = H x := hagree x hxA hxM
      exact ⟨hxA, hyF.trans hxAgree⟩

/-- Tuple-based restatement of the preceding theorem. -/
theorem functionAbsoluteTo_of_recursiveModelSolution
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
      H x = step x (predecessorRestrictionGraph (predecessors x) H))
    (graph : FOFormula 2)
    (hHclosed : forall x, x ∈ M -> x ∈ A -> H x ∈ M)
    (hHgraph : forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) graph (snoc ![x] y) <->
        x ∈ A ∧ y = H x)) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) (UnaryTupleDomain A)
      (fun s : Tuple ZFSet.{u} 1 => F (s 0)) graph := by
  apply unaryFunctionAbsoluteTo_iff_functionAbsoluteTo.mp
  exact unaryFunctionAbsoluteTo_of_recursiveModelSolution
    hrelation hmin hpredecessors hclosedIn hF hH graph
      hHclosed hHgraph

end

end Constructible.Model
