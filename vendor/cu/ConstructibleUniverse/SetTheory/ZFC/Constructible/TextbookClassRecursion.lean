/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassWellFounded

/-!
# Textbook recursion on a well-founded set-like class relation

This file formalizes the recursion theorem of Section 6.1 in Wang Fangting,
*Axiomatic Set Theory*.  The hypotheses are the textbook hypotheses:
`R` is a relation on `A`, every nonempty actual set contained in `A` has an
`R`-minimal member, and every predecessor class is represented by an actual
`ZFSet`.

The construction uses `wellFounded_classRel_zfSubtype`, which was derived
from precisely those hypotheses by the preceding textbook closure and
class-minimum arguments.  Lean's `WellFounded.fix` below merely implements
the induction supplied by that derived theorem; global `WellFounded` is not
an additional assumption.

For every `x in A`, the second argument passed to `step` is the actual
Kuratowski graph

`{ <y,F(y)> | y R x } : ZFSet`,

constructed by `predecessorRestrictionGraph` over the displayed predecessor
set.  This is an ambient `ZFSet` statement.  It does not assert that the graph
belongs to a particular inner model.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## The recursive construction -/

/-- The temporary total function used when forming the predecessor graph at
`x`.  On an `R`-predecessor it returns the already constructed value; away
from the predecessor relation it is totalized by the empty set.  Only its
values on `displayedPredecessors` enter the graph. -/
noncomputable def textbookClassRecursionPrevious
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (x : {z : ZFSet.{u} // z ∈ A})
    (previous : forall y : {z : ZFSet.{u} // z ∈ A},
      ClassRel R y.1 x.1 -> ZFSet.{u})
    (y : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hyx : ClassRel R y x.1 then
    previous ⟨y, hrelation.left_mem hyx⟩ hyx
  else
    ∅

/-- The induction step supplied to the derived well-founded induction on
the subtype `A`.  Its graph argument is an actual `ZFSet`. -/
noncomputable def textbookClassRecursionFunctional
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (x : {z : ZFSet.{u} // z ∈ A})
    (previous : forall y : {z : ZFSet.{u} // z ∈ A},
      ClassRel R y.1 x.1 -> ZFSet.{u}) : ZFSet.{u} :=
  step x.1 <| predecessorRestrictionGraph
    (displayedPredecessors A R hR.2.2 x.1)
    (textbookClassRecursionPrevious hR.1 x previous)

/-- The recursively constructed function on the subtype `A`.

`WellFounded.fix` is used only with the relation obtained from
`wellFounded_classRel_zfSubtype hR`; it therefore implements the induction
already proved from the textbook set-minimum and set-likeness hypotheses. -/
noncomputable def textbookClassRecursionOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    {z : ZFSet.{u} // z ∈ A} -> ZFSet.{u} :=
  (wellFounded_classRel_zfSubtype hR).fix
    (textbookClassRecursionFunctional hR step)

/-- The textbook recursive function, totalized by `empty` away from `A`.
The off-domain value has no mathematical role in the recursion theorem. -/
noncomputable def textbookClassRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ A then
    textbookClassRecursionOn hR step ⟨x, hx⟩
  else
    ∅

/-- The exact recursion equation used in the textbook theorem.  In
particular, `displayedPredecessors` is an actual set representing the full
predecessor class. -/
def SatisfiesTextbookClassRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) : Prop :=
  forall x, x ∈ A ->
    F x = step x (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike x) F)

@[simp]
theorem textbookClassRecursion_eq_empty_of_not_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∉ A) :
    textbookClassRecursion hR step x = ∅ := by
  simp [textbookClassRecursion, hx]

@[simp]
theorem textbookClassRecursion_eq_on
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    textbookClassRecursion hR step x =
      textbookClassRecursionOn hR step ⟨x, hx⟩ := by
  simp [textbookClassRecursion, hx]

/-- The defining equation on the subtype.  The graph produced inside
`WellFounded.fix` is extensionally equal to the graph of the final totalized
function because every displayed predecessor lies in `A` and is smaller
than the current argument. -/
theorem textbookClassRecursionOn_eq
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (x : {z : ZFSet.{u} // z ∈ A}) :
    textbookClassRecursionOn hR step x =
      step x.1 (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x.1)
        (textbookClassRecursion hR step)) := by
  rw [textbookClassRecursionOn, WellFounded.fix_eq]
  unfold textbookClassRecursionFunctional
  apply congrArg (step x.1)
  apply predecessorRestrictionGraph_congr
  intro y hy
  have hySpec := (displayedPredecessors_spec hR.2.2 x.2 y).mp hy
  have hyA : y ∈ A := hySpec.1
  have hyx : ClassRel R y x.1 := hySpec.2
  rw [textbookClassRecursionPrevious]
  simp only [dif_pos hyx]
  change textbookClassRecursionOn hR step ⟨y, _⟩ =
    textbookClassRecursion hR step y
  rw [textbookClassRecursion_eq_on hR step hyA]

/-- The constructed total function satisfies the exact recursion equation
at every point of `A`. -/
theorem textbookClassRecursion_satisfies
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    SatisfiesTextbookClassRecursion A R hR.2.2 step
      (textbookClassRecursion hR step) := by
  intro x hx
  rw [textbookClassRecursion_eq_on hR step hx]
  exact textbookClassRecursionOn_eq hR step ⟨x, hx⟩

/-! ## Uniqueness -/

/-- Two solutions of the textbook recursion equation agree throughout `A`.
The induction relation here is not assumed globally well-founded: it is the
one derived by `wellFounded_classRel_zfSubtype` from the textbook hypotheses. -/
theorem satisfiesTextbookClassRecursion_uniqueOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hF : SatisfiesTextbookClassRecursion A R hR.2.2 step F)
    (hH : SatisfiesTextbookClassRecursion A R hR.2.2 step H) :
    forall x, x ∈ A -> F x = H x := by
  intro x hx
  by_contra hxNe
  let bad : Set ZFSet.{u} := {z | z ∈ A ∧ Not (F z = H z)}
  have hbadSubset : bad ⊆ A := by
    intro z hz
    exact hz.1
  have hbadNonempty : bad.Nonempty := ⟨x, hx, hxNe⟩
  rcases hasClassMinimaOn_of_isWellFoundedSetLikeOn hR bad
      hbadSubset hbadNonempty with ⟨z, hzBad, hzMinimal⟩
  have hzEq : F z = H z := by
    rw [hF z hzBad.1, hH z hzBad.1]
    apply congrArg (step z)
    apply predecessorRestrictionGraph_congr
    intro y hy
    have hySpec :=
      (displayedPredecessors_spec hR.2.2 hzBad.1 y).mp hy
    by_contra hyNe
    exact hzMinimal y ⟨hySpec.1, hyNe⟩ hySpec.2
  exact hzBad.2 hzEq

/-- Existence and uniqueness on `A` in one theorem.  Uniqueness is
pointwise on the intended class domain, as in the textbook statement; values
chosen by other totalizations outside `A` are irrelevant. -/
theorem exists_uniqueOn_satisfiesTextbookClassRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    exists F : ZFSet.{u} -> ZFSet.{u},
      SatisfiesTextbookClassRecursion A R hR.2.2 step F ∧
      forall H : ZFSet.{u} -> ZFSet.{u},
        SatisfiesTextbookClassRecursion A R hR.2.2 step H ->
        forall x, x ∈ A -> F x = H x := by
  refine ⟨textbookClassRecursion hR step,
    textbookClassRecursion_satisfies hR step, ?_⟩
  intro H hH
  exact satisfiesTextbookClassRecursion_uniqueOn hR
    (textbookClassRecursion_satisfies hR step) hH

end

end Constructible
