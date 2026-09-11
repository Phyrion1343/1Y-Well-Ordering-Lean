/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassRecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalRecursion

/-!
# Bridge from the textbook local-graph proof to the class-recursion interface

`TextbookLocalRecursion` avoids importing the earlier fixpoint implementation,
so it states the recursion equation under a separate name.  This file proves
that the two predicates are definitionally the same and re-exports the
existence-and-uniqueness theorem through the established class-recursion
interface.  The existence proof below is the page-108 local-graph construction;
it does not invoke the earlier fixpoint existence theorem.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- The local-graph module and the class-recursion module state exactly the
same recursion equation. -/
theorem satisfiesTextbookGlobalRecursion_iff_classRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) :
    SatisfiesTextbookGlobalRecursion A R hsetLike step F <->
      SatisfiesTextbookClassRecursion A R hsetLike step F := by
  rfl

/-- The function assembled from the textbook local graphs satisfies the
established class-recursion predicate. -/
theorem textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    SatisfiesTextbookClassRecursion A R hR.2.2 step
      (textbookGlobalRecursionFromLocalGraphs hR step) :=
  (satisfiesTextbookGlobalRecursion_iff_classRecursion
    hR.2.2 step (textbookGlobalRecursionFromLocalGraphs hR step)).mp
      (textbookGlobalRecursionFromLocalGraphs_satisfies hR step)

/-- Existence and uniqueness for the established interface, with existence
proved by the literal local-domain, union, and top-pair construction. -/
theorem exists_uniqueOn_satisfiesTextbookClassRecursion_via_localGraphs
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    exists F : ZFSet.{u} -> ZFSet.{u},
      SatisfiesTextbookClassRecursion A R hR.2.2 step F /\
      forall H : ZFSet.{u} -> ZFSet.{u},
        SatisfiesTextbookClassRecursion A R hR.2.2 step H ->
        forall x, x ∈ A -> F x = H x := by
  refine
    ⟨textbookGlobalRecursionFromLocalGraphs hR step,
      textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion hR step,
      ?_⟩
  intro H hH
  apply satisfiesTextbookGlobalRecursion_uniqueOn hR
  · exact textbookGlobalRecursionFromLocalGraphs_satisfies hR step
  · exact (satisfiesTextbookGlobalRecursion_iff_classRecursion
      hR.2.2 step H).mpr hH

end

end Constructible
