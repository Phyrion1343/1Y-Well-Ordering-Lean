/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentElementarity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiCollapse

/-!
# Mostowski collapse from finite-fragment closure

The distinguishing-member formula is the only elementarity fragment needed
to establish extensionality of a restricted membership structure.  This file
connects that fact to the set-sized Mostowski collapse.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-- A set-sized hull closed under distinguishing witnesses is extensional. -/
theorem mostowskiIsExtensional_of_closesWithin
    {domain : ZFSet.{u}} {big : Set ZFSet.{u}}
    (hsubset : (domain : Set ZFSet.{u}) ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithin (domain : Set ZFSet.{u}) big
      distinguishingMemberFormula) :
    MostowskiCollapse.IsExtensional domain := by
  intro x hx y hy hsame
  exact restricted_extensionality_of_closesWithin
    hsubset htrans hclose hx hy hsame

/-- The resulting collapse preserves and reflects membership on the hull. -/
theorem finiteFragmentCollapse_mem_iff
    {domain : ZFSet.{u}} {big : Set ZFSet.{u}}
    (hsubset : (domain : Set ZFSet.{u}) ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithin (domain : Set ZFSet.{u}) big
      distinguishingMemberFormula)
    {x y : ZFSet.{u}} (hx : x ∈ domain) (hy : y ∈ domain) :
    MostowskiCollapse.collapse domain x ∈
        MostowskiCollapse.collapse domain y <->
      x ∈ y := by
  exact MostowskiCollapse.collapse_mem_collapse_iff
    (mostowskiIsExtensional_of_closesWithin hsubset htrans hclose) hx hy

/-- The collapse map of the finite-fragment hull is an equivalence onto a
transitive `ZFSet`. -/
noncomputable def finiteFragmentCollapseEquiv
    {domain : ZFSet.{u}} {big : Set ZFSet.{u}}
    (hsubset : (domain : Set ZFSet.{u}) ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithin (domain : Set ZFSet.{u}) big
      distinguishingMemberFormula) :
    {x : ZFSet.{u} // x ∈ domain} ≃
      {z : ZFSet.{u} // z ∈ MostowskiCollapse.range domain} :=
  MostowskiCollapse.equivRange
    (mostowskiIsExtensional_of_closesWithin hsubset htrans hclose)

end ZFC

end Constructible
