/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Set-sized restriction graphs

This file contains the representation-neutral facts about the actual
Kuratowski graph of an external function restricted to an actual `ZFSet`.
It makes no assertion that the graph belongs to a particular model; that
additional fact must be obtained from that model's Replacement scheme.
-/

@[expose] public section

universe u

namespace Constructible

noncomputable section

/-- The actual Kuratowski graph of `f` restricted to the members of
`domain`. -/
noncomputable def predecessorRestrictionGraph
    (domain : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    ZFSet.pair x.1 (f x.1)

/-- Membership in the restriction graph has the expected semantics. -/
@[simp]
theorem mem_predecessorRestrictionGraph_iff
    {domain p : ZFSet.{u}} {f : ZFSet.{u} -> ZFSet.{u}} :
    p ∈ predecessorRestrictionGraph domain f <->
      exists x : ZFSet.{u}, x ∈ domain ∧
        ZFSet.pair x (f x) = p := by
  rw [predecessorRestrictionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨x, hx⟩, hp⟩

/-- Every domain member contributes its ordered pair. -/
theorem pair_mem_predecessorRestrictionGraph
    {domain x : ZFSet.{u}} (f : ZFSet.{u} -> ZFSet.{u})
    (hx : x ∈ domain) :
    ZFSet.pair x (f x) ∈ predecessorRestrictionGraph domain f := by
  exact mem_predecessorRestrictionGraph_iff.mpr ⟨x, hx, rfl⟩

/-- Pointwise agreement on the domain gives equality of the actual graphs. -/
theorem predecessorRestrictionGraph_congr
    {domain : ZFSet.{u}} {f g : ZFSet.{u} -> ZFSet.{u}}
    (hfg : forall x : ZFSet.{u}, x ∈ domain -> f x = g x) :
    predecessorRestrictionGraph domain f =
      predecessorRestrictionGraph domain g := by
  apply ZFSet.ext
  intro p
  simp only [mem_predecessorRestrictionGraph_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfg x hx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfg x hx]⟩

/-- Equality of graphs is equivalent to pointwise agreement on their common
domain. -/
theorem predecessorRestrictionGraph_eq_iff
    {domain : ZFSet.{u}} {f g : ZFSet.{u} -> ZFSet.{u}} :
    predecessorRestrictionGraph domain f =
        predecessorRestrictionGraph domain g <->
      forall x : ZFSet.{u}, x ∈ domain -> f x = g x := by
  constructor
  · intro hgraphs x hx
    have hp : ZFSet.pair x (f x) ∈
        predecessorRestrictionGraph domain g := by
      rw [← hgraphs]
      exact pair_mem_predecessorRestrictionGraph f hx
    rcases mem_predecessorRestrictionGraph_iff.mp hp with
      ⟨z, _hz, hz⟩
    have hcoordinates := ZFSet.pair_inj.mp hz
    simpa only [hcoordinates.1] using hcoordinates.2.symm
  · exact predecessorRestrictionGraph_congr

end

end Constructible
