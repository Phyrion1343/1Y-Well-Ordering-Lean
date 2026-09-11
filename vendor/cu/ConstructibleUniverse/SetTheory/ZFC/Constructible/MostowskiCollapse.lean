/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Mostowski collapse for set-sized membership structures

This file develops the external collapse of membership restricted to a
`ZFSet`.  The recursion is along genuine well-founded membership, while each
recursive image is again packaged as a `ZFSet`.
-/

@[expose] public section

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

/-- The collapse of `x`, using only predecessors which belong to `domain`. -/
noncomputable def collapse (domain x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun y : {y : ZFSet.{u} // y ∈ x ∩ domain} =>
    collapse domain y.1
termination_by x
decreasing_by
  exact (ZFSet.mem_inter.mp y.2).1

/-- Membership in the collapse is exactly membership through a predecessor
which lies in the restricted domain. -/
@[simp]
theorem mem_collapse_iff {domain x z : ZFSet.{u}} :
    z ∈ collapse domain x ↔
      ∃ y : ZFSet.{u}, y ∈ x ∧ y ∈ domain ∧ collapse domain y = z := by
  rw [collapse, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y, hy⟩, hvalue⟩
    exact ⟨y, (ZFSet.mem_inter.mp hy).1,
      (ZFSet.mem_inter.mp hy).2, hvalue⟩
  · rintro ⟨y, hyx, hydomain, hvalue⟩
    exact ⟨⟨y, ZFSet.mem_inter.mpr ⟨hyx, hydomain⟩⟩, hvalue⟩

/-- The transitive target of the collapse. -/
noncomputable def range (domain : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    collapse domain x.1

@[simp]
theorem mem_range_iff {domain z : ZFSet.{u}} :
    z ∈ range domain ↔
      ∃ x : ZFSet.{u}, x ∈ domain ∧ collapse domain x = z := by
  rw [range, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, hvalue⟩
    exact ⟨x, hx, hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨⟨x, hx⟩, hvalue⟩

/-- The range of the collapse is transitive, independently of
extensionality of the restricted structure. -/
theorem range_isTransitive (domain : ZFSet.{u}) :
    (range domain).IsTransitive := by
  intro z hz w hw
  rcases mem_range_iff.mp hz with ⟨x, hxdomain, rfl⟩
  rcases mem_collapse_iff.mp hw with
    ⟨y, _hyx, hydomain, hvalue⟩
  exact mem_range_iff.mpr ⟨y, hydomain, hvalue⟩

/-- Extensionality of membership after both arguments and all predecessors
are restricted to `domain`. -/
def IsExtensional (domain : ZFSet.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain →
    ∀ ⦃y : ZFSet.{u}⦄, y ∈ domain →
      (∀ z : ZFSet.{u}, z ∈ domain → (z ∈ x ↔ z ∈ y)) → x = y

/-- Extensionality of the restricted membership structure makes the collapse
injective on its domain. -/
theorem collapse_eq_imp_eq_of_mem {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    ∀ x : ZFSet.{u}, x ∈ domain →
      ∀ y : ZFSet.{u}, y ∈ domain →
        collapse domain x = collapse domain y → x = y := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ domain →
      ∀ y : ZFSet.{u}, y ∈ domain →
        collapse domain x = collapse domain y → x = y)
    x ?_
  intro x ih hxdomain y hydomain hcollapse
  apply hextensional hxdomain hydomain
  intro z hzdomain
  constructor
  · intro hzx
    have hzCollapse : collapse domain z ∈ collapse domain x :=
      mem_collapse_iff.mpr ⟨z, hzx, hzdomain, rfl⟩
    rw [hcollapse] at hzCollapse
    rcases mem_collapse_iff.mp hzCollapse with
      ⟨w, hwy, hwdomain, hwz⟩
    have hzw : z = w :=
      ih z hzx hzdomain w hwdomain hwz.symm
    simpa only [hzw] using hwy
  · intro hzy
    have hzCollapse : collapse domain z ∈ collapse domain y :=
      mem_collapse_iff.mpr ⟨z, hzy, hzdomain, rfl⟩
    rw [← hcollapse] at hzCollapse
    rcases mem_collapse_iff.mp hzCollapse with
      ⟨w, hwx, hwdomain, hwz⟩
    have hwz' : w = z :=
      ih w hwx hwdomain z hzdomain hwz
    simpa only [hwz'] using hwx

/-- Function-injectivity formulation of `collapse_eq_imp_eq_of_mem`. -/
theorem collapse_injective_on {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    Function.Injective
      (fun x : {x : ZFSet.{u} // x ∈ domain} => collapse domain x.1) := by
  intro x y hxy
  apply Subtype.ext
  exact collapse_eq_imp_eq_of_mem hextensional
    x.1 x.2 y.1 y.2 hxy

/-- The collapse map with its codomain restricted to the collapse range. -/
def toRange (domain : ZFSet.{u}) :
    {x : ZFSet.{u} // x ∈ domain} →
      {z : ZFSet.{u} // z ∈ range domain} :=
  fun x => ⟨collapse domain x.1,
    mem_range_iff.mpr ⟨x.1, x.2, rfl⟩⟩

@[simp]
theorem toRange_val (domain : ZFSet.{u})
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (toRange domain x).1 = collapse domain x.1 := rfl

theorem toRange_surjective (domain : ZFSet.{u}) :
    Function.Surjective (toRange domain) := by
  intro z
  rcases mem_range_iff.mp z.2 with ⟨x, hx, hvalue⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hvalue

theorem toRange_injective {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    Function.Injective (toRange domain) := by
  intro x y hxy
  apply Subtype.ext
  apply collapse_eq_imp_eq_of_mem hextensional x.1 x.2 y.1 y.2
  exact congrArg Subtype.val hxy

/-- The Mostowski equivalence between an extensional restricted membership
structure and its transitive collapse range. -/
noncomputable def equivRange {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain) :
    {x : ZFSet.{u} // x ∈ domain} ≃
      {z : ZFSet.{u} // z ∈ range domain} :=
  Equiv.ofBijective (toRange domain)
    ⟨toRange_injective hextensional, toRange_surjective domain⟩

@[simp]
theorem equivRange_apply {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (equivRange hextensional x).1 = collapse domain x.1 := rfl

/-- On an extensional restricted structure, the collapse preserves and
reflects membership. -/
theorem collapse_mem_collapse_iff {domain x y : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hxdomain : x ∈ domain) (_hydomain : y ∈ domain) :
    collapse domain x ∈ collapse domain y ↔ x ∈ y := by
  constructor
  · intro hcollapse
    rcases mem_collapse_iff.mp hcollapse with
      ⟨z, hzy, hzdomain, hzx⟩
    have hxz : x = z := collapse_eq_imp_eq_of_mem hextensional
      x hxdomain z hzdomain hzx.symm
    simpa only [hxz] using hzy
  · intro hxy
    exact mem_collapse_iff.mpr ⟨x, hxy, hxdomain, rfl⟩

@[simp]
theorem equivRange_mem_iff {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (x y : {x : ZFSet.{u} // x ∈ domain}) :
    (equivRange hextensional x).1 ∈ (equivRange hextensional y).1 ↔
      x.1 ∈ y.1 := by
  simp only [equivRange_apply]
  exact collapse_mem_collapse_iff hextensional x.2 y.2

/-- A transitive domain is extensional for its restricted membership
relation. -/
theorem isExtensional_of_isTransitive {domain : ZFSet.{u}}
    (htransitive : domain.IsTransitive) : IsExtensional domain := by
  intro x hxdomain y hydomain hext
  apply ZFSet.ext
  intro z
  constructor
  · intro hzx
    exact (hext z (htransitive.mem_trans hzx hxdomain)).mp hzx
  · intro hzy
    exact (hext z (htransitive.mem_trans hzy hydomain)).mpr hzy

/-- Collapsing an already transitive membership structure fixes each of its
elements. -/
theorem collapse_eq_self_of_mem {domain : ZFSet.{u}}
    (htransitive : domain.IsTransitive) :
    ∀ x : ZFSet.{u}, x ∈ domain → collapse domain x = x := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ domain → collapse domain x = x) x ?_
  intro x ih hxdomain
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, hydomain, hvalue⟩
    have hyz : y = z := (ih y hyx hydomain).symm.trans hvalue
    simpa only [hyz] using hyx
  · intro hzx
    have hzdomain : z ∈ domain :=
      htransitive.mem_trans hzx hxdomain
    exact ⟨z, hzx, hzdomain, ih z hzx hzdomain⟩

end

end Constructible.MostowskiCollapse
