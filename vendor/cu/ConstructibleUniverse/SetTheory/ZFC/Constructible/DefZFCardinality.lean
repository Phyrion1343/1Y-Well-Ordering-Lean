/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationEnumeration
public import Mathlib.Data.List.OfFn
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of the definability operation

This file formalizes Proposition 1(I) of Section 6.8 of Wang Fangting,
*Axiomatic Set Theory*: if `a` is infinite, then `Def(a)` has the same
cardinality as `a`.

The upper bound is the textbook enumeration argument.  A definable subset is
specified by a natural-number formula code and a finite list of parameters
from `a`.  The lower bound sends each member of `a` to its singleton, which is
definable over `a`.

All cardinalities in this file are external cardinalities of the concrete
`ZFSet` objects.  In particular, this theorem does not assert the separate
Section 6.4 absoluteness theorem for an internally represented enumeration.
-/

@[expose] public section

open Set
open scoped Cardinal

universe u

namespace Constructible

noncomputable section

/-- A finite tuple together with its arity. -/
abbrev FiniteParameters (A : Type u) := Sigma fun n : Nat => Tuple A n

/--
The subset selected by one relation in the fixed-arity enumeration of
`Df E (n+1)` and a finite parameter list.  Invalid codes denote the empty
relation, exactly as in `definableRelationEnumerate`.
-/
def definableSubsetEnumerate {A : Type u} (E : A -> A -> Prop)
    (params : FiniteParameters A) (code : Nat) : Set A :=
  relSection
    (definableRelationEnumerate E (params.1 + 1) code).1
    params.2

/-- Every value of `definableSubsetEnumerate` is a definable subset. -/
theorem definableSubsetEnumerate_mem {A : Type u} (E : A -> A -> Prop)
    (params : FiniteParameters A) (code : Nat) :
    definableSubsetEnumerate E params code ∈ definablePowerset E := by
  exact ⟨params.1, params.2,
    (definableRelationEnumerate E (params.1 + 1) code).1,
    definableRelationEnumerate_mem_Df E (params.1 + 1) code, rfl⟩

/--
The external enumeration of the members of `DefZF a` by a finite parameter
list and a natural-number formula code.
-/
noncomputable def defZFEnumerate (a : ZFSet.{u}) :
    FiniteParameters (ZFCarrier a) × Nat -> ZFCarrier (DefZF a) :=
  fun input =>
    ⟨representZFSubset a
        (definableSubsetEnumerate (zfCarrierMem a) input.1 input.2),
      representZFSubset_mem_DefZF
        (definableSubsetEnumerate_mem (zfCarrierMem a) input.1 input.2)⟩

/-- Every definable subset occurs in the external enumeration. -/
theorem defZFEnumerate_surjective (a : ZFSet.{u}) :
    Function.Surjective (defZFEnumerate a) := by
  rintro ⟨z, hz⟩
  rcases (mem_DefZF_iff.mp hz) with
    ⟨hza, n, params, relation, hrelation, hsection⟩
  let relationDf : DefinableRelation (zfCarrierMem a) (n + 1) :=
    ⟨relation, hrelation⟩
  rcases definableRelationEnumerate_surjective
      (zfCarrierMem a) (n + 1) relationDf with ⟨code, hcode⟩
  have hrelationCode :
      (definableRelationEnumerate (zfCarrierMem a) (n + 1) code).1 =
        relation :=
    congrArg Subtype.val hcode
  refine ⟨(⟨n, params⟩, code), ?_⟩
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  change
    (x ∈ representZFSubset a
      (definableSubsetEnumerate (zfCarrierMem a) ⟨n, params⟩ code)) ↔
        x ∈ z
  rw [mem_representZFSubset_iff]
  simp only [definableSubsetEnumerate, hrelationCode, ← hsection,
    zfSubsetAsCarrier]
  constructor
  · rintro ⟨_hxa, hxz⟩
    exact hxz
  · intro hxz
    exact ⟨hza hxz, hxz⟩

/-- The singleton map embeds the carrier of `a` into the carrier of `DefZF a`. -/
def singletonDefZFEmbedding (a : ZFSet.{u}) :
    ZFCarrier a ↪ ZFCarrier (DefZF a) where
  toFun x :=
    ⟨({x.1} : ZFSet.{u}), by
      simpa only [ZFSet.pair_eq_singleton] using
        (pair_mem_DefZF x.2 x.2)⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact ZFSet.singleton_injective (congrArg Subtype.val hxy)

/-- The textbook singleton argument gives `|a| <= |DefZF a|`. -/
theorem card_le_card_DefZF (a : ZFSet.{u}) :
    a.card <= (DefZF a).card := by
  have h := (singletonDefZFEmbedding a).cardinal_le
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_le] using h

/-- For every `a`, the textbook enumeration bounds `DefZF a` by the maximum
of `aleph0` and the cardinality of `a`. -/
theorem card_DefZF_le_max (a : ZFSet.{u}) :
    (DefZF a).card <= max Cardinal.aleph0 a.card := by
  have hsurj : #(ZFCarrier (DefZF a)) <=
      #(FiniteParameters (ZFCarrier a) × Nat) :=
    Cardinal.mk_le_of_surjective (defZFEnumerate_surjective a)
  have hparameters : #(FiniteParameters (ZFCarrier a)) =
      #(List (ZFCarrier a)) :=
    (List.equivSigmaTuple (α := ZFCarrier a)).cardinal_eq.symm
  have hsource : #(FiniteParameters (ZFCarrier a) × Nat) <=
      max Cardinal.aleph0 #(ZFCarrier a) := by
    calc
      #(FiniteParameters (ZFCarrier a) × Nat) =
          #(FiniteParameters (ZFCarrier a)) * Cardinal.aleph0 := by
        rw [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat,
          Cardinal.lift_aleph0]
      _ = #(List (ZFCarrier a)) * Cardinal.aleph0 := by
        rw [hparameters]
      _ <= max Cardinal.aleph0 #(ZFCarrier a) * Cardinal.aleph0 :=
        mul_le_mul' (Cardinal.mk_list_le_max (ZFCarrier a)) le_rfl
      _ = max Cardinal.aleph0 #(ZFCarrier a) :=
        Cardinal.mul_aleph0_eq (le_max_left _ _)
  have hcarrier : #(ZFCarrier (DefZF a)) <=
      max Cardinal.aleph0 #(ZFCarrier a) :=
    hsurj.trans hsource
  refine Cardinal.lift_le.{u + 1, u}.mp ?_
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_max,
    Cardinal.lift_aleph0] using hcarrier

/-- For infinite `a`, the enumeration gives `|DefZF a| <= |a|`. -/
theorem card_DefZF_le_of_aleph0_le {a : ZFSet.{u}}
    (ha : Cardinal.aleph0 <= a.card) :
    (DefZF a).card <= a.card := by
  exact (card_DefZF_le_max a).trans_eq (max_eq_right ha)

/--
For every infinite `a`, `DefZF a` and `a` have exactly the same external
cardinality.  This is Section 6.8, Proposition 1(I), for the hierarchy's
definability operation.
-/
theorem card_DefZF_eq_of_aleph0_le {a : ZFSet.{u}}
    (ha : Cardinal.aleph0 <= a.card) :
    (DefZF a).card = a.card :=
  le_antisymm (card_DefZF_le_of_aleph0_le ha) (card_le_card_DefZF a)

end

end Constructible
