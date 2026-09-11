/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentativeInterface
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeInduction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem

/-!
# Constructing the internal order-type witness

The pointwise well-founded induction is assembled into the explicit
`InternalOrderTypeWitness` required by the cardinal-representative interface.
The target is the ordinary order type of the universe-small presentation,
represented by its von Neumann code in `L`.  The formula
`memberOrderTypeRelation` is proved total, bounded, single-valued, injective,
and onto that target.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The canonical point order type lies in the canonical order type of the
whole represented well-order. -/
theorem canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    (canonicalMemberOrderTypeLCarrier
      relation domain hwell x hx).1 ∈
        (ordinalLCarrier
          (canonicalOrderType relation domain hwell)).1 := by
  exact (ordinalLCarrier_mem_ordinalLCarrier_iff _ _).mpr
    (canonicalMemberOrderType_lt_canonicalOrderType
      relation domain hwell x hx)

/-- An internally represented well-order supplies the complete order-type
witness needed to build its internal bijection with an ordinal. -/
noncomputable def canonicalInternalOrderTypeWitness
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    InternalOrderTypeWitness relation domain where
  ordinal := ordinalLCarrier (canonicalOrderType relation domain hwell)
  ordinal_spec := by
    apply (isVonNeumannOrdinal_lCarrier_iff _).mpr
    exact ZFSet.isOrdinal_toZFSet _
  total := by
    intro x hx
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hx
    refine ⟨value,
      canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
        relation domain hwell x hx, ?_⟩
    apply (satisfies_memberOrderTypeRelation
      relation domain x value).mpr
    exact ⟨hx,
      canonicalMemberOrderType_isInitial
        relation domain hwell x hx⟩
  bounded := by
    intro x y hx hformula
    have hySegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hformula |>.2
    have hcanonical := canonicalMemberOrderType_isInitial
      relation domain hwell x hx
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx :=
      hySegment.ordinal_unique hcanonical
    rw [hyEq]
    exact canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
      relation domain hwell x hx
  unique := by
    intro x y z _hx _hy _hz hyFormula hzFormula
    have hySegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hyFormula |>.2
    have hzSegment := (satisfies_memberOrderTypeRelation
      relation domain x z).mp hzFormula |>.2
    exact hySegment.ordinal_unique hzSegment
  injective := by
    intro x z y hx hz _hy hxFormula hzFormula
    have hxSegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hxFormula |>.2
    have hzSegment := (satisfies_memberOrderTypeRelation
      relation domain z y).mp hzFormula |>.2
    have hxCanonical := canonicalMemberOrderType_isInitial
      relation domain hwell x hx
    have hzCanonical := canonicalMemberOrderType_isInitial
      relation domain hwell z hz
    have hyEqX : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx :=
      hxSegment.ordinal_unique hxCanonical
    have hyEqZ : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell z hz :=
      hzSegment.ordinal_unique hzCanonical
    apply canonicalMemberOrderTypeLCarrier_injective
      relation domain hwell x z hx hz
    exact hyEqX.symm.trans hyEqZ
  onto := by
    intro y hy
    have hyOrdinal : y.1 ∈
        (canonicalOrderType relation domain hwell).toZFSet := by
      exact hy
    rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
      ⟨beta, hbeta, hbetaValue⟩
    rcases exists_member_canonicalOrderType_eq_of_lt
        relation domain hwell hbeta with
      ⟨x, hx, hxType⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx := by
      apply Subtype.ext
      change y.1 =
        (canonicalMemberOrderType relation domain hwell x hx).toZFSet
      rw [hxType]
      exact hbetaValue.symm
    refine ⟨x, hx, ?_⟩
    apply (satisfies_memberOrderTypeRelation
      relation domain x y).mpr
    refine ⟨hx, ?_⟩
    rw [hyEq]
    exact canonicalMemberOrderType_isInitial
      relation domain hwell x hx

/-- Internal well-orderability now gives internal cardinal representatives,
with no additional order-type-recursion hypothesis. -/
theorem hasInternalCardinalRepresentatives_of_modelsInternalWellOrdering
    (hwellOrder : ModelsInternalWellOrdering.{u}) :
    HasInternalCardinalRepresentatives.{u} := by
  apply hasInternalCardinalRepresentatives_of_orderTypeWitness
  intro domain
  rcases hwellOrder domain with ⟨relation, hwell⟩
  exact ⟨relation, hwell,
    ⟨canonicalInternalOrderTypeWitness relation domain hwell⟩⟩

/-- The recursively constructed stage well-orders yield internal cardinal
representatives for every constructible set. -/
theorem hasInternalCardinalRepresentatives_lCarrier :
    HasInternalCardinalRepresentatives.{u} :=
  hasInternalCardinalRepresentatives_of_modelsInternalWellOrdering
    (Constructible.Model.modelsInternalWellOrdering_of_allStages
      Constructible.Model.allStagesInternallyWellOrdered_of_historyData)

end

end Constructible.ContinuumFormula
