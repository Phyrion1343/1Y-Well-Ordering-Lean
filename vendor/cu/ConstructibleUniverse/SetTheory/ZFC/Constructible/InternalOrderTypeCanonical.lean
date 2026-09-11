/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentatives

/-!
# Canonical external order types for internally represented well-orders

This file identifies the canonical ordinal attached to each point of an
internally represented well-order.  The construction uses `Ordinal.typein`
only as an external mathematical reference.  It does not claim that the
ordinal or its isomorphism graph is already represented inside `L`; those are
the subsequent Separation and Replacement obligations.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

/-! ## Points in the small presentation -/

/-- A member of an internal set, transported to its universe-small carrier. -/
noncomputable def smallMember (domain x : LCarrier.{u})
    (hx : x.1 ∈ domain.1) :
    SmallZFCarrier domain.1 :=
  equivShrink (ZFCarrier domain.1) ⟨x.1, hx⟩

@[simp]
theorem smallGraphRel_smallMember_iff
    (relation domain x y : LCarrier.{u})
    (hx : x.1 ∈ domain.1) (hy : y.1 ∈ domain.1) :
    smallGraphRel relation domain (smallMember domain x hx)
        (smallMember domain y hy) ↔
      GraphRel relation x y := by
  simpa only [smallGraphRel, smallMember, InvImage,
    Equiv.symm_apply_apply, rawMemberLCarrier, GraphRel] using
      (rawGraphRel_iff_graphRel relation domain
        ⟨x.1, hx⟩ ⟨y.1, hy⟩)

/-! ## Canonical order types -/

/-- The external ordinal type of an internally represented well-order. -/
noncomputable def canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) : Ordinal.{u} := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.type (smallGraphRel relation domain)

/-- The constructible von Neumann code of the whole canonical order type. -/
noncomputable def canonicalOrderTypeLCarrier
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) : LCarrier.{u} :=
  ordinalLCarrier (canonicalOrderType relation domain hwell)

theorem canonicalOrderTypeLCarrier_isVonNeumannOrdinal
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem
      (canonicalOrderTypeLCarrier relation domain hwell) := by
  apply (isVonNeumannOrdinal_lCarrier_iff _).mpr
  exact ZFSet.isOrdinal_toZFSet _

/-- The external order type of the strict initial segment below `x`. -/
noncomputable def canonicalMemberOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) : Ordinal.{u} := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.typein (smallGraphRel relation domain)
    (smallMember domain x hx)

/-- The von Neumann set code of the canonical initial-segment type.  This is
an element of `L` because every ordinal is constructible.  No function graph
is asserted at this point. -/
noncomputable def canonicalMemberOrderTypeLCarrier
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) : LCarrier.{u} :=
  ordinalLCarrier (canonicalMemberOrderType relation domain hwell x hx)

theorem canonicalMemberOrderTypeLCarrier_isVonNeumannOrdinal
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem
      (canonicalMemberOrderTypeLCarrier relation domain hwell x hx) := by
  apply (isVonNeumannOrdinal_lCarrier_iff _).mpr
  exact ZFSet.isOrdinal_toZFSet _

/-- Canonical initial-segment types preserve and reflect the represented
strict order. -/
theorem canonicalMemberOrderType_lt_iff
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1) :
    canonicalMemberOrderType relation domain hwell x hx <
        canonicalMemberOrderType relation domain hwell y hy ↔
      GraphRel relation x y := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  change Ordinal.typein (smallGraphRel relation domain)
      (smallMember domain x hx) <
        Ordinal.typein (smallGraphRel relation domain)
          (smallMember domain y hy) ↔ _
  rw [Ordinal.typein_lt_typein]
  exact smallGraphRel_smallMember_iff relation domain x y hx hy

/-- Membership between the von Neumann codes of canonical point types is
exactly the represented source order. -/
theorem canonicalMemberOrderTypeLCarrier_mem_iff
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1) :
    (canonicalMemberOrderTypeLCarrier relation domain hwell x hx).1 ∈
        (canonicalMemberOrderTypeLCarrier relation domain hwell y hy).1 ↔
      GraphRel relation x y := by
  rw [canonicalMemberOrderTypeLCarrier,
    canonicalMemberOrderTypeLCarrier,
    ordinalLCarrier_mem_ordinalLCarrier_iff,
    canonicalMemberOrderType_lt_iff relation domain hwell x y hx hy]

/-- Distinct points of the represented well-order have distinct canonical
initial-segment types. -/
theorem canonicalMemberOrderType_injective
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1)
    (hxy : canonicalMemberOrderType relation domain hwell x hx =
      canonicalMemberOrderType relation domain hwell y hy) :
    x = y := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  have hsmall : smallMember domain x hx = smallMember domain y hy := by
    apply Ordinal.typein_injective (smallGraphRel relation domain)
    exact hxy
  apply Subtype.ext
  have hraw :
      (⟨x.1, hx⟩ : ZFCarrier domain.1) = ⟨y.1, hy⟩ := by
    simpa only [smallMember, Equiv.symm_apply_apply] using congrArg
      (equivShrink (ZFCarrier domain.1)).symm hsmall
  exact congrArg (fun z : ZFCarrier domain.1 => z.1) hraw

/-- Every point type lies below the type of the whole represented order. -/
theorem canonicalMemberOrderType_lt_canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    canonicalMemberOrderType relation domain hwell x hx <
      canonicalOrderType relation domain hwell := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.typein_lt_type (smallGraphRel relation domain)
    (smallMember domain x hx)

/-- Every canonical point type is a member of the whole order-type code. -/
theorem canonicalMemberOrderTypeLCarrier_mem_canonicalOrderTypeLCarrier
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    (canonicalMemberOrderTypeLCarrier relation domain hwell x hx).1 ∈
      (canonicalOrderTypeLCarrier relation domain hwell).1 := by
  apply (ordinalLCarrier_mem_ordinalLCarrier_iff _ _).mpr
  exact canonicalMemberOrderType_lt_canonicalOrderType
    relation domain hwell x hx

/-- Every ordinal below the type of the whole order is the canonical type of
some member of the internal domain. -/
theorem exists_member_canonicalOrderType_eq_of_lt
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    {alpha : Ordinal.{u}}
    (halpha : alpha < canonicalOrderType relation domain hwell) :
    exists x : LCarrier.{u}, exists hx : x.1 ∈ domain.1,
      canonicalMemberOrderType relation domain hwell x hx = alpha := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  change alpha < Ordinal.type (smallGraphRel relation domain) at halpha
  rcases Ordinal.typein_surj (smallGraphRel relation domain) halpha with
    ⟨small, hsmall⟩
  let raw : ZFCarrier domain.1 :=
    (equivShrink (ZFCarrier domain.1)).symm small
  let x : LCarrier.{u} := rawMemberLCarrier domain raw
  have hx : x.1 ∈ domain.1 := raw.2
  refine ⟨x, hx, ?_⟩
  change Ordinal.typein (smallGraphRel relation domain)
      (smallMember domain x hx) = alpha
  have hpoint : smallMember domain x hx = small := by
    apply (equivShrink (ZFCarrier domain.1)).symm.injective
    simp only [smallMember, Equiv.symm_apply_apply]
    change (⟨x.1, hx⟩ : ZFCarrier domain.1) = raw
    apply Subtype.ext
    rfl
  rw [hpoint]
  exact hsmall

/-- Every ordinal below the canonical type at `bound` is represented by a
unique predecessor of `bound`.  This is the surjectivity fact used in the
standard order-type induction. -/
theorem exists_predecessor_canonicalMemberOrderType_eq_of_lt
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (bound : LCarrier.{u}) (hbound : bound.1 ∈ domain.1)
    {alpha : Ordinal.{u}}
    (halpha : alpha <
      canonicalMemberOrderType relation domain hwell bound hbound) :
    exists x : LCarrier.{u}, exists hx : x.1 ∈ domain.1,
      GraphRel relation x bound /\
        canonicalMemberOrderType relation domain hwell x hx = alpha := by
  have halphaWhole : alpha < canonicalOrderType relation domain hwell :=
    halpha.trans
      (canonicalMemberOrderType_lt_canonicalOrderType
        relation domain hwell bound hbound)
  rcases exists_member_canonicalOrderType_eq_of_lt
      relation domain hwell halphaWhole with ⟨x, hx, htype⟩
  refine ⟨x, hx, ?_, htype⟩
  apply (canonicalMemberOrderType_lt_iff
    relation domain hwell x bound hx hbound).mp
  simpa only [htype] using halpha

end Constructible.ContinuumFormula
