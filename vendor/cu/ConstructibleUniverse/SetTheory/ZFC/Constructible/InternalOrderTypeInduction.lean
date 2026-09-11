/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeStep

/-!
# Well-founded induction for internal order types

The local order-type step is iterated along the universe-small presentation
of an internally represented well-order.  Every point therefore receives its
canonical von Neumann ordinal together with an actual predecessor set and an
actual order-isomorphism graph in `L`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Moving between small points and internal points -/

/-- Turn a point of the small carrier back into an internal member. -/
noncomputable def smallPointLCarrier
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    LCarrier.{u} :=
  rawMemberLCarrier domain
    ((equivShrink (ZFCarrier domain.1)).symm point)

theorem smallPointLCarrier_mem
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    (smallPointLCarrier domain point).1 ∈ domain.1 :=
  ((equivShrink (ZFCarrier domain.1)).symm point).2

@[simp]
theorem smallMember_smallPointLCarrier
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    smallMember domain (smallPointLCarrier domain point)
        (smallPointLCarrier_mem domain point) = point := by
  simp [smallMember, smallPointLCarrier]

@[simp]
theorem smallPointLCarrier_smallMember
    (domain x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    smallPointLCarrier domain (smallMember domain x hx) = x := by
  apply Subtype.ext
  simp [smallPointLCarrier, smallMember]

/-! ## The induction theorem -/

/-- Every point of an internally represented well-order has its canonical
internally represented initial-segment order type. -/
theorem canonicalMemberOrderType_isInitial
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (point : LCarrier.{u}) (hpoint : point.1 ∈ domain.1) :
    IsInitialSegmentOrderType LMem relation domain point
      (canonicalMemberOrderTypeLCarrier
        relation domain hwell point hpoint) := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  let wellFounded : WellFounded (smallGraphRel relation domain) :=
    IsWellFounded.wf
  have hall : forall small : SmallZFCarrier domain.1,
      forall z : LCarrier.{u}, forall hz : z.1 ∈ domain.1,
        smallMember domain z hz = small ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz) := by
    intro small
    apply wellFounded.induction small
    intro current ih z hz hzCurrent
    apply canonicalMemberOrderType_isInitial_of_predecessors
      relation domain z hwell hz
    intro predecessor hpredecessor hpredecessorZ
    have hbelowRaw := (smallGraphRel_smallMember_iff
      relation domain predecessor z hpredecessor hz).mpr hpredecessorZ
    have hbelow : smallGraphRel relation domain
        (smallMember domain predecessor hpredecessor) current := by
      simpa only [hzCurrent] using hbelowRaw
    exact ih (smallMember domain predecessor hpredecessor) hbelow
      predecessor hpredecessor rfl
  let pointSmall := smallMember domain point hpoint
  exact hall pointSmall point hpoint rfl

end

end Constructible.ContinuumFormula
