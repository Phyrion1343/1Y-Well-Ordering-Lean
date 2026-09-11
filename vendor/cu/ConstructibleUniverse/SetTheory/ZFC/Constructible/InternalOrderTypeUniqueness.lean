/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentatives

/-!
# Uniqueness of internally represented order types

An internal order-isomorphism is represented by an actual Kuratowski graph
in `L`.  This file forgets only the representation proofs after that graph
has been supplied, transports the represented isomorphism to the universe-
small carriers, and compares their ordinary ordinal types.

In particular, two internal von Neumann ordinals which are represented as the
order type of the same initial segment are equal.  No ambient equivalence is
used as an internal witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Transporting an internal graph to the small carriers -/

/-- The canonical equivalence from the small presentation of a set to its
internal carrier. -/
noncomputable def smallToInternalCarrierEquiv (a : LCarrier.{u}) :
    SmallZFCarrier a.1 ≃ Constructible.Model.InternalCarrier a :=
  (equivShrink (ZFCarrier a.1)).symm.trans
    (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv a)

/-- Membership on an internal set, pulled back to its small carrier. -/
noncomputable def smallInternalMem (a : LCarrier.{u}) :
    SmallZFCarrier a.1 -> SmallZFCarrier a.1 -> Prop :=
  InvImage
    (fun x y : Constructible.Model.InternalCarrier a => LMem x.1 y.1)
    (smallToInternalCarrierEquiv a)

theorem smallInternalMem_ordinalLCarrier (alpha : Ordinal.{u}) :
    smallInternalMem (ordinalLCarrier alpha) = smallOrdinalMem alpha := by
  funext x y
  rfl

/-- The equality above, packaged as a relation isomorphism so that it can be
composed without dependent rewriting through `Ordinal.type`. -/
noncomputable def smallInternalMemOrdinalRelIso (alpha : Ordinal.{u}) :
    smallInternalMem (ordinalLCarrier alpha) ≃r smallOrdinalMem alpha where
  toEquiv := Equiv.refl _
  map_rel_iff' {x y} := by
    change smallOrdinalMem alpha x y <->
      smallInternalMem (ordinalLCarrier alpha) x y
    rw [smallInternalMem_ordinalLCarrier]

/-- The semantic equivalence selected from a represented bijection still
follows the represented graph. -/
theorem IsBijection.toEquiv_graphValue
    {graph domain codomain : LCarrier.{u}}
    (h : IsBijection LMem graph domain codomain)
    (x : Constructible.Model.InternalCarrier domain) :
    GraphValue LMem graph x.1 (h.toEquiv x).1 := by
  change GraphValue LMem graph x.1 (h.toIsInjection.toFun x).1
  exact h.toIsInjection.toFun_graphValue x

/-- A represented order-isomorphism induces an ordinary relation isomorphism
between the semantic internal carriers.  The represented graph remains the
source of the map. -/
noncomputable def IsOrderIsomorphism.toInternalRelIso
    {graph relation domain ordinal : LCarrier.{u}}
    (h : IsOrderIsomorphism LMem graph relation domain ordinal) :
    Constructible.Model.graphRelOn relation domain ≃r
      (fun x y : Constructible.Model.InternalCarrier ordinal =>
        LMem x.1 y.1) where
  toEquiv := h.1.toEquiv
  map_rel_iff' {x y} := by
    have hxValue : GraphValue LMem graph x.1 (h.1.toEquiv x).1 :=
      h.1.toEquiv_graphValue x
    have hyValue : GraphValue LMem graph y.1 (h.1.toEquiv y).1 :=
      h.1.toEquiv_graphValue y
    rw [show Constructible.Model.graphRelOn relation domain x y =
        Constructible.Model.GraphRel relation x.1 y.1 from rfl]
    rw [<- graphValue_lCarrier_iff_graphRel]
    exact (h.2 x.1 y.1 (h.1.toEquiv x).1 (h.1.toEquiv y).1
      x.2 y.2 hxValue hyValue).symm

/-- The preceding relation isomorphism on the universe-small presentations. -/
noncomputable def IsOrderIsomorphism.toSmallRelIso
    {graph relation domain ordinal : LCarrier.{u}}
    (h : IsOrderIsomorphism LMem graph relation domain ordinal) :
    smallGraphRel relation domain ≃r smallInternalMem ordinal := by
  let sourceEquiv := smallToInternalCarrierEquiv domain
  let targetEquiv := smallToInternalCarrierEquiv ordinal
  let sourceIso := RelIso.preimage sourceEquiv
    (Constructible.Model.graphRelOn relation domain)
  let targetIso := RelIso.preimage targetEquiv
    (fun x y : Constructible.Model.InternalCarrier ordinal => LMem x.1 y.1)
  have hsource :
      smallGraphRel relation domain =
        InvImage (Constructible.Model.graphRelOn relation domain)
          sourceEquiv := by
    funext x y
    rfl
  have htarget :
      smallInternalMem ordinal =
        InvImage
          (fun x y : Constructible.Model.InternalCarrier ordinal =>
            LMem x.1 y.1)
          targetEquiv := by
    rfl
  rw [hsource, htarget]
  exact sourceIso.trans (h.toInternalRelIso.trans targetIso.symm)

/-! ## Uniqueness of the ordinal target -/

/-- The ordinal target of an internal order-isomorphism is the ordinary order
type of the source small carrier. -/
theorem IsOrderIsomorphism.type_smallGraphRel_eq
    {graph relation domain ordinal : LCarrier.{u}}
    [IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain)]
    (h : IsOrderIsomorphism LMem graph relation domain ordinal)
    (alpha : Ordinal.{u}) (hordinal : ordinal = ordinalLCarrier alpha) :
    Ordinal.type (smallGraphRel relation domain) = alpha := by
  subst ordinal
  let orderIso := h.toSmallRelIso.trans
    (smallInternalMemOrdinalRelIso alpha)
  calc
    Ordinal.type (smallGraphRel relation domain) =
        Ordinal.type (smallOrdinalMem alpha) :=
      orderIso.ordinalType_congr
    _ = alpha := type_smallZFCarrier_ordinal alpha

/-- Internal predecessor sets for the same represented relation and point are
extensionally equal. -/
theorem predecessorSet_unique
    {first second relation domain point : LCarrier.{u}}
    (hfirst : IsPredecessorSetOf LMem first relation domain point)
    (hsecond : IsPredecessorSetOf LMem second relation domain point) :
    first = second := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  . intro hz
    let zL : LCarrier.{u} :=
      ⟨z, Constructible.mem_L_of_mem hz first.2⟩
    have hsemantic := (hfirst zL).mp hz
    exact (hsecond zL).mpr hsemantic
  . intro hz
    let zL : LCarrier.{u} :=
      ⟨z, Constructible.mem_L_of_mem hz second.2⟩
    have hsemantic := (hsecond zL).mp hz
    exact (hfirst zL).mpr hsemantic

/-- A well-ordered initial segment has only one internally represented von
Neumann ordinal as its order type. -/
theorem IsInitialSegmentOrderType.ordinal_unique
    {relation domain point first second : LCarrier.{u}}
    (hfirst : IsInitialSegmentOrderType LMem relation domain point first)
    (hsecond : IsInitialSegmentOrderType LMem relation domain point second) :
    first = second := by
  rcases hfirst with ⟨hfirstOrdinal, predecessorsFirst,
    hpredecessorsFirst, graphFirst, hgraphFirst⟩
  rcases hsecond with ⟨hsecondOrdinal, predecessorsSecond,
    hpredecessorsSecond, graphSecond, hgraphSecond⟩
  have hpredecessors : predecessorsSecond = predecessorsFirst :=
    predecessorSet_unique hpredecessorsSecond hpredecessorsFirst
  subst predecessorsSecond
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      first hfirstOrdinal with ⟨alpha, hfirstEq⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      second hsecondOrdinal with ⟨beta, hsecondEq⟩
  subst first
  subst second
  let ordinalIso : smallOrdinalMem alpha ≃r smallOrdinalMem beta :=
    (smallInternalMemOrdinalRelIso alpha).symm.trans
      (hgraphFirst.toSmallRelIso.symm.trans
        (hgraphSecond.toSmallRelIso.trans
          (smallInternalMemOrdinalRelIso beta)))
  have hab : alpha = beta := by
    calc
      alpha = Ordinal.type (smallOrdinalMem alpha) :=
        (type_smallZFCarrier_ordinal alpha).symm
      _ = Ordinal.type (smallOrdinalMem beta) :=
        ordinalIso.ordinalType_congr
      _ = beta := type_smallZFCarrier_ordinal beta
  exact congrArg ordinalLCarrier hab

end

end Constructible.ContinuumFormula
