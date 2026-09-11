/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeReplacement

/-!
# The successor step of the internal order-type recursion

Assume that every strict predecessor of a point already has its canonical
internally represented order type.  The preceding Replacement theorem gives
the exact internal range.  Separation of `beforeOrderTypeRelation` inside the
union of the predecessor set and the target ordinal then gives an actual
Kuratowski graph in `L`.  This file proves that graph is an order isomorphism.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

private theorem beforeOrderTypeStep_assignment
    (relation domain point input output : LCarrier.{u}) :
    snoc (snoc ![relation, domain, point] input) output =
      ![relation, domain, point, input, output] := by
  funext i
  fin_cases i <;> rfl

/-- The canonical order-type code is injective on the points of an internally
represented well-order. -/
theorem canonicalMemberOrderTypeLCarrier_injective
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1)
    (hxy : canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx =
      canonicalMemberOrderTypeLCarrier
        relation domain hwell y hy) :
    x = y := by
  apply canonicalMemberOrderType_injective
    relation domain hwell x y hx hy
  apply Ordinal.toZFSet_injective
  exact congrArg Subtype.val hxy

/--
The well-founded induction step: if all strict predecessors of `point` have
their canonical internal order types, then `point` has its canonical internal
order type as well.
-/
theorem canonicalMemberOrderType_isInitial_of_predecessors
    (relation domain point : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (hpoint : point.1 ∈ domain.1)
    (hsegments : forall z : LCarrier.{u},
      forall hz : z.1 ∈ domain.1,
        GraphRel relation z point ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz)) :
    IsInitialSegmentOrderType LMem relation domain point
      (canonicalMemberOrderTypeLCarrier
        relation domain hwell point hpoint) := by
  let target := canonicalMemberOrderTypeLCarrier
    relation domain hwell point hpoint
  rcases exists_internalPredecessorOrderTypeRange
      relation domain point hwell hpoint hsegments with
    ⟨predecessors, range, hpredecessors, _hrange, hrangeEq⟩
  have hrangeTarget : range = target := by
    exact hrangeEq
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  let container : LCarrier.{u} := unionLCarrier predecessors target
  rcases Model.exists_definableRelationGraph_with_support
      beforeOrderTypeRelation params container with
    ⟨graph, hsupport, hgraph⟩
  have hformula_iff : forall x y : LCarrier.{u},
      FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) <->
        x.1 ∈ domain.1 /\ GraphRel relation x point /\
          IsInitialSegmentOrderType LMem relation domain x y := by
    intro x y
    simp only [params]
    rw [beforeOrderTypeStep_assignment]
    exact satisfies_beforeOrderTypeRelation relation domain point x y
  have hcanonicalMem : forall x : LCarrier.{u},
      forall hx : x.1 ∈ domain.1,
        GraphRel relation x point ->
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell x hx).1 ∈ target.1 := by
    intro x hx hxPoint
    exact (canonicalMemberOrderTypeLCarrier_mem_iff
      relation domain hwell x point hx hpoint).mpr hxPoint
  have hformula_eq : forall x y : LCarrier.{u},
      forall hx : x.1 ∈ predecessors.1,
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) ->
            y = canonicalMemberOrderTypeLCarrier
              relation domain hwell x
                ((hpredecessors x).mp hx).1 := by
    intro x y hx hformula
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxPoint : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    have hySegment := (hformula_iff x y).mp hformula |>.2.2
    have hcanonical := hsegments x hxDomain hxPoint
    exact hySegment.ordinal_unique hcanonical
  have hbetween : IsGraphBetween LMem graph predecessors target := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
    have hsemantic := (hformula_iff x y).mp hformula
    have hxDomain : x.1 ∈ domain.1 := hsemantic.1
    have hxPoint : GraphRel relation x point := hsemantic.2.1
    have hxPredecessors : x.1 ∈ predecessors.1 :=
      (hpredecessors x).mpr
        ⟨hxDomain,
          (graphValue_lCarrier_iff_graphRel relation x point).mpr
            hxPoint⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hxDomain :=
      hsemantic.2.2.ordinal_unique (hsegments x hxDomain hxPoint)
    have hyTarget : y.1 ∈ target.1 := by
      rw [hyEq]
      exact hcanonicalMem x hxDomain hxPoint
    refine ⟨x, hxPredecessors, y, hyTarget, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq
  have htotal : forall x : LCarrier.{u}, x.1 ∈ predecessors.1 ->
      HasUniqueImage LMem graph x target := by
    intro x hx
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxPoint : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hxDomain
    have hvalueTarget : value.1 ∈ target.1 :=
      hcanonicalMem x hxDomain hxPoint
    have hxContainer : x.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target x).mpr (Or.inl hx)
    have hvalueContainer : value.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target value).mpr
        (Or.inr hvalueTarget)
    have hvalueFormula :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) value) :=
      (hformula_iff x value).mpr
        ⟨hxDomain, hxPoint, hsegments x hxDomain hxPoint⟩
    have hvalueGraph : GraphValue LMem graph x value :=
      (graphValue_lCarrier_iff_graphRel graph x value).mpr
        ((hgraph x value).mpr
          ⟨hxContainer, hvalueContainer, hvalueFormula⟩)
    refine ⟨value, hvalueTarget, hvalueGraph, ?_⟩
    intro other _hotherTarget hotherGraph
    have hotherFormula := (hgraph x other).mp
      ((graphValue_lCarrier_iff_graphRel graph x other).mp
        hotherGraph) |>.2.2
    exact hformula_eq x other hx hotherFormula
  have honto : forall y : LCarrier.{u}, y.1 ∈ target.1 ->
      HasUniquePreimage LMem graph predecessors y := by
    intro y hyTarget
    have hyOrdinal : y.1 ∈
        (canonicalMemberOrderType
          relation domain hwell point hpoint).toZFSet := by
      exact hyTarget
    rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
      ⟨beta, hbeta, hbetaValue⟩
    rcases exists_predecessor_canonicalMemberOrderType_eq_of_lt
        relation domain hwell point hpoint hbeta with
      ⟨x, hxDomain, hxPoint, hxType⟩
    have hxPredecessors : x.1 ∈ predecessors.1 :=
      (hpredecessors x).mpr
        ⟨hxDomain,
          (graphValue_lCarrier_iff_graphRel relation x point).mpr
            hxPoint⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hxDomain := by
      apply Subtype.ext
      change y.1 =
        (canonicalMemberOrderType
          relation domain hwell x hxDomain).toZFSet
      rw [hxType]
      exact hbetaValue.symm
    have hxContainer : x.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target x).mpr
        (Or.inl hxPredecessors)
    have hyContainer : y.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target y).mpr
        (Or.inr hyTarget)
    have hformula :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) := by
      apply (hformula_iff x y).mpr
      refine ⟨hxDomain, hxPoint, ?_⟩
      rw [hyEq]
      exact hsegments x hxDomain hxPoint
    have hgraphValue : GraphValue LMem graph x y :=
      (graphValue_lCarrier_iff_graphRel graph x y).mpr
        ((hgraph x y).mpr ⟨hxContainer, hyContainer, hformula⟩)
    refine ⟨x, hxPredecessors, hgraphValue, ?_⟩
    intro z hzPredecessors hzGraph
    have hzSemantic := (hpredecessors z).mp hzPredecessors
    have hzDomain : z.1 ∈ domain.1 := hzSemantic.1
    have hzPoint : GraphRel relation z point :=
      (graphValue_lCarrier_iff_graphRel relation z point).mp
        hzSemantic.2
    have hzFormula := (hgraph z y).mp
      ((graphValue_lCarrier_iff_graphRel graph z y).mp hzGraph) |>.2.2
    have hyEqZ : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell z hzDomain :=
      hformula_eq z y hzPredecessors hzFormula
    apply canonicalMemberOrderTypeLCarrier_injective
      relation domain hwell z x hzDomain hxDomain
    exact hyEqZ.symm.trans hyEq
  refine ⟨canonicalMemberOrderTypeLCarrier_isVonNeumannOrdinal
      relation domain hwell point hpoint,
    predecessors, hpredecessors, graph, ?_⟩
  refine ⟨⟨hbetween, htotal, honto⟩, ?_⟩
  intro x y imageX imageY hx hy hxImage hyImage
  have hxSemantic := (hpredecessors x).mp hx
  have hySemantic := (hpredecessors y).mp hy
  have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
  have hyDomain : y.1 ∈ domain.1 := hySemantic.1
  have hxFormula := (hgraph x imageX).mp
    ((graphValue_lCarrier_iff_graphRel graph x imageX).mp
      hxImage) |>.2.2
  have hyFormula := (hgraph y imageY).mp
    ((graphValue_lCarrier_iff_graphRel graph y imageY).mp
      hyImage) |>.2.2
  have hxEq := hformula_eq x imageX hx hxFormula
  have hyEq := hformula_eq y imageY hy hyFormula
  rw [hxEq, hyEq]
  rw [graphValue_lCarrier_iff_graphRel]
  exact (canonicalMemberOrderTypeLCarrier_mem_iff
    relation domain hwell x y hxDomain hyDomain).symm

end

end Constructible.ContinuumFormula
