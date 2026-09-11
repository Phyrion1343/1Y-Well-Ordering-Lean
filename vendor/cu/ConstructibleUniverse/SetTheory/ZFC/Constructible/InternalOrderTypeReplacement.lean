/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeCanonical
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypePredecessor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeUniqueness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement

/-!
# Replacement of the canonical order types below one point

This is the Replacement step in the standard well-order recursion.  Assume
that every strict predecessor of `point` already has its canonical internally
represented order type.  Separation first produces the internal predecessor
set.  Replacement, applied to `beforeOrderTypeRelation`, then produces the
set of predecessor order types.  That range is exactly the canonical ordinal
attached to `point`.

The returned range is an actual `LCarrier`; an external `ZFSet.range` is not
used as its witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

private theorem beforeOrderTypeReplacement_assignment
    (relation domain point input output : LCarrier.{u}) :
    snoc (snoc ![relation, domain, point] input) output =
      ![relation, domain, point, input, output] := by
  funext i
  fin_cases i <;> rfl

/--
Under the induction hypothesis for all predecessors of `point`, Replacement
constructs their order-type range inside `L`, and this range is precisely the
von Neumann ordinal which is the canonical order type at `point`.
-/
theorem exists_internalPredecessorOrderTypeRange
    (relation domain point : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (hpoint : point.1 ∈ domain.1)
    (hsegments : forall z : LCarrier.{u},
      forall hz : z.1 ∈ domain.1,
        GraphRel relation z point ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz)) :
    exists predecessors range : LCarrier.{u},
      IsPredecessorSetOf LMem predecessors relation domain point /\
        (forall y : LCarrier.{u},
          y.1 ∈ range.1 <->
            (exists x : LCarrier.{u}, x.1 ∈ predecessors.1 /\
              FOFormula.Satisfies LMem beforeOrderTypeRelation
                (snoc (snoc ![relation, domain, point] x) y))) /\
        range = canonicalMemberOrderTypeLCarrier
          relation domain hwell point hpoint := by
  rcases exists_internalPredecessorSet relation domain point with
    ⟨predecessors, hpredecessors⟩
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  have hfunctional : forall x : LCarrier.{u},
      x.1 ∈ predecessors.1 ->
        ∃! y : LCarrier.{u},
          FOFormula.Satisfies LMem beforeOrderTypeRelation
            (snoc (snoc params x) y) := by
    intro x hx
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxRelation : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hxDomain
    have hsegment :
        IsInitialSegmentOrderType LMem relation domain x value :=
      hsegments x hxDomain hxRelation
    have hvalue :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) value) := by
      simp only [params]
      rw [beforeOrderTypeReplacement_assignment]
      exact (satisfies_beforeOrderTypeRelation
        relation domain point x value).mpr
          ⟨hxDomain, hxRelation, hsegment⟩
    refine ⟨value, hvalue, ?_⟩
    intro other hother
    have hotherSemantic :
        IsInitialSegmentOrderType LMem relation domain x other := by
      simp only [params] at hother
      rw [beforeOrderTypeReplacement_assignment] at hother
      exact (satisfies_beforeOrderTypeRelation
        relation domain point x other).mp hother |>.2.2
    exact hotherSemantic.ordinal_unique hsegment
  rcases Model.exists_replacementLCarrier
      beforeOrderTypeRelation params predecessors hfunctional with
    ⟨range, hrange⟩
  refine ⟨predecessors, range, hpredecessors, ?_, ?_⟩
  . intro y
    simpa only [params] using hrange y
  . apply Subtype.ext
    apply ZFSet.ext
    intro y
    constructor
    . intro hyRange
      let yL : LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hyRange range.2⟩
      rcases (hrange yL).mp hyRange with
        ⟨x, hxPredecessors, hformula⟩
      have hsemantic := (hpredecessors x).mp hxPredecessors
      have hxDomain : x.1 ∈ domain.1 := hsemantic.1
      have hxRelation : GraphRel relation x point :=
        (graphValue_lCarrier_iff_graphRel relation x point).mp
          hsemantic.2
      have hcanonical :
          IsInitialSegmentOrderType LMem relation domain x
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell x hxDomain) :=
        hsegments x hxDomain hxRelation
      have hySegment :
          IsInitialSegmentOrderType LMem relation domain x yL := by
        simp only [params] at hformula
        rw [beforeOrderTypeReplacement_assignment] at hformula
        exact (satisfies_beforeOrderTypeRelation
          relation domain point x yL).mp hformula |>.2.2
      have hyEq : yL = canonicalMemberOrderTypeLCarrier
          relation domain hwell x hxDomain :=
        hySegment.ordinal_unique hcanonical
      have hcanonicalMem :
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell x hxDomain).1 ∈
              (canonicalMemberOrderTypeLCarrier
                relation domain hwell point hpoint).1 :=
        (canonicalMemberOrderTypeLCarrier_mem_iff
          relation domain hwell x point hxDomain hpoint).mpr hxRelation
      change yL.1 ∈
        (canonicalMemberOrderTypeLCarrier
          relation domain hwell point hpoint).1
      rw [hyEq]
      exact hcanonicalMem
    . intro hyTarget
      let yL : LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hyTarget
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell point hpoint).2⟩
      have hyOrdinal : y ∈
          (canonicalMemberOrderType
            relation domain hwell point hpoint).toZFSet := by
        exact hyTarget
      rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
        ⟨beta, hbeta, hbetaValue⟩
      rcases exists_predecessor_canonicalMemberOrderType_eq_of_lt
          relation domain hwell point hpoint hbeta with
        ⟨x, hxDomain, hxRelation, hxType⟩
      have hxPredecessors : x.1 ∈ predecessors.1 :=
        (hpredecessors x).mpr
          ⟨hxDomain,
            (graphValue_lCarrier_iff_graphRel relation x point).mpr
              hxRelation⟩
      have hyEq : yL = canonicalMemberOrderTypeLCarrier
          relation domain hwell x hxDomain := by
        apply Subtype.ext
        change y =
          (canonicalMemberOrderType
            relation domain hwell x hxDomain).toZFSet
        rw [hxType]
        exact hbetaValue.symm
      have hsegment :
          IsInitialSegmentOrderType LMem relation domain x
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell x hxDomain) :=
        hsegments x hxDomain hxRelation
      have hformula :
          FOFormula.Satisfies LMem beforeOrderTypeRelation
            (snoc (snoc params x) yL) := by
        simp only [params]
        rw [beforeOrderTypeReplacement_assignment]
        apply (satisfies_beforeOrderTypeRelation
          relation domain point x yL).mpr
        refine ⟨hxDomain, hxRelation, ?_⟩
        rw [hyEq]
        exact hsegment
      exact (hrange yL).mpr ⟨x, hxPredecessors, hformula⟩

end

end Constructible.ContinuumFormula
