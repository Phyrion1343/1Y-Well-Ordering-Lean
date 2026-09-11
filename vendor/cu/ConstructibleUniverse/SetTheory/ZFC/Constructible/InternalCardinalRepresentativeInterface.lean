/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentatives
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHBridge

/-!
# The explicit order-type interface for internal cardinal representatives

`ModelsInternalWellOrdering` supplies a constructible graph for a well-order,
but it does not by itself supply the graph of the order-type map.  This file
records the exact missing witness.  Once an internal ordinal and a total,
single-valued, onto interpretation of `memberOrderTypeRelation` are supplied,
the existing Separation/graph theorem constructs the actual Kuratowski graph
in `L`.  No ambient equivalence is used as an internal witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The missing order-type witness -/

/--
An internal witness that `ordinal` is the range of the order-type map for
`relation` on `domain`.  The formula is the already verified
`memberOrderTypeRelation`, with assignment `[relation, domain, point, ordinal]`.

The four semantic fields are deliberately explicit: proving them is the
genuine well-founded-recursion/Replacement step in the usual proof.
-/
structure InternalOrderTypeWitness
    (relation domain : LCarrier.{u}) where
  ordinal : LCarrier.{u}
  ordinal_spec : IsVonNeumannOrdinal LMem ordinal
  total : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
    exists y : LCarrier.{u},
      y.1 ∈ ordinal.1 /\
        FOFormula.Satisfies LMem memberOrderTypeRelation
          ![relation, domain, x, y]
  bounded : forall x y : LCarrier.{u}, x.1 ∈ domain.1 ->
    FOFormula.Satisfies LMem memberOrderTypeRelation
      ![relation, domain, x, y] ->
      y.1 ∈ ordinal.1
  unique : forall x y z : LCarrier.{u},
    x.1 ∈ domain.1 ->
      y.1 ∈ ordinal.1 ->
        z.1 ∈ ordinal.1 ->
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, y] ->
            FOFormula.Satisfies LMem memberOrderTypeRelation
              ![relation, domain, x, z] ->
              y = z
  injective : forall x z y : LCarrier.{u},
    x.1 ∈ domain.1 ->
      z.1 ∈ domain.1 ->
        y.1 ∈ ordinal.1 ->
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, y] ->
            FOFormula.Satisfies LMem memberOrderTypeRelation
              ![relation, domain, z, y] ->
              x = z
  onto : forall y : LCarrier.{u}, y.1 ∈ ordinal.1 ->
    exists x : LCarrier.{u},
      x.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem memberOrderTypeRelation
          ![relation, domain, x, y]

/-! ## Internal graph and equinumerosity -/

/--
An `InternalOrderTypeWitness` yields an internally represented bijection from
the domain to its ordinal target.  The graph is obtained by the existing
Separation construction for a fixed first-order relation.
-/
theorem internalEquinumerous_ordinal_of_orderTypeWitness
    {relation domain : LCarrier.{u}}
    (w : InternalOrderTypeWitness relation domain) :
    exists graph : LCarrier.{u},
      IsBijection LMem graph domain w.ordinal := by
  let params : Tuple LCarrier.{u} 2 := ![relation, domain]
  let container : LCarrier.{u} := unionLCarrier domain w.ordinal
  rcases Model.exists_definableRelationGraph_with_support
      memberOrderTypeRelation params container with
    ⟨graph, hsupport, hgraph⟩
  refine ⟨graph, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro pair hpair
    rcases (hsupport pair hpair) with
      ⟨x, y, hx, hy, hpairEq, hformula⟩
    have hformulaSem :=
      (satisfies_memberOrderTypeRelation relation domain x y).mp hformula
    have hxDomain : x.1 ∈ domain.1 := hformulaSem.1
    have hyOrdinal : y.1 ∈ w.ordinal.1 := w.bounded x y hxDomain hformula
    refine ⟨x, hxDomain, y, hyOrdinal, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq
  · intro x hx
    rcases w.total x hx with ⟨y, hyOrdinal, hformula⟩
    refine ⟨y, hyOrdinal, ?_, ?_⟩
    · apply (graphValue_lCarrier_iff_graphRel graph x y).mpr
      exact (hgraph x y).mpr ⟨mem_unionLCarrier_iff domain w.ordinal x |>.mpr (Or.inl hx),
        mem_unionLCarrier_iff domain w.ordinal y |>.mpr (Or.inr hyOrdinal), hformula⟩
    · intro z hz hvalue
      have hzFormula :
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, z] := by
        exact (hgraph x z).mp
          ((graphValue_lCarrier_iff_graphRel graph x z).mp hvalue) |>.2.2
      exact w.unique x y z hx hyOrdinal hz hformula hzFormula |>.symm
  · intro y hy
    rcases w.onto y hy with ⟨x, hx, hformula⟩
    refine ⟨x, hx, ?_, ?_⟩
    · apply (graphValue_lCarrier_iff_graphRel graph x y).mpr
      exact (hgraph x y).mpr ⟨mem_unionLCarrier_iff domain w.ordinal x |>.mpr (Or.inl hx),
        mem_unionLCarrier_iff domain w.ordinal y |>.mpr (Or.inr hy), hformula⟩
    · intro z hz hvalue
      have hzFormula :
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, z, y] := by
        exact (hgraph z y).mp
          ((graphValue_lCarrier_iff_graphRel graph z y).mp hvalue) |>.2.2
      exact w.injective z x y hz hx hy hzFormula hformula

/-! ## Reduction to the cardinal-representative interface -/

/--
If every internally well-ordered set has the explicit order-type witness
above, then every constructible set has an internal cardinal representative.
The hypothesis is exactly the remaining order-type recursion theorem; it is
not discharged by an external `Equiv`.
-/
theorem hasInternalCardinalRepresentatives_of_orderTypeWitness
    (h : forall domain : LCarrier.{u},
      exists relation : LCarrier.{u},
        InternallyWellOrders relation domain /\
          Nonempty (InternalOrderTypeWitness relation domain)) :
    HasInternalCardinalRepresentatives.{u} := by
  intro domain
  rcases h domain with ⟨relation, _hwell, ⟨w⟩⟩
  rcases internalEquinumerous_ordinal_of_orderTypeWitness w with
    ⟨graph, hbij⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      w.ordinal w.ordinal_spec with ⟨alpha, halpha⟩
  have hEquiv : Equinumerous LMem domain (ordinalLCarrier alpha) := by
    rw [← halpha]
    exact ⟨graph, hbij⟩
  exact exists_internalCardinalRepresentative_of_ordinalRepresentative
    domain ⟨alpha, hEquiv⟩

end Constructible.ContinuumFormula
