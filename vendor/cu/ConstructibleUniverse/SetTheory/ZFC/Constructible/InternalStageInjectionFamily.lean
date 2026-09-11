/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalLimitStageSelector
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInfiniteCardinalSquare

/-!
# Collecting internal stage injections by Replacement

`CanonicalLimitStageSelector` reduces the limit-stage cardinal argument to a
single constructible function graph which assigns an injection graph to every
earlier stage.  This file records the exact formula-level input needed to
construct that family by Replacement.

The remaining mathematical obligation is deliberately visible as
`InternalStageInjectionFormulaData`: one fixed first-order formula must have a
unique output at every ordinal below the limit, and that output must really be
an internal injection from the corresponding constructible stage.  An
external cardinal estimate, or an externally chosen family of maps, does not
inhabit this structure.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A formula-functional Replacement graph and its range -/

/-- Replacement simultaneously supplies the actual function graph and its
actual range set.  The graph-value equivalence exposes precisely the formula
used to construct it. -/
theorem exists_replacementFunctionGraphAndRangeLCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u})
    (hfun : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
      ExistsUnique fun y : LCarrier.{u} =>
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y)) :
    exists graph range : LCarrier.{u},
      IsFunctionGraph LMem graph domain range /\
        (forall y : LCarrier.{u}, y.1 ∈ range.1 <->
          exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
            FOFormula.Satisfies LMem phi
              (snoc (snoc params x) y)) /\
        forall x y : LCarrier.{u},
          GraphValue LMem graph x y <->
            x.1 ∈ domain.1 /\
              FOFormula.Satisfies LMem phi
                (snoc (snoc params x) y) := by
  rcases Constructible.Model.exists_replacementLCarrier
      phi params domain hfun with
    ⟨range, hrange⟩
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      phi params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall x y : LCarrier.{u},
      GraphValue LMem graph x y <->
        x.1 ∈ domain.1 /\
          FOFormula.Satisfies LMem phi
            (snoc (snoc params x) y) := by
    intro x y
    constructor
    · rintro ⟨pair, hpairGraph, hpairXY⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨x', hx', y', hy', hpairEq⟩
      have hpairXYEq :=
        (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairXYEq)
      have hxEq : x' = x := Subtype.ext hcoordinates.1
      have hyEq : y' = y := Subtype.ext hcoordinates.2
      subst x'
      subst y'
      exact ⟨hx', hy'⟩
    · rintro ⟨hx, hy⟩
      let pair := orderedPairLCarrier x y
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨x, hx, y, hy, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain range := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨x, hx, y, hy, hpairEq⟩
    have hyRange : y.1 ∈ range.1 := (hrange y).mpr ⟨x, hx, hy⟩
    exact ⟨x, hx, y, hyRange,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  have htotal : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
      HasUniqueImage LMem graph x range := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    have hyRange : y.1 ∈ range.1 := (hrange y).mpr ⟨x, hx, hy⟩
    refine ⟨y, hyRange, (hvalue x y).mpr ⟨hx, hy⟩, ?_⟩
    intro z _hzRange hxz
    exact hyUnique z ((hvalue x z).mp hxz).2
  exact ⟨graph, range, ⟨hbetween, htotal⟩, hrange, hvalue⟩

/-! ## The exact uniform-stage interface -/

/-- Formula-level data sufficient to collect a family of stage injections.

The output is required to be unique because Replacement must collect a
function, not merely choose independently from an external family of
existential witnesses. -/
structure InternalStageInjectionFormulaData
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) where
  arity : Nat
  formula : FOFormula (arity + 2)
  params : Tuple LCarrier.{u} arity
  existsUnique_output : forall index : LCarrier.{u},
    index.1 ∈ (ordinalLCarrier limit).1 ->
      ExistsUnique fun injection : LCarrier.{u} =>
        FOFormula.Satisfies LMem formula
          (snoc (snoc params index) injection)
  output_isInjection : forall ordinal : Ordinal.{u}, ordinal < limit ->
    forall injection : LCarrier.{u},
      FOFormula.Satisfies LMem formula
        (snoc (snoc params (ordinalLCarrier ordinal)) injection) ->
      IsInjection LMem injection (stageLCarrier ordinal) kappa

/-- A uniform formula satisfying the preceding interface is collected into
the exact internal family consumed by the limit-stage union theorem. -/
theorem exists_internalStageInjectionFamily_of_formulaData
    {limit : Ordinal.{u}} {kappa : LCarrier.{u}}
    (data : InternalStageInjectionFormulaData limit kappa) :
    exists injectionFamily graphFamily : LCarrier.{u},
      IsFunctionGraph LMem injectionFamily
        (ordinalLCarrier limit) graphFamily /\
      forall ordinal : Ordinal.{u}, ordinal < limit ->
        forall injection : LCarrier.{u},
          GraphValue LMem injectionFamily
            (ordinalLCarrier ordinal) injection ->
          IsInjection LMem injection (stageLCarrier ordinal) kappa := by
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      data.formula data.params (ordinalLCarrier limit)
      data.existsUnique_output with
    ⟨injectionFamily, graphFamily, hfamily, _hrange, hvalue⟩
  refine ⟨injectionFamily, graphFamily, hfamily, ?_⟩
  intro ordinal hordinal injection hinjection
  apply data.output_isInjection ordinal hordinal injection
  exact (hvalue (ordinalLCarrier ordinal) injection).mp hinjection |>.2

/-! ## Exact connection to the Hartogs stage bound -/

/-- Once the uniform stage-injection formula has been constructed, all
remaining selector, union, and product steps yield the Hartogs stage bound.
The formula data is the sole remaining premise in this theorem. -/
theorem hartogsStageBound_of_internalStageInjectionFormulaData
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (data : InternalStageInjectionFormulaData
      (internalHartogsOrdinal kappa) kappa) :
    HartogsStageBound kappa := by
  rcases exists_internalStageInjectionFamily_of_formulaData data with
    ⟨injectionFamily, graphFamily, hfamily, hinjections⟩
  exact injects_hartogsStage_of_internal_injectionFamily kappa
    (internalHartogsOrdinal_isSuccLimit kappa hcardinal homega)
    hfamily hinjections
    (injects_internalHartogsProduct_internalHartogs_lCarrier
      kappa hcardinal homega)

end

end Constructible.ContinuumFormula
