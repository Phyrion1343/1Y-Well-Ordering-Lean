/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeWitnessConstruction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalLStageInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessCardinality

/-!
# GCH in the constructible universe

This file first records the condensation bridge with its two substantive
interfaces explicit.  It then discharges both interfaces by the textbook
`E`-Skolem-hull construction and the internal Hartogs-stage induction.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-- The Condensation reduction yields GCH in `L` once its two genuinely open
interfaces are constructed.  Internal cardinal representatives require no
additional hypothesis. -/
theorem modelsGCH_lCarrier_of_hulls_and_hartogsStageBound
    (hhulls : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HasCardinalControlledHulls kappa)
    (hstage : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HartogsStageBound kappa) :
    ModelsGCH (A := LCarrier.{u}) LMem := by
  exact modelsGCH_lCarrier_of_condensation_interfaces
    hasInternalCardinalRepresentatives_lCarrier hhulls hstage

/-- The constructible membership structure satisfies GCH.

The controlled-hull input is the full textbook `E` Skolem hull, and the
stage-cardinality input is the internal transfinite induction below the
Hartogs successor. -/
theorem modelsGCH_lCarrier :
    ModelsGCH (A := LCarrier.{u}) LMem :=
  modelsGCH_lCarrier_of_hulls_and_hartogsStageBound
    (fun kappa hcardinal homega =>
      hasCardinalControlledHulls_lCarrier
        kappa hcardinal homega)
    (fun kappa hcardinal homega =>
      hartogsStageBound_lCarrier
        kappa hcardinal homega)

end Constructible.ContinuumFormula
