/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHApplication

/-!
# The logical implication `GCH -> CH`

This file contains the standard semantic implication and applies it to the
unconditional GCH theorem for the constructible membership structure.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
local notation "LMem" => Constructible.Model.lCarrierMem

theorem modelsCH_of_modelsGCH {A : Type u} {E : A -> A -> Prop}
    (hGCH : ModelsGCH E) : ModelsCH E := by
  rcases hGCH with ⟨omega, hOmega, hOmegaCardinal, hGCHAt⟩
  have hOmegaSubset : IsSubsetOf E omega omega := by
    intro x hx
    exact hx
  rcases hGCHAt omega ⟨hOmegaCardinal, hOmegaSubset⟩ with
    ⟨next, power, hNext, hPower, hEquinumerous⟩
  exact ⟨omega, next, power, hOmega, hNext, hPower, hEquinumerous⟩

/-- Once the existing conditional GCH interfaces are discharged, CH follows
by the preceding semantic implication. -/
theorem modelsCH_lCarrier_of_condensation_interfaces
    (hhulls : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HasCardinalControlledHulls kappa)
    (hstage : forall kappa : LCarrier.{u},
      IsCardinal LMem kappa ->
      IsSubsetOf LMem omegaLCarrier kappa ->
      HartogsStageBound kappa) :
    ModelsCH (A := LCarrier.{u}) LMem := by
  exact modelsCH_of_modelsGCH
    (modelsGCH_lCarrier_of_hulls_and_hartogsStageBound hhulls hstage)

/-- The constructible membership structure satisfies CH, as the `kappa = omega`
instance of its GCH theorem. -/
theorem modelsCH_lCarrier :
    ModelsCH (A := LCarrier.{u}) LMem :=
  modelsCH_of_modelsGCH modelsGCH_lCarrier

end Constructible.ContinuumFormula

end
