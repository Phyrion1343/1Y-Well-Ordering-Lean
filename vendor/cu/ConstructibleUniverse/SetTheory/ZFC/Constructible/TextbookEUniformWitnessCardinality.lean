/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEElementaryHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteTupleInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFunctionRangeInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalBinaryUnionInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ParametricUniformOmegaInjectionFamily

/-!
# Cardinal control for the textbook E witness hull

This file follows the standard countable-language Skolem-hull estimate with
internally represented graphs at every step.  The task set and all finite
parameter tuples inject into an infinite internal cardinal.  The inverse of
the Replacement graph injects its range back into the request domain, and a
tagged binary-union graph retains the preceding stage.  Finite induction gives
the pointwise bounds; canonical least selection and Replacement then collect
the injection family used to bound the genuine internal omega union.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

private theorem natLCarrier_mem_omega (n : Nat) :
    (natLCarrier n).1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
  change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode n)).mpr ⟨n, rfl⟩

/-- The internal task set `omega x (omega \ {0})` is bounded by every
internal infinite cardinal. -/
theorem injects_textbookEWitnessTaskDomain_lCarrier
    {kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa) :
    Injects LMem textbookEWitnessTaskDomain kappa := by
  have htaskSquare : Injects LMem textbookEWitnessTaskDomain
      (prodLCarrier kappa kappa) := by
    apply injects_of_subset_lCarrier
    intro task htask
    rcases (mem_textbookEWitnessTaskDomain_iff task.1).mp htask with
      ⟨code, arity, htaskEq⟩
    change task.1 ∈ ZFSet.prod kappa.1 kappa.1
    rw [htaskEq, ZFSet.pair_mem_prod]
    exact ⟨homega (natLCarrier code) (natLCarrier_mem_omega code),
      homega (natLCarrier (arity + 1))
        (natLCarrier_mem_omega (arity + 1))⟩
  exact htaskSquare.trans_lCarrier hsquare

/-- The request domain for one simultaneous witness step injects into the
controlling cardinal. -/
theorem injects_textbookEUniformWitnessRequestDomain_lCarrier
    {seed kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessRequestDomain seed) kappa := by
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have htasks : Injects LMem textbookEWitnessTaskDomain kappa :=
    injects_textbookEWitnessTaskDomain_lCarrier homega hsquare
  have htuples : Injects LMem (internalFiniteTupleSpaces seed) kappa :=
    injects_internalFiniteTupleSpaces_lCarrier hseed hcardinal homega
  have hrequestSquare : Injects LMem
      (textbookEUniformWitnessRequestDomain seed)
      (prodLCarrier kappa kappa) := by
    simpa only [textbookEUniformWitnessRequestDomain] using
      injects_prod_of_injects_lCarrier htasks htuples
  exact hrequestSquare.trans_lCarrier hsquare

/-- One uniform witness step preserves an internal infinite-cardinal bound.
The range estimate is obtained by reversing the actual Replacement graph. -/
theorem injects_textbookEUniformWitnessStep_lCarrier
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessStep seed U) kappa := by
  let data := textbookEUniformWitnessReplacementData seed U
  have hrequest : Injects LMem
      (textbookEUniformWitnessRequestDomain seed) kappa :=
    injects_textbookEUniformWitnessRequestDomain_lCarrier
      hcardinal homega hseed
  have hrangeDomain : Injects LMem data.range
      (textbookEUniformWitnessRequestDomain seed) :=
    injects_range_into_domain_of_functionGraph
      data.graph (textbookEUniformWitnessRequestDomain seed) data.range
      data.isFunctionGraph data.rangeCovered
  have hrange : Injects LMem data.range kappa :=
    hrangeDomain.trans_lCarrier hrequest
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hunionEq :
      Constructible.Model.unionLCarrier seed data.range =
        Constructible.ContinuumFormula.unionLCarrier seed data.range := by
    apply Constructible.Model.lCarrier_extensionality
    intro z
    rw [Constructible.Model.mem_unionLCarrier_iff,
      Constructible.ContinuumFormula.mem_unionLCarrier_iff]
  rw [textbookEUniformWitnessStep, hunionEq]
  exact injects_binaryUnion_lCarrier homega hsquare hseed hrange

/-- Every finite stage of the simultaneous iteration has a genuine internal
injection into `kappa`. -/
theorem injects_textbookEUniformWitnessStage_lCarrier
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    forall n : Nat,
      Injects LMem (textbookEUniformWitnessStage seed U n) kappa := by
  intro n
  induction n with
  | zero => simpa only [textbookEUniformWitnessStage_zero] using hseed
  | succ n ih =>
      simpa only [textbookEUniformWitnessStage_succ] using
        injects_textbookEUniformWitnessStep_lCarrier
          hcardinal homega ih

/-- The genuine internal omega union of witness stages injects into the same
infinite cardinal. -/
theorem injects_textbookEUniformWitnessOmegaUnion_lCarrier
    {seed U kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hseed : Injects LMem seed kappa) :
    Injects LMem (textbookEUniformWitnessOmegaUnion seed U) kappa := by
  let spec := textbookEUniformWitnessOmegaFamilySpec seed U
  have hsquare : Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hpointwise : forall n : Nat, Injects LMem (spec.value n) kappa := by
    intro n
    simpa only [spec, textbookEUniformWitnessOmegaFamilySpec_value] using
      injects_textbookEUniformWitnessStage_lCarrier
        hcardinal homega hseed n
  simpa only [textbookEUniformWitnessOmegaUnion, spec] using
    injects_parametricUniformOmegaUnion_of_pointwise
      spec kappa homega hsquare hpointwise

/-- Adjoining one distinguished parameter to an infinite cardinal preserves
the bound. -/
theorem injects_textbookEElementaryHullSeed_lCarrier
    (kappa x : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Injects LMem (textbookEElementaryHullSeed kappa x) kappa := by
  by_cases hx : x.1 ∈ kappa.1
  · apply injects_of_subset_lCarrier
    intro z hz
    let zL : LCarrier.{u} :=
      ⟨z, mem_L_of_mem hz (textbookEElementaryHullSeed kappa x).2⟩
    rcases (mem_adjoinLCarrier_iff kappa x zL).mp hz with hzx | hzkappa
    · have hzEq : z = x.1 := congrArg Subtype.val hzx
      simpa only [hzEq] using hx
    · exact hzkappa
  · exact injects_adjoin_fresh_of_omega_subset_lCarrier
      homega hx (injects_refl_lCarrier kappa)

/-- The concrete fully elementary textbook E hull is cardinal-controlled. -/
theorem injects_textbookEElementaryHull_lCarrier
    (kappa x : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Injects LMem (textbookEElementaryHull kappa x) kappa := by
  simpa only [textbookEElementaryHull] using
    injects_textbookEUniformWitnessOmegaUnion_lCarrier
      hcardinal homega
      (injects_textbookEElementaryHullSeed_lCarrier kappa x homega)

/-- The standard Skolem-hull construction discharges the full
`HasCardinalControlledHulls` interface. -/
theorem hasCardinalControlledHulls_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    HasCardinalControlledHulls kappa := by
  apply hasCardinalControlledHulls_of_textbookEElementaryHull_injects
  intro x _hx
  exact injects_textbookEElementaryHull_lCarrier
    kappa x hcardinal homega

end

end Constructible.ContinuumFormula
