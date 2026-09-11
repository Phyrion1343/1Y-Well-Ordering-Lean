/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalStageInjectionFamily

/-!
# Parameterized internal omega families

This is the parameterized form of `UniformOmegaFamilySpec`.  A fixed tuple of
constructible parameters is passed to one object-language formula with layout
`[params,index,value]`.  Replacement over the actual internal omega produces
both the represented function graph and its range, and internal union then
collects all stages.
-/

@[expose] public section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- A fixed formula, with constructible parameters, uniformly defines an
omega-indexed family. -/
structure ParametricUniformOmegaFamilySpec (parameterCount : Nat) where
  params : Tuple LCarrier.{u} parameterCount
  formula : FOFormula (parameterCount + 2)
  value : Nat -> LCarrier.{u}
  realizes : forall (n : Nat) (y : LCarrier.{u}),
    FOFormula.Satisfies LMem formula
        (snoc (snoc params (natLCarrier n)) y) <->
      y = value n

/-- The actual Replacement graph and range of a parameterized omega family. -/
structure ParametricUniformOmegaFamilyData {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) where
  graph : LCarrier.{u}
  family : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem graph omegaLCarrier family
  mem_family_iff : forall y : LCarrier.{u},
    y.1 ∈ family.1 <-> exists n : Nat, y = spec.value n
  graphValue_iff : forall index y : LCarrier.{u},
    GraphValue LMem graph index y <->
      index.1 ∈ omegaLCarrier.1 /\
        FOFormula.Satisfies LMem spec.formula
          (snoc (snoc spec.params index) y)

/-- Replacement constructs the represented family data. -/
theorem exists_parametricUniformOmegaFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    Nonempty (ParametricUniformOmegaFamilyData spec) := by
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ omegaLCarrier.1 ->
        ExistsUnique fun y : LCarrier.{u} =>
          FOFormula.Satisfies LMem spec.formula
            (snoc (snoc spec.params index) y) := by
    intro index hindex
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    refine ⟨spec.value n, (spec.realizes n (spec.value n)).mpr rfl, ?_⟩
    intro other hother
    exact (spec.realizes n other).mp hother
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      spec.formula spec.params omegaLCarrier hfun with
    ⟨graph, family, hgraph, hfamily, hvalue⟩
  refine ⟨{
    graph := graph
    family := family
    isFunctionGraph := hgraph
    mem_family_iff := ?_
    graphValue_iff := hvalue
  }⟩
  intro y
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    exact ⟨n, (spec.realizes n y).mp hformula⟩
  · rintro ⟨n, rfl⟩
    refine ⟨natLCarrier n, ?_, (spec.realizes n (spec.value n)).mpr rfl⟩
    change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩

/-- A canonical choice of the extensional Replacement data. -/
noncomputable def parametricUniformOmegaFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    ParametricUniformOmegaFamilyData spec :=
  Classical.choice (exists_parametricUniformOmegaFamilyData spec)

/-- The actual internal union of the parameterized family. -/
noncomputable def parametricUniformOmegaUnion
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  sUnionLCarrier (parametricUniformOmegaFamilyData spec).family

@[simp]
theorem mem_parametricUniformOmegaUnion_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (z : LCarrier.{u}) :
    z.1 ∈ (parametricUniformOmegaUnion spec).1 <->
      exists n : Nat, z.1 ∈ (spec.value n).1 := by
  rw [parametricUniformOmegaUnion, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstageFamily, hz⟩
    rcases (parametricUniformOmegaFamilyData spec).mem_family_iff
        stage |>.mp hstageFamily with ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨spec.value n,
      (parametricUniformOmegaFamilyData spec).mem_family_iff
        (spec.value n) |>.mpr ⟨n, rfl⟩,
      hz⟩

theorem value_subset_parametricUniformOmegaUnion
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (n : Nat) :
    (spec.value n).1 ⊆ (parametricUniformOmegaUnion spec).1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (spec.value n).2⟩
  exact (mem_parametricUniformOmegaUnion_iff spec zL).mpr ⟨n, hz⟩

end

end Constructible.Model
