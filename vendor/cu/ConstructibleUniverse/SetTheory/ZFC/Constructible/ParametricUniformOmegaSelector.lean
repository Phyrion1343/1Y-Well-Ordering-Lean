/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ParametricUniformOmegaFamily

/-!
# The least-stage selector for a uniform omega family

For an internally represented omega-indexed family, this file constructs the
actual Kuratowski graph which sends an element of the union to the least
natural-number index of a family member containing it.  The graph is obtained
by Separation from one fixed first-order formula.  External minimization on
`Nat` is used only to prove totality and uniqueness of that internal graph.
-/

@[expose] public section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- In a larger context, some value of `familyGraph` at `index` contains
`element`. -/
def uniformOmegaFamilyContainsAt {n : Nat}
    (familyGraph index element : Fin n) : FOFormula n :=
  .ex <| .conj
    (graphValueAt familyGraph.castSucc index.castSucc (Fin.last n))
    (.mem element.castSucc (Fin.last n))

@[simp]
theorem satisfies_uniformOmegaFamilyContainsAt {n : Nat}
    (familyGraph index element : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (uniformOmegaFamilyContainsAt familyGraph index element) s <->
      exists fiber : LCarrier.{u},
        GraphValue LMem (s familyGraph) (s index) fiber /\
          (s element).1 ∈ fiber.1 := by
  simp only [uniformOmegaFamilyContainsAt, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc]

/-- Semantic content of the least-index formula. -/
def IsLeastUniformOmegaFamilyIndex
    (familyGraph omega element index : LCarrier.{u}) : Prop :=
  index.1 ∈ omega.1 /\
    (exists fiber : LCarrier.{u},
      GraphValue LMem familyGraph index fiber /\ element.1 ∈ fiber.1) /\
    forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
      Not (exists fiber : LCarrier.{u},
        GraphValue LMem familyGraph earlier fiber /\
          element.1 ∈ fiber.1)

/-- Layout `[familyGraph,omega,element,index]`. -/
def leastUniformOmegaFamilyIndexFormula : FOFormula 4 :=
  .conj
    (.mem (3 : Fin 4) (1 : Fin 4))
    (.conj
      (uniformOmegaFamilyContainsAt
        (0 : Fin 4) (3 : Fin 4) (2 : Fin 4))
      (FOFormula.boundedAll (3 : Fin 4)
        (.neg (uniformOmegaFamilyContainsAt
          (0 : Fin 5) (Fin.last 4) (2 : Fin 5)))))

@[simp]
theorem satisfies_leastUniformOmegaFamilyIndexFormula
    (familyGraph omega element index : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastUniformOmegaFamilyIndexFormula
        ![familyGraph, omega, element, index] <->
      IsLeastUniformOmegaFamilyIndex
        familyGraph omega element index := by
  simp only [leastUniformOmegaFamilyIndexFormula,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    satisfies_uniformOmegaFamilyContainsAt,
    IsLeastUniformOmegaFamilyIndex, snoc_last]
  change
    (index.1 ∈ omega.1 /\
      (exists fiber : LCarrier.{u},
        GraphValue LMem familyGraph index fiber /\
          element.1 ∈ fiber.1) /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
        Not (exists fiber : LCarrier.{u},
          GraphValue LMem familyGraph earlier fiber /\
            element.1 ∈ fiber.1)) <-> _
  rfl

/-- A support containing both the union-domain and the natural-number
codomain of the selector. -/
def parametricUniformOmegaSelectorSupport
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  unionLCarrier (parametricUniformOmegaUnion spec) omegaLCarrier

/-- The Separation-generated graph selecting the least containing index. -/
noncomputable def parametricUniformOmegaSelectorGraph
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  canonicalDefinableRelationGraph
    leastUniformOmegaFamilyIndexFormula
    ![(parametricUniformOmegaFamilyData spec).graph, omegaLCarrier]
    (parametricUniformOmegaSelectorSupport spec)

private theorem least_index_assignment
    (familyGraph omega element index : LCarrier.{u}) :
    snoc (snoc ![familyGraph, omega] element) index =
      ![familyGraph, omega, element, index] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem graphValue_parametricUniformOmegaSelectorGraph_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (element index : LCarrier.{u}) :
    GraphValue LMem (parametricUniformOmegaSelectorGraph spec)
        element index <->
      element.1 ∈ (parametricUniformOmegaUnion spec).1 /\
        IsLeastUniformOmegaFamilyIndex
          (parametricUniformOmegaFamilyData spec).graph
          omegaLCarrier element index := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [parametricUniformOmegaSelectorGraph,
    graphRel_canonicalDefinableRelationGraph_iff]
  rw [least_index_assignment,
    satisfies_leastUniformOmegaFamilyIndexFormula]
  constructor
  · rintro ⟨_helementSupport, _hindexSupport, hleast⟩
    rcases hleast.2.1 with ⟨fiber, hfiberValue, helementFiber⟩
    have hfiberFamily :=
      (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
        |>.graphValue_mem_lCarrier hfiberValue |>.2
    exact ⟨(mem_parametricUniformOmegaUnion_iff spec element).mpr <| by
      rcases (parametricUniformOmegaFamilyData spec).mem_family_iff fiber |>.mp
          hfiberFamily with ⟨n, rfl⟩
      exact ⟨n, helementFiber⟩, hleast⟩
  · rintro ⟨helementUnion, hleast⟩
    have helementSupport :
        element.1 ∈ (parametricUniformOmegaSelectorSupport spec).1 :=
      (mem_unionLCarrier_iff
        (parametricUniformOmegaUnion spec) omegaLCarrier element).mpr
          (Or.inl helementUnion)
    have hindexSupport :
        index.1 ∈ (parametricUniformOmegaSelectorSupport spec).1 :=
      (mem_unionLCarrier_iff
        (parametricUniformOmegaUnion spec) omegaLCarrier index).mpr
          (Or.inr hleast.1)
    exact ⟨helementSupport, hindexSupport, hleast⟩

private theorem canonical_family_value
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (n : Nat) :
    GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
      (natLCarrier n) (spec.value n) := by
  apply ((parametricUniformOmegaFamilyData spec).graphValue_iff
    (natLCarrier n) (spec.value n)).mpr
  constructor
  · change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩
  · exact (spec.realizes n (spec.value n)).mpr rfl

private theorem value_eq_of_family_graphValue
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {index fiber : LCarrier.{u}} (hindex : index.1 ∈ omegaLCarrier.1)
    (hvalue : GraphValue LMem
      (parametricUniformOmegaFamilyData spec).graph index fiber) :
    exists n : Nat, index = natLCarrier n /\ fiber = spec.value n := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
      hindex with ⟨n, hindexCode⟩
  have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
  subst index
  have hfiberFamily :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
      |>.graphValue_mem_lCarrier hvalue |>.2
  have hcanonicalFamily :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
      |>.graphValue_mem_lCarrier (canonical_family_value spec n) |>.2
  have hfiberEq :=
    (parametricUniformOmegaFamilyData spec).isFunctionGraph.graphValue_unique
      (by
        change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩)
      hfiberFamily hcanonicalFamily hvalue (canonical_family_value spec n)
  exact ⟨n, rfl, hfiberEq⟩

/-- The least-index graph is a total internally represented function from
the omega union into the internal natural numbers. -/
theorem parametricUniformOmegaSelectorGraph_isFunctionGraph
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    IsFunctionGraph LMem (parametricUniformOmegaSelectorGraph spec)
      (parametricUniformOmegaUnion spec) omegaLCarrier := by
  classical
  constructor
  · intro pair hpair
    rcases (mem_canonicalDefinableRelationGraph_iff
        leastUniformOmegaFamilyIndexFormula
        ![(parametricUniformOmegaFamilyData spec).graph, omegaLCarrier]
        (parametricUniformOmegaSelectorSupport spec) pair).mp hpair with
      ⟨element, index, _helementSupport, _hindexSupport,
        hpairEq, hformula⟩
    rw [least_index_assignment,
      satisfies_leastUniformOmegaFamilyIndexFormula] at hformula
    have hgraph :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mpr ⟨?_, hformula⟩
    · exact ⟨element,
        (graphValue_parametricUniformOmegaSelectorGraph_iff
          spec element index).mp hgraph |>.1,
        index, hformula.1,
        (isKuratowskiPairOf_lCarrier_iff pair element index).mpr hpairEq⟩
    · rcases hformula.2.1 with ⟨fiber, hvalue, helement⟩
      have hfiberFamily :=
        (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
          |>.graphValue_mem_lCarrier hvalue |>.2
      rcases (parametricUniformOmegaFamilyData spec).mem_family_iff fiber |>.mp
          hfiberFamily with ⟨n, rfl⟩
      exact (mem_parametricUniformOmegaUnion_iff spec element).mpr
        ⟨n, helement⟩
  · intro element helement
    have hexists : exists n : Nat, element.1 ∈ (spec.value n).1 :=
      (mem_parametricUniformOmegaUnion_iff spec element).mp helement
    let first : Nat := Nat.find hexists
    have hfirst : element.1 ∈ (spec.value first).1 := Nat.find_spec hexists
    let index := natLCarrier first
    have hindexOmega : index.1 ∈ omegaLCarrier.1 := by
      change (natCode first : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode first)).mpr ⟨first, rfl⟩
    have hcontains : exists fiber : LCarrier.{u},
        GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
          index fiber /\ element.1 ∈ fiber.1 :=
      ⟨spec.value first, canonical_family_value spec first, hfirst⟩
    have hminimal : forall earlier : LCarrier.{u},
        earlier.1 ∈ index.1 ->
          Not (exists fiber : LCarrier.{u},
            GraphValue LMem (parametricUniformOmegaFamilyData spec).graph
              earlier fiber /\ element.1 ∈ fiber.1) := by
      intro earlier hearlier
      rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
        earlier.1 first).mp hearlier with ⟨j, hj, hearlierCode⟩
      rintro ⟨fiber, hvalue, helementFiber⟩
      have hearlierOmega : earlier.1 ∈ omegaLCarrier.1 := by
        change earlier.1 ∈ Ordinal.omega0.toZFSet
        rw [hearlierCode]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode j)).mpr ⟨j, rfl⟩
      rcases value_eq_of_family_graphValue spec hearlierOmega hvalue with
        ⟨k, hearlierEq, hfiberEq⟩
      have hjk : j = k := by
        apply natCode_injective
        exact hearlierCode.symm.trans (congrArg Subtype.val hearlierEq)
      subst k
      rw [hfiberEq] at helementFiber
      exact (Nat.not_lt_of_ge (Nat.find_min' hexists helementFiber)) hj
    have hleast : IsLeastUniformOmegaFamilyIndex
        (parametricUniformOmegaFamilyData spec).graph
        omegaLCarrier element index :=
      ⟨hindexOmega, hcontains, hminimal⟩
    refine ⟨index, hindexOmega,
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mpr ⟨helement, hleast⟩, ?_⟩
    intro other hotherOmega hotherGraph
    have hotherLeast :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element other).mp hotherGraph |>.2
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode other.1).mp
        hotherOmega with ⟨m, hotherCode⟩
    have hotherEq : other = natLCarrier m := Subtype.ext hotherCode
    subst other
    rcases hotherLeast.2.1 with ⟨fiber, hfamilyValue, helementFiber⟩
    rcases value_eq_of_family_graphValue spec hotherLeast.1 hfamilyValue with
      ⟨k, hindexEq, hfiberEq⟩
    have hmk : m = k := by
      apply natCode_injective
      exact congrArg Subtype.val hindexEq
    subst k
    rw [hfiberEq] at helementFiber
    have hfirstLe : first <= m := Nat.find_min' hexists helementFiber
    have hmLe : m <= first := by
      by_contra hnot
      have hfirstLt : first < m := Nat.lt_of_not_ge hnot
      have hfirstMem :
          (natLCarrier first).1 ∈ (natLCarrier m).1 :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode first) m).mpr ⟨first, hfirstLt, rfl⟩
      exact (hotherLeast.2.2 (natLCarrier first) hfirstMem)
        ⟨spec.value first, canonical_family_value spec first, hfirst⟩
    exact congrArg natLCarrier (Nat.le_antisymm hmLe hfirstLe)

/-- The canonical least-index graph supplies exactly the selector contract
used by the internal cardinal-union construction. -/
theorem parametricUniformOmegaSelectorGraph_selectsContainingFiber
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    SelectsContainingFiber LMem
      (parametricUniformOmegaSelectorGraph spec)
      (parametricUniformOmegaUnion spec) omegaLCarrier
      (parametricUniformOmegaFamilyData spec).graph := by
  constructor
  · exact parametricUniformOmegaSelectorGraph_isFunctionGraph spec
  · intro element index helement hselect
    have hleast :=
      (graphValue_parametricUniformOmegaSelectorGraph_iff
        spec element index).mp hselect |>.2
    exact hleast.2.1

/-- An internally collected family of stage injections combines to an
injection of the whole omega union into `omega x kappa`. -/
theorem injects_parametricUniformOmegaUnion_to_prod_of_injectionFamily
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      omegaLCarrier graphFamily)
    (hinjections : forall n : Nat, forall injection : LCarrier.{u},
      GraphValue LMem injectionFamily (natLCarrier n) injection ->
        IsInjection LMem injection (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec)
      (prodLCarrier omegaLCarrier kappa) := by
  have hfibers : IsFiberInjectionFamily LMem
      (parametricUniformOmegaFamilyData spec).graph
      injectionFamily omegaLCarrier
      (parametricUniformOmegaFamilyData spec).family
      graphFamily kappa := by
    refine ⟨(parametricUniformOmegaFamilyData spec).isFunctionGraph,
      hinjectionFamily, ?_⟩
    intro index fiber injection hindex hfiber hinjection
    rcases value_eq_of_family_graphValue spec hindex hfiber with
      ⟨n, hindexEq, hfiberEq⟩
    subst index
    subst fiber
    exact hinjections n injection hinjection
  have hinjects := injects_sUnion_to_prod_lCarrier
    (parametricUniformOmegaSelectorGraph_selectsContainingFiber spec)
    hfibers
  simpa only [parametricUniformOmegaUnion] using hinjects

/-- If `kappa` contains omega and absorbs its square, the internally
collected omega union is bounded by `kappa`. -/
theorem injects_parametricUniformOmegaUnion_of_injectionFamily
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      omegaLCarrier graphFamily)
    (hinjections : forall n : Nat, forall injection : LCarrier.{u},
      GraphValue LMem injectionFamily (natLCarrier n) injection ->
        IsInjection LMem injection (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec) kappa := by
  have homegaInjection : Injects LMem omegaLCarrier kappa :=
    injects_of_subset_lCarrier homega
  have hkappaInjection : Injects LMem kappa kappa :=
    injects_refl_lCarrier kappa
  have hproduct : Injects LMem
      (prodLCarrier omegaLCarrier kappa)
      (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier homegaInjection hkappaInjection
  exact (injects_parametricUniformOmegaUnion_to_prod_of_injectionFamily
    spec hinjectionFamily hinjections).trans_lCarrier
      (hproduct.trans_lCarrier hsquare)

end

end Constructible.Model
