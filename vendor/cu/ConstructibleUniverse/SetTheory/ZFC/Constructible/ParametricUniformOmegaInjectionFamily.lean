/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ParametricUniformOmegaSelector
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.PowerSet
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FullSkolemHull

/-!
# Canonically collecting injections along a uniform omega family

Suppose every value of a uniformly definable omega family has some internally
represented injection into `kappa`.  This file does not externally choose
those graphs.  It bounds all candidate graphs by the genuine internal
powerset of `H x kappa`, selects the least candidate in the canonical stage
order by one fixed first-order formula, and applies Replacement over the
internal omega.  The result is the actual indexed family of injection graphs
needed by the cardinal-union argument.
-/

@[expose] public section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- A common internal container for graphs from family values into `kappa`. -/
def parametricUniformOmegaInjectionGraphContainer
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier (parametricUniformOmegaUnion spec) kappa

/-- The genuine internal powerset which bounds all constructible candidate
injection graphs. -/
noncomputable def parametricUniformOmegaInjectionPower
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_powerSetLCarrier
    (parametricUniformOmegaInjectionGraphContainer spec kappa))

@[simp]
theorem mem_parametricUniformOmegaInjectionPower_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa graph : LCarrier.{u}) :
    graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 <->
      graph.1 ⊆
        (parametricUniformOmegaInjectionGraphContainer spec kappa).1 :=
  Classical.choose_spec (exists_powerSetLCarrier
    (parametricUniformOmegaInjectionGraphContainer spec kappa)) graph

/-! ## Candidate sets for the minimum argument -/

/-- Layout `[stage,kappa,graph]`: `graph` is an injection from `stage` to
`kappa`. -/
def uniformOmegaInjectionCandidateFormula : FOFormula 3 :=
  injectionAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_uniformOmegaInjectionCandidateFormula
    (stage kappa graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem uniformOmegaInjectionCandidateFormula
        ![stage, kappa, graph] <->
      IsInjection LMem graph stage kappa := by
  exact satisfies_injectionAt LMem
    (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![stage, kappa, graph]

/-- The actual subset of the common power consisting of injection graphs for
one displayed stage. -/
noncomputable def uniformOmegaInjectionCandidates
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa stage : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    uniformOmegaInjectionCandidateFormula ![stage, kappa]
    (parametricUniformOmegaInjectionPower spec kappa))

@[simp]
theorem mem_uniformOmegaInjectionCandidates_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa stage graph : LCarrier.{u}) :
    graph.1 ∈ (uniformOmegaInjectionCandidates spec kappa stage).1 <->
      graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 /\
        IsInjection LMem graph stage kappa := by
  rw [uniformOmegaInjectionCandidates,
    Classical.choose_spec (exists_separationLCarrier
      uniformOmegaInjectionCandidateFormula ![stage, kappa]
      (parametricUniformOmegaInjectionPower spec kappa)) graph]
  change _ /\ FOFormula.Satisfies LMem
    uniformOmegaInjectionCandidateFormula ![stage, kappa, graph] <-> _
  rw [satisfies_uniformOmegaInjectionCandidateFormula]

/-! ## The fixed formula selecting the canonical graph -/

/-- Place the family-value formula in the context obtained after adjoining
the hidden stage variable to
`[specParams,H,kappa,power,order,index,injection]`. -/
def uniformOmegaInjectionStageRename (parameterCount : Nat) :
    Fin (parameterCount + 2) -> Fin (parameterCount + 7) :=
  Fin.lastCases (Fin.last (parameterCount + 6))
    (fun i => Fin.lastCases
      (⟨parameterCount + 4, by omega⟩ : Fin (parameterCount + 7))
      (fun j => Fin.castLE (by omega) j) i)

/--
Layout `[specParams,H,kappa,power,order,index,injection]`.  The hidden stage
is the value of the uniform family at `index`; `injection` is the least graph
in `power` which injects that stage into `kappa`.
-/
def canonicalUniformOmegaInjectionFormula
    {parameterCount : Nat}
    (familyFormula : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 6) :=
  let kappa : Fin (parameterCount + 6) := ⟨parameterCount + 1, by omega⟩
  let power : Fin (parameterCount + 6) := ⟨parameterCount + 2, by omega⟩
  let order : Fin (parameterCount + 6) := ⟨parameterCount + 3, by omega⟩
  let injection : Fin (parameterCount + 6) :=
    ⟨parameterCount + 5, by omega⟩
  .ex <| .conj
    (FOFormula.rename (uniformOmegaInjectionStageRename parameterCount)
      familyFormula)
    (.conj
      (.mem injection.castSucc power.castSucc)
      (.conj
        (injectionAt injection.castSucc (Fin.last (parameterCount + 6))
          kappa.castSucc)
        (.all <| FOFormula.imp
          (.conj
            (.mem (Fin.last (parameterCount + 7))
              power.castSucc.castSucc)
            (injectionAt (Fin.last (parameterCount + 7))
              (Fin.last (parameterCount + 6)).castSucc
              kappa.castSucc.castSucc))
          (.neg (graphRelAt order.castSucc.castSucc
            (Fin.last (parameterCount + 7))
            injection.castSucc.castSucc)))))

/-- Fixed parameters of the canonical-injection formula. -/
def canonicalUniformOmegaInjectionParams
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : Tuple LCarrier.{u} (parameterCount + 4) :=
  snoc (snoc (snoc (snoc spec.params
    (parametricUniformOmegaUnion spec)) kappa)
    (parametricUniformOmegaInjectionPower spec kappa))
    (canonicalWitnessOrder
      (parametricUniformOmegaInjectionPower spec kappa))

/-- Semantic content of the canonical-injection formula. -/
def IsCanonicalUniformOmegaInjection
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) : Prop :=
  exists stage : LCarrier.{u},
    FOFormula.Satisfies LMem spec.formula
      (snoc (snoc spec.params index) stage) /\
    injection.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 /\
    IsInjection LMem injection stage kappa /\
    forall other : LCarrier.{u},
      other.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 ->
      IsInjection LMem other stage kappa ->
        Not (GraphRel
          (canonicalWitnessOrder
            (parametricUniformOmegaInjectionPower spec kappa))
          other injection)

private theorem canonical_injection_stage_assignment
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection stage : LCarrier.{u}) :
    (fun i =>
      snoc
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa)
            index)
          injection)
        stage
        (uniformOmegaInjectionStageRename parameterCount i)) =
      snoc (snoc spec.params index) stage := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [uniformOmegaInjectionStageRename, Fin.lastCases_last,
      snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [uniformOmegaInjectionStageRename,
        Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [show (⟨parameterCount + 4, by omega⟩ :
          Fin (parameterCount + 7)) =
          (Fin.last (parameterCount + 4)).castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [snoc_castSucc, snoc_last]
    · simp only [uniformOmegaInjectionStageRename,
        Fin.lastCases_castSucc]
      rw [show Fin.castLE (by omega) k =
          k.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [canonicalUniformOmegaInjectionParams, snoc_castSucc]

private theorem canonical_injection_assignment_kappa
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 1, by omega⟩ :
          Fin (parameterCount + 6)) = kappa := by
  rw [show (⟨parameterCount + 1, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

private theorem canonical_injection_assignment_power
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 2, by omega⟩ :
          Fin (parameterCount + 6)) =
      parametricUniformOmegaInjectionPower spec kappa := by
  rw [show (⟨parameterCount + 2, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

private theorem canonical_injection_assignment_order
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 3, by omega⟩ :
          Fin (parameterCount + 6)) =
      canonicalWitnessOrder
        (parametricUniformOmegaInjectionPower spec kappa) := by
  rw [show (⟨parameterCount + 3, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 3)).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

private theorem canonical_injection_assignment_injection
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 5, by omega⟩ :
          Fin (parameterCount + 6)) = injection := by
  rw [show (⟨parameterCount + 5, by omega⟩ :
      Fin (parameterCount + 6)) = Fin.last (parameterCount + 5) by
    apply Fin.ext
    rfl]
  simp only [snoc_last]

@[simp]
theorem satisfies_canonicalUniformOmegaInjectionFormula
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (canonicalUniformOmegaInjectionFormula spec.formula)
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
          injection) <->
      IsCanonicalUniformOmegaInjection spec kappa index injection := by
  simp only [canonicalUniformOmegaInjectionFormula,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    satisfies_injectionAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphRelAt,
    IsCanonicalUniformOmegaInjection, snoc_last, snoc_castSucc]
  apply exists_congr
  intro stage
  rw [canonical_injection_stage_assignment]
  rw [canonical_injection_assignment_injection,
    canonical_injection_assignment_power,
    canonical_injection_assignment_kappa,
    canonical_injection_assignment_order]
  change
    (FOFormula.Satisfies LMem spec.formula
        (snoc (snoc spec.params index) stage) /\
      injection.1 ∈
        (parametricUniformOmegaInjectionPower spec kappa).1 /\
      IsInjection LMem injection stage kappa /\
      forall other : LCarrier.{u},
        (other.1 ∈
          (parametricUniformOmegaInjectionPower spec kappa).1 /\
          IsInjection LMem other stage kappa) ->
          Not (GraphRel
            (canonicalWitnessOrder
              (parametricUniformOmegaInjectionPower spec kappa))
            other injection)) <-> _
  simp only [and_imp]

/-! ## Existence, uniqueness, and Replacement -/

private theorem injection_graph_mem_power
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) (n : Nat)
    {graph : LCarrier.{u}}
    (hgraph : IsInjection LMem graph (spec.value n) kappa) :
    graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 := by
  apply (mem_parametricUniformOmegaInjectionPower_iff
    spec kappa graph).mpr
  intro pairRaw hpair
  let pair : LCarrier.{u} :=
    ⟨pairRaw, mem_L_of_mem hpair graph.2⟩
  have hbetween := hgraph.1 pair hpair
  rcases hbetween with ⟨input, hinput, output, houtput, hpairs⟩
  have hinputUnion := value_subset_parametricUniformOmegaUnion spec n hinput
  apply ZFSet.mem_prod.mpr
  exact ⟨input.1, hinputUnion, output.1, houtput,
    (isKuratowskiPairOf_lCarrier_iff pair input output).mp hpairs⟩

/-- If the displayed family value has an internal injection, the fixed
formula has exactly one output: the canonical least such graph. -/
theorem canonicalUniformOmegaInjectionFormula_existsUnique
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) (n : Nat)
    (hinjects : Injects LMem (spec.value n) kappa) :
    ExistsUnique fun injection : LCarrier.{u} =>
      FOFormula.Satisfies LMem
        (canonicalUniformOmegaInjectionFormula spec.formula)
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa)
            (natLCarrier n))
          injection) := by
  let stage := spec.value n
  let power := parametricUniformOmegaInjectionPower spec kappa
  let candidates := uniformOmegaInjectionCandidates spec kappa stage
  have hcandidatesSubset : forall graph : LCarrier.{u},
      graph.1 ∈ candidates.1 ->
        graph.1 ∈ (canonicalWitnessStage power).1 := by
    intro graph hgraph
    exact seed_subset_canonicalWitnessStage power
      ((mem_uniformOmegaInjectionCandidates_iff
        spec kappa stage graph).mp hgraph).1
  have hcandidatesNonempty : exists graph : LCarrier.{u},
      graph.1 ∈ candidates.1 := by
    rcases hinjects with ⟨graph, hgraph⟩
    exact ⟨graph, (mem_uniformOmegaInjectionCandidates_iff
      spec kappa stage graph).mpr
        ⟨injection_graph_mem_power spec kappa n hgraph, hgraph⟩⟩
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders power)
      hcandidatesSubset hcandidatesNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_canonicalUniformOmegaInjectionFormula
      spec kappa (natLCarrier n) minimum).mpr
    refine ⟨stage, (spec.realizes n stage).mpr rfl, ?_⟩
    have hcandidate := (mem_uniformOmegaInjectionCandidates_iff
      spec kappa stage minimum).mp hminimum.1
    exact ⟨hcandidate.1, hcandidate.2, fun other hotherPower hotherInjection =>
      hminimum.2 other
        ((mem_uniformOmegaInjectionCandidates_iff
          spec kappa stage other).mpr
            ⟨hotherPower, hotherInjection⟩)⟩
  · intro other hother
    have hotherSemantic :=
      (satisfies_canonicalUniformOmegaInjectionFormula
        spec kappa (natLCarrier n) other).mp hother
    rcases hotherSemantic with
      ⟨otherStage, hotherStage, hotherPower,
        hotherInjection, hotherMinimal⟩
    have hotherStageEq : otherStage = stage :=
      (spec.realizes n otherStage).mp hotherStage
    subst otherStage
    apply hminimumUnique other
    exact ⟨(mem_uniformOmegaInjectionCandidates_iff
        spec kappa stage other).mpr
          ⟨hotherPower, hotherInjection⟩,
      fun z hz =>
        hotherMinimal z
          ((mem_uniformOmegaInjectionCandidates_iff
            spec kappa stage z).mp hz).1
          ((mem_uniformOmegaInjectionCandidates_iff
            spec kappa stage z).mp hz).2⟩

/-- The internally collected canonical injection graphs. -/
structure ParametricUniformOmegaInjectionFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) where
  injectionFamily : LCarrier.{u}
  graphFamily : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem injectionFamily
    omegaLCarrier graphFamily
  values_areInjections : forall n : Nat, forall injection : LCarrier.{u},
    GraphValue LMem injectionFamily (natLCarrier n) injection ->
      IsInjection LMem injection (spec.value n) kappa

/-- Replacement produces the genuine family graph from pointwise internal
injections. -/
theorem exists_parametricUniformOmegaInjectionFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u})
    (hinjects : forall n : Nat, Injects LMem (spec.value n) kappa) :
    Nonempty (ParametricUniformOmegaInjectionFamilyData spec kappa) := by
  let params := canonicalUniformOmegaInjectionParams spec kappa
  have hfun : forall index : LCarrier.{u}, index.1 ∈ omegaLCarrier.1 ->
      ExistsUnique fun injection : LCarrier.{u} =>
        FOFormula.Satisfies LMem
          (canonicalUniformOmegaInjectionFormula spec.formula)
          (snoc (snoc params index) injection) := by
    intro index hindex
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    simpa only [params] using
      canonicalUniformOmegaInjectionFormula_existsUnique
        spec kappa n (hinjects n)
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      (canonicalUniformOmegaInjectionFormula spec.formula)
      params omegaLCarrier hfun with
    ⟨injectionFamily, graphFamily, hfamily, _hrange, hvalue⟩
  refine ⟨{
    injectionFamily := injectionFamily
    graphFamily := graphFamily
    isFunctionGraph := hfamily
    values_areInjections := ?_
  }⟩
  intro n injection hinjection
  have hformula := (hvalue (natLCarrier n) injection).mp hinjection |>.2
  have hsemantic :=
    (satisfies_canonicalUniformOmegaInjectionFormula
      spec kappa (natLCarrier n) injection).mp <| by
        simpa only [params] using hformula
  rcases hsemantic with
    ⟨stage, hstage, _hinjectionPower, hinjectionGraph, _hminimal⟩
  have hstageEq : stage = spec.value n :=
    (spec.realizes n stage).mp hstage
  simpa only [hstageEq] using hinjectionGraph

/-- The pointwise cardinal bound therefore yields an actual injection of the
whole omega union into `omega x kappa`. -/
theorem injects_parametricUniformOmegaUnion_to_prod_of_pointwise
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u})
    (hinjects : forall n : Nat, Injects LMem (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec)
      (prodLCarrier omegaLCarrier kappa) := by
  rcases exists_parametricUniformOmegaInjectionFamilyData
      spec kappa hinjects with ⟨data⟩
  exact injects_parametricUniformOmegaUnion_to_prod_of_injectionFamily
    spec data.isFunctionGraph data.values_areInjections

/-- With the standard infinite-cardinal absorption hypotheses, the omega
union itself injects into `kappa`. -/
theorem injects_parametricUniformOmegaUnion_of_pointwise
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hsquare : Injects LMem (prodLCarrier kappa kappa) kappa)
    (hinjects : forall n : Nat, Injects LMem (spec.value n) kappa) :
    Injects LMem (parametricUniformOmegaUnion spec) kappa := by
  rcases exists_parametricUniformOmegaInjectionFamilyData
      spec kappa hinjects with ⟨data⟩
  exact injects_parametricUniformOmegaUnion_of_injectionFamily
    spec homega hsquare data.isFunctionGraph data.values_areInjections

end

end Constructible.Model
