/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ParametricUniformOmegaInjectionFamily
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalStageInjectionFamily
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FunctionGraphFormulaLCarrier

/-!
# Canonical internal injection families for constructible stages

Assume that every `L_alpha`, for `alpha < limit`, has an internally
represented injection into `kappa`.  All such graphs are subsets of
`L_limit x kappa`, so the genuine internal powerset of that product is a
single set bounding every candidate.

A fixed first-order formula obtains `L_alpha` through the already internal
`stageValueGraph limit`, and selects the least candidate injection graph in
the canonical witness order on the bounding powerset.  Replacement over the
internal ordinal `limit` then produces the actual family graph.  External
ordinal decoding is used only to prove totality and correctness of this fixed
formula; it is not used as the collected family.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## A common internal bound for all candidate graphs -/

/-- Every candidate graph is bounded by `L_limit x kappa`. -/
def canonicalStageInjectionGraphContainer
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier (stageLCarrier limit) kappa

/-- The genuine internal powerset of the common graph container. -/
noncomputable def canonicalStageInjectionPower
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose
    (exists_powerSetLCarrier
      (canonicalStageInjectionGraphContainer limit kappa))

@[simp]
theorem mem_canonicalStageInjectionPower_iff
    (limit : Ordinal.{u}) (kappa graph : LCarrier.{u}) :
    graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 ↔
      graph.1 ⊆ (canonicalStageInjectionGraphContainer limit kappa).1 :=
  Classical.choose_spec
    (exists_powerSetLCarrier
      (canonicalStageInjectionGraphContainer limit kappa)) graph

/-! ## Candidate sets -/

/-- Layout `[stage,kappa,graph]`: `graph` injects `stage` into `kappa`. -/
def canonicalStageInjectionCandidateFormula : FOFormula 3 :=
  injectionAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_canonicalStageInjectionCandidateFormula
    (stage kappa graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem canonicalStageInjectionCandidateFormula
        ![stage, kappa, graph] ↔
      IsInjection LMem graph stage kappa := by
  exact satisfies_injectionAt LMem
    (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![stage, kappa, graph]

/-- The separated set of candidate injections for one displayed stage. -/
noncomputable def canonicalStageInjectionCandidates
    (limit : Ordinal.{u}) (kappa stage : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose
    (exists_separationLCarrier
      canonicalStageInjectionCandidateFormula ![stage, kappa]
      (canonicalStageInjectionPower limit kappa))

@[simp]
theorem mem_canonicalStageInjectionCandidates_iff
    (limit : Ordinal.{u}) (kappa stage graph : LCarrier.{u}) :
    graph.1 ∈ (canonicalStageInjectionCandidates limit kappa stage).1 ↔
      graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 ∧
        IsInjection LMem graph stage kappa := by
  rw [canonicalStageInjectionCandidates,
    Classical.choose_spec
      (exists_separationLCarrier
        canonicalStageInjectionCandidateFormula ![stage, kappa]
        (canonicalStageInjectionPower limit kappa)) graph]
  change _ ∧ FOFormula.Satisfies LMem
    canonicalStageInjectionCandidateFormula ![stage, kappa, graph] ↔ _
  rw [satisfies_canonicalStageInjectionCandidateFormula]

/-! ## The fixed canonical-selection formula -/

/--
Layout `[stageGraph,kappa,power,order,index,injection]`.

The hidden variable is the exact value of `stageGraph` at `index`.
`injection` is the least member of `power` which injects that stage into
`kappa`.
-/
def canonicalStageInjectionFormula : FOFormula 6 :=
  let stageGraph : Fin 6 := 0
  let kappa : Fin 6 := 1
  let power : Fin 6 := 2
  let order : Fin 6 := 3
  let index : Fin 6 := 4
  let injection : Fin 6 := 5
  .ex <| .conj
    (graphValueFormulaAt stageGraph.castSucc index.castSucc (Fin.last 6))
    (.conj
      (.mem injection.castSucc power.castSucc)
      (.conj
        (injectionAt injection.castSucc (Fin.last 6) kappa.castSucc)
        (.all <| FOFormula.imp
          (.conj
            (.mem (Fin.last 7) power.castSucc.castSucc)
            (injectionAt (Fin.last 7) (Fin.last 6).castSucc
              kappa.castSucc.castSucc))
          (.neg
            (graphRelAt order.castSucc.castSucc
              (Fin.last 7) injection.castSucc.castSucc)))))

/-- The four fixed parameters of the canonical-selection formula. -/
def canonicalStageInjectionParams
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![stageValueGraph limit, kappa,
    canonicalStageInjectionPower limit kappa,
    canonicalWitnessOrder (canonicalStageInjectionPower limit kappa)]

/-- Exact semantic content of the fixed selection formula. -/
def IsCanonicalStageInjection
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) : Prop :=
  ∃ stage : LCarrier.{u},
    GraphRel (stageValueGraph limit) index stage ∧
      injection.1 ∈ (canonicalStageInjectionPower limit kappa).1 ∧
      IsInjection LMem injection stage kappa ∧
      ∀ other : LCarrier.{u},
        other.1 ∈ (canonicalStageInjectionPower limit kappa).1 →
        IsInjection LMem other stage kappa →
          ¬ GraphRel
            (canonicalWitnessOrder
              (canonicalStageInjectionPower limit kappa))
            other injection

private theorem canonicalStageInjection_assignment
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalStageInjectionParams limit kappa) index)
        injection =
      ![stageValueGraph limit, kappa,
        canonicalStageInjectionPower limit kappa,
        canonicalWitnessOrder
          (canonicalStageInjectionPower limit kappa),
        index, injection] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_canonicalStageInjectionFormula
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) :
    FOFormula.Satisfies LMem canonicalStageInjectionFormula
        (snoc (snoc
          (canonicalStageInjectionParams limit kappa) index) injection) ↔
      IsCanonicalStageInjection limit kappa index injection := by
  rw [canonicalStageInjection_assignment]
  simp only [canonicalStageInjectionFormula, FOFormula.Satisfies,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_injectionAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphRelAt,
    snoc_last, snoc_castSucc]
  simp only [and_imp]
  change
    IsCanonicalStageInjection limit kappa index injection ↔
      IsCanonicalStageInjection limit kappa index injection
  rfl

/-! ## Existence and uniqueness of the canonical graph -/

private theorem stageInjection_graph_mem_power
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    {ordinal : Ordinal.{u}} (hordinal : ordinal < limit)
    {graph : LCarrier.{u}}
    (hgraph :
      IsInjection LMem graph (stageLCarrier ordinal) kappa) :
    graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 := by
  apply (mem_canonicalStageInjectionPower_iff
    limit kappa graph).mpr
  intro pairRaw hpair
  let pair : LCarrier.{u} :=
    ⟨pairRaw, mem_L_of_mem hpair graph.2⟩
  rcases hgraph.1 pair hpair with
    ⟨input, hinput, output, houtput, hpairCoordinates⟩
  have hinputLimit :
      input.1 ∈ (stageLCarrier limit).1 := by
    exact LStageZF_mono hordinal.le hinput
  apply ZFSet.mem_prod.mpr
  exact ⟨input.1, hinputLimit, output.1, houtput,
    (isKuratowskiPairOf_lCarrier_iff
      pair input output).mp hpairCoordinates⟩

/--
At each genuine ordinal index below `limit`, the fixed formula has exactly
one output: the canonical least injection graph.
-/
theorem canonicalStageInjectionFormula_existsUnique
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (ordinal : Ordinal.{u}) (hordinal : ordinal < limit)
    (hinjects :
      Injects LMem (stageLCarrier ordinal) kappa) :
    ExistsUnique fun injection : LCarrier.{u} =>
      FOFormula.Satisfies LMem canonicalStageInjectionFormula
        (snoc (snoc (canonicalStageInjectionParams limit kappa)
          (ordinalLCarrier ordinal)) injection) := by
  let stage := stageLCarrier ordinal
  let power := canonicalStageInjectionPower limit kappa
  let candidates :=
    canonicalStageInjectionCandidates limit kappa stage
  have hcandidatesSubset : ∀ graph : LCarrier.{u},
      graph.1 ∈ candidates.1 →
        graph.1 ∈ (canonicalWitnessStage power).1 := by
    intro graph hgraph
    exact seed_subset_canonicalWitnessStage power
      ((mem_canonicalStageInjectionCandidates_iff
        limit kappa stage graph).mp hgraph).1
  have hcandidatesNonempty : ∃ graph : LCarrier.{u},
      graph.1 ∈ candidates.1 := by
    rcases hinjects with ⟨graph, hgraph⟩
    exact ⟨graph,
      (mem_canonicalStageInjectionCandidates_iff
        limit kappa stage graph).mpr
          ⟨stageInjection_graph_mem_power
            limit kappa hordinal hgraph, hgraph⟩⟩
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders power)
      hcandidatesSubset hcandidatesNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_canonicalStageInjectionFormula
      limit kappa (ordinalLCarrier ordinal) minimum).mpr
    have hstageGraph :
        GraphValue LMem (stageValueGraph limit)
          (ordinalLCarrier ordinal) stage := by
      apply (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) stage).mpr
      exact
        ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
            limit ordinal).mpr hordinal,
          (stageValueAt_ordinal_iff ordinal stage).mpr rfl⟩
    have hcandidate :=
      (mem_canonicalStageInjectionCandidates_iff
        limit kappa stage minimum).mp hminimum.1
    exact ⟨stage,
      (graphValue_lCarrier_iff_graphRel
        (stageValueGraph limit) (ordinalLCarrier ordinal) stage).mp
          hstageGraph,
      hcandidate.1, hcandidate.2,
      fun other hotherPower hotherInjection =>
        hminimum.2 other
          ((mem_canonicalStageInjectionCandidates_iff
            limit kappa stage other).mpr
              ⟨hotherPower, hotherInjection⟩)⟩
  · intro other hother
    rcases
        (satisfies_canonicalStageInjectionFormula
          limit kappa (ordinalLCarrier ordinal) other).mp hother with
      ⟨otherStage, hotherStageGraph, hotherPower,
        hotherInjection, hotherMinimal⟩
    have hotherStageValue :=
      (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) otherStage).mp
          ((graphValue_lCarrier_iff_graphRel
            (stageValueGraph limit) (ordinalLCarrier ordinal)
              otherStage).mpr hotherStageGraph)
    have hotherStageEq : otherStage = stage :=
      (stageValueAt_ordinal_iff ordinal otherStage).mp
        hotherStageValue.2
    subst otherStage
    apply hminimumUnique other
    exact
      ⟨(mem_canonicalStageInjectionCandidates_iff
          limit kappa stage other).mpr
            ⟨hotherPower, hotherInjection⟩,
        fun graph hgraph =>
          hotherMinimal graph
            ((mem_canonicalStageInjectionCandidates_iff
              limit kappa stage graph).mp hgraph).1
            ((mem_canonicalStageInjectionCandidates_iff
              limit kappa stage graph).mp hgraph).2⟩

/-! ## Formula data and the internally collected family -/

/--
The pointwise internal injections produce the exact fixed-formula data
required by `InternalStageInjectionFormulaData`.
-/
noncomputable def canonicalStageInjectionFormulaData
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (hinjects : ∀ ordinal : Ordinal.{u}, ordinal < limit →
      Injects LMem (stageLCarrier ordinal) kappa) :
    InternalStageInjectionFormulaData limit kappa where
  arity := 4
  formula := canonicalStageInjectionFormula
  params := canonicalStageInjectionParams limit kappa
  existsUnique_output := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    exact canonicalStageInjectionFormula_existsUnique
      limit kappa ordinal hordinal (hinjects ordinal hordinal)
  output_isInjection := by
    intro ordinal hordinal injection hformula
    rcases
        (satisfies_canonicalStageInjectionFormula
          limit kappa (ordinalLCarrier ordinal) injection).mp hformula with
      ⟨stage, hstageGraph, _hpower, hinjection, _hminimal⟩
    have hstageValue :=
      (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) stage).mp
          ((graphValue_lCarrier_iff_graphRel
            (stageValueGraph limit) (ordinalLCarrier ordinal) stage).mpr
              hstageGraph)
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hstageValue.2
    simpa only [hstageEq] using hinjection

/-- Replacement constructs the genuine indexed family and its range. -/
theorem exists_canonicalStageInjectionFamily
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (hinjects : ∀ ordinal : Ordinal.{u}, ordinal < limit →
      Injects LMem (stageLCarrier ordinal) kappa) :
    ∃ injectionFamily graphFamily : LCarrier.{u},
      IsFunctionGraph LMem injectionFamily
        (ordinalLCarrier limit) graphFamily ∧
      ∀ ordinal : Ordinal.{u}, ordinal < limit →
        ∀ injection : LCarrier.{u},
          GraphValue LMem injectionFamily
            (ordinalLCarrier ordinal) injection →
          IsInjection LMem injection (stageLCarrier ordinal) kappa :=
  exists_internalStageInjectionFamily_of_formulaData
    (canonicalStageInjectionFormulaData limit kappa hinjects)

/-! ## The exact Hartogs interface -/

/--
The canonical family removes the formula-uniformity obligation from the
Hartogs bound.  The pointwise stage bound remains explicit; proving it
requires the separate zero/successor/limit transfinite cardinal induction.
-/
theorem hartogsStageBound_of_pointwise_stage_injects
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : ∀ ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa →
        Injects LMem (stageLCarrier ordinal) kappa) :
    HartogsStageBound kappa :=
  hartogsStageBound_of_internalStageInjectionFormulaData
    kappa hcardinal homega
      (canonicalStageInjectionFormulaData
        (internalHartogsOrdinal kappa) kappa hinjects)

end

end Constructible.ContinuumFormula
