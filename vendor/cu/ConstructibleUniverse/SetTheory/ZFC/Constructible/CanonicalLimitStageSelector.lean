/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalStageCardinalUnion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MinimalStage

/-!
# The canonical containing-stage selector at a limit

For an element of a nonzero limit stage, this file selects the least earlier
stage containing it.  The selector is an actual constructible graph obtained
by Separation from a fixed first-order formula.  The external `firstStage`
operation appears only in the proof that this graph is total and single
valued; it is not used as an internal graph witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage contains an element -/

/-- The stage at `index` contains `x`. -/
def StageContains (x index : LCarrier.{u}) : Prop :=
  exists stage : LCarrier.{u},
    StageValueAt index stage /\ x.1 ∈ stage.1

/-- Layout `(fixed13,x,index)`.  The hidden variable is the stage value. -/
def stageContainsAtFormula : FOFormula 15 :=
  .ex (.conj
    (FOFormula.rename boundedStageValueAtRename stageValueAtFormula)
    (.mem (13 : Fin 16) (15 : Fin 16)))

/-- The direct assignment for the stage-containment relation. -/
def stageContainsAtAssignment (x index : LCarrier.{u}) :
    Tuple LCarrier.{u} 15 :=
  stageValueAtAssignment x index

@[simp]
theorem satisfies_stageContainsAtFormula
    (x index : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageContainsAtFormula
        (stageContainsAtAssignment x index) ↔
      StageContains x index := by
  simp only [stageContainsAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, StageContains]
  apply exists_congr
  intro stage
  change
    (FOFormula.Satisfies LMem stageValueAtFormula
        (fun i => boundedStageValueAtAssignment x index stage
          (boundedStageValueAtRename i)) /\
      x.1 ∈ stage.1) ↔ _
  rw [comp_boundedStageValueAtRename,
    satisfies_stageValueAtFormula]

/-- At a canonical ordinal index, containment is ordinary membership in the
corresponding constructible stage. -/
theorem stageContains_ordinal_iff
    (x : LCarrier.{u}) (ordinal : Ordinal.{u}) :
    StageContains x (ordinalLCarrier ordinal) ↔
      x.1 ∈ LStageZF ordinal := by
  constructor
  · rintro ⟨stage, hstage, hx⟩
    rw [(stageValueAt_ordinal_iff ordinal stage).mp hstage] at hx
    exact hx
  · intro hx
    exact ⟨stageLCarrier ordinal,
      (stageValueAt_ordinal_iff ordinal
        (stageLCarrier ordinal)).mpr rfl, hx⟩

/-! ## Least containing indices -/

/-- Rename `(fixed13,x,index)` into the context
`(fixed13,bound,x,current,earlier)`, selecting the last variable as the new
index. -/
def earlierStageContainsRename : Fin 15 -> Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (14 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

private theorem comp_earlierStageContainsRename
    (bound x current earlier : LCarrier.{u}) :
    (fun i => snoc
      (boundedStageValueAtAssignment bound x current) earlier
        (earlierStageContainsRename i)) =
      stageContainsAtAssignment x earlier := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [earlierStageContainsRename, Fin.lastCases_castSucc]
      rw [show Fin.castLE (by decide) i13 =
          i13.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [boundedStageValueAtAssignment,
        stageContainsAtAssignment, stageValueAtAssignment, snoc_castSucc]

/-- Semantic predicate: `index` is the least member of `bound` whose stage
contains `x`. -/
def IsLeastContainingStage
    (bound x index : LCarrier.{u}) : Prop :=
  index.1 ∈ bound.1 /\
    StageContains x index /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
        Not (StageContains x earlier)

/-- Layout `(fixed13,bound,x,index)`. -/
def leastContainingStageFormula : FOFormula 16 :=
  .conj
    (.mem (15 : Fin 16) (13 : Fin 16))
    (.conj
      (FOFormula.rename boundedStageValueAtRename stageContainsAtFormula)
      (FOFormula.boundedAll (15 : Fin 16)
        (.neg (FOFormula.rename earlierStageContainsRename
          stageContainsAtFormula))))

/-- Direct assignment for the least-containing-stage formula. -/
def leastContainingStageAssignment
    (bound x index : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  boundedStageValueAtAssignment bound x index

@[simp]
theorem satisfies_leastContainingStageFormula
    (bound x index : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastContainingStageFormula
        (leastContainingStageAssignment bound x index) ↔
      IsLeastContainingStage bound x index := by
  simp only [leastContainingStageFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_boundedAll,
    IsLeastContainingStage, leastContainingStageAssignment]
  rw [comp_boundedStageValueAtRename]
  rw [show FOFormula.Satisfies LMem stageContainsAtFormula
        (stageValueAtAssignment x index) ↔ StageContains x index by
      simpa only [stageContainsAtAssignment] using
        (satisfies_stageContainsAtFormula x index)]
  apply and_congr_right
  intro _hindex
  apply and_congr_right
  intro _hcontains
  apply forall_congr'
  intro earlier
  rw [comp_earlierStageContainsRename,
    satisfies_stageContainsAtFormula]
  change (earlier.1 ∈ index.1 -> Not (StageContains x earlier)) ↔ _
  rfl

/-! ## The Separation-generated selector graph -/

/-- The actual constructible graph selecting the least containing stage. -/
noncomputable def leastContainingStageGraph
    (limit : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.canonicalDefinableRelationGraph
    leastContainingStageFormula
    (snoc Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier limit))
    (stageLCarrier limit)

@[simp]
theorem graphValue_leastContainingStageGraph_iff
    (limit : Ordinal.{u}) (x index : LCarrier.{u}) :
    GraphValue LMem (leastContainingStageGraph limit) x index ↔
      x.1 ∈ (stageLCarrier limit).1 /\
        IsLeastContainingStage (ordinalLCarrier limit) x index := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [leastContainingStageGraph,
    Constructible.Model.graphRel_canonicalDefinableRelationGraph_iff]
  change
    (x.1 ∈ (stageLCarrier limit).1 /\
      index.1 ∈ (stageLCarrier limit).1 /\
        FOFormula.Satisfies LMem leastContainingStageFormula
          (leastContainingStageAssignment
            (ordinalLCarrier limit) x index)) ↔ _
  rw [satisfies_leastContainingStageFormula]
  constructor
  · rintro ⟨hx, _hindexStage, hleast⟩
    exact ⟨hx, hleast⟩
  · rintro ⟨hx, hleast⟩
    have hindexStage : index.1 ∈ (stageLCarrier limit).1 := by
      change index.1 ∈ LStageZF limit
      exact (ordinal_stage_invariants limit).2 hleast.1
    exact ⟨hx, hindexStage, hleast⟩

/-- An element of a nonzero limit stage has first occurrence strictly below
that limit. -/
theorem firstStage_lt_of_mem_limitStage
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (x : LCarrier.{u}) (hx : x.1 ∈ (stageLCarrier limit).1) :
    firstStage x.1 x.2 < limit := by
  change x.1 ∈ LStageZF limit at hx
  rcases (mem_LStageZF_limit_iff hl).mp hx with
    ⟨ordinal, hordinal, hxOrdinal⟩
  exact (firstStage_le x.2 hxOrdinal).trans_lt hordinal

/-- The least-containing-stage graph is a total internally represented
function from the limit stage to its ordinal index set. -/
theorem leastContainingStageGraph_isFunctionGraph
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    IsFunctionGraph LMem (leastContainingStageGraph limit)
      (stageLCarrier limit) (ordinalLCarrier limit) := by
  constructor
  · intro pair hpair
    have hmem :=
      (Constructible.Model.mem_canonicalDefinableRelationGraph_iff
        leastContainingStageFormula
        (snoc Constructible.Model.stageHistoryFixedParameters
          (ordinalLCarrier limit))
        (stageLCarrier limit) pair).mp hpair
    rcases hmem with
      ⟨x, index, hx, _hindexStage, hpairEq, hformula⟩
    have hleast :=
      (satisfies_leastContainingStageFormula
        (ordinalLCarrier limit) x index).mp hformula
    exact ⟨x, hx, index, hleast.1,
      (isKuratowskiPairOf_lCarrier_iff pair x index).mpr hpairEq⟩
  · intro x hx
    let alpha := firstStage x.1 x.2
    have halphaLimit : alpha < limit :=
      firstStage_lt_of_mem_limitStage hl x hx
    have hcontains : StageContains x (ordinalLCarrier alpha) :=
      (stageContains_ordinal_iff x alpha).mpr
        (mem_LStageZF_firstStage x.1 x.2)
    have hminimal : forall earlier : LCarrier.{u},
        earlier.1 ∈ (ordinalLCarrier alpha).1 ->
          Not (StageContains x earlier) := by
      intro earlier hearlier
      rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
          hearlier with ⟨delta, hdelta, rfl⟩
      rw [stageContains_ordinal_iff]
      exact not_mem_LStageZF_of_lt_firstStage x.2 hdelta
    have hleast : IsLeastContainingStage
        (ordinalLCarrier limit) x (ordinalLCarrier alpha) :=
      ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          limit alpha).mpr halphaLimit,
        hcontains, hminimal⟩
    refine ⟨ordinalLCarrier alpha, hleast.1,
      (graphValue_leastContainingStageGraph_iff
        limit x (ordinalLCarrier alpha)).mpr ⟨hx, hleast⟩, ?_⟩
    intro other _hotherBound hotherGraph
    have hotherLeast :=
      (graphValue_leastContainingStageGraph_iff
        limit x other).mp hotherGraph |>.2
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
        hotherLeast.1 with ⟨gamma, _hgammaLimit, rfl⟩
    have hxGamma : x.1 ∈ LStageZF gamma :=
      (stageContains_ordinal_iff x gamma).mp hotherLeast.2.1
    have halphaGamma : alpha <= gamma :=
      firstStage_le x.2 hxGamma
    have hgammaAlpha : gamma <= alpha := by
      by_contra hnot
      have halphaLtGamma : alpha < gamma := lt_of_not_ge hnot
      have halphaMem :
          (ordinalLCarrier alpha).1 ∈ (ordinalLCarrier gamma).1 :=
        (ordinalLCarrier_mem_ordinalLCarrier_iff gamma alpha).mpr
          halphaLtGamma
      exact (hotherLeast.2.2 (ordinalLCarrier alpha) halphaMem)
        hcontains
    exact congrArg ordinalLCarrier
      (le_antisymm hgammaAlpha halphaGamma)

/-- The canonical graph has exactly the selector contract consumed by the
internal cardinal-union theorem. -/
theorem leastContainingStageGraph_selectsContainingFiber
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    SelectsContainingFiber LMem
      (leastContainingStageGraph limit)
      (stageLCarrier limit) (ordinalLCarrier limit)
      (stageValueGraph limit) := by
  constructor
  · exact leastContainingStageGraph_isFunctionGraph hl
  · intro x index hx hselect
    have hleast :=
      (graphValue_leastContainingStageGraph_iff
        limit x index).mp hselect |>.2
    rcases hleast.2.1 with ⟨stage, hstageValue, hxStage⟩
    exact ⟨stage,
      (graphValue_stageValueGraph_iff limit index stage).mpr
        ⟨hleast.1, hstageValue⟩,
      hxStage⟩

/-! ## Limit and Hartogs corollaries with the selector discharged -/

/-- Once the internal family of fiber injections is supplied, the canonical
selector completes the limit-union injection into `limit x kappa`. -/
theorem injects_limitStage_to_prod_of_internalInjectionFamily
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    {kappa injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      (ordinalLCarrier limit) graphFamily)
    (hinjections : forall ordinal : Ordinal.{u}, ordinal < limit ->
      forall injection : LCarrier.{u},
        GraphValue LMem injectionFamily
          (ordinalLCarrier ordinal) injection ->
        IsInjection LMem injection (stageLCarrier ordinal) kappa) :
    Injects LMem (stageLCarrier limit)
      (Constructible.Model.prodLCarrier
        (ordinalLCarrier limit) kappa) := by
  exact injects_limitStage_to_prod_of_internalFamilies hl
    (leastContainingStageGraph_selectsContainingFiber hl)
    hinjectionFamily hinjections

/-- At the Hartogs index, the selector no longer appears among the remaining
interfaces. -/
theorem injects_hartogsStage_of_internal_injectionFamily
    (kappa : LCarrier.{u})
    (hlimit : Order.IsSuccLimit (internalHartogsOrdinal kappa))
    {injectionFamily graphFamily : LCarrier.{u}}
    (hinjectionFamily : IsFunctionGraph LMem injectionFamily
      (internalHartogsLCarrier kappa) graphFamily)
    (hinjections : forall ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa ->
      forall injection : LCarrier.{u},
        GraphValue LMem injectionFamily
          (ordinalLCarrier ordinal) injection ->
        IsInjection LMem injection (stageLCarrier ordinal) kappa)
    (hproduct : Injects LMem
      (Constructible.Model.prodLCarrier
        (internalHartogsLCarrier kappa) kappa)
      (internalHartogsLCarrier kappa)) :
    Injects LMem
      (stageLCarrier (internalHartogsOrdinal kappa))
      (internalHartogsLCarrier kappa) := by
  exact (injects_limitStage_to_prod_of_internalInjectionFamily hlimit
    hinjectionFamily hinjections).trans_lCarrier hproduct

end

end Constructible.ContinuumFormula
