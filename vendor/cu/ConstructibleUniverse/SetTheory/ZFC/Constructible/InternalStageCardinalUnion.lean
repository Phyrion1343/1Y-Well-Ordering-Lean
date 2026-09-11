/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalUnion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem

/-!
# The internally represented family of constructible stages

This file supplies the stage-family part of the standard cardinal estimate at
a limit level.  Replacement constructs the actual set of earlier stages, and
Separation constructs the actual graph sending an ordinal index to its stage.
Consequently the generic indexed-union theorem can be applied without taking
an externally indexed family as an internal graph.

The remaining inputs to the limit-cardinal argument are stated explicitly:
an internal selector choosing a containing stage, an internal family of
injection graphs for the fibers, and (when the final target is an ordinal
cardinal) the appropriate internal product absorption.  No ambient cardinal
comparison is converted into any of these graph witnesses.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage-valued functional relation -/

/-- `stage` is the stage coordinate of the canonical state at `index`. -/
def StageValueAt (index stage : LCarrier.{u}) : Prop :=
  exists relation : LCarrier.{u},
    Constructible.Model.StageStateAt index stage relation

/-- Layout `(fixed13, index, stage)`.  The hidden variable is the relation
coordinate of the stage state. -/
def stageValueAtFormula : FOFormula 15 :=
  .ex Constructible.Model.stageStateAtFormula

/-- The direct assignment for `stageValueAtFormula`. -/
def stageValueAtAssignment (index stage : LCarrier.{u}) :
    Tuple LCarrier.{u} 15 :=
  snoc (snoc Constructible.Model.stageHistoryFixedParameters index) stage

@[simp]
theorem satisfies_stageValueAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageValueAtFormula
        (stageValueAtAssignment index stage) ↔
      StageValueAt index stage := by
  simp only [stageValueAtFormula, FOFormula.Satisfies, StageValueAt]
  apply exists_congr
  intro relation
  change FOFormula.Satisfies LMem
      Constructible.Model.stageStateAtFormula
        (Constructible.Model.stageStateAtLAssignment
          index stage relation) ↔ _
  exact Constructible.Model.satisfies_stageStateAtFormula
    index stage relation

/-- At a canonical ordinal index, the stage coordinate is exactly the
externally defined level packaged as an `LCarrier`. -/
theorem stageValueAt_ordinal_iff
    (ordinal : Ordinal.{u}) (stage : LCarrier.{u}) :
    StageValueAt (ordinalLCarrier ordinal) stage ↔
      stage = stageLCarrier ordinal := by
  constructor
  · rintro ⟨relation, hstate⟩
    exact (Constructible.Model.stageStateAt_ordinal_outputs_unique
      ordinal hstate
        (Constructible.Model.stageHistoryData ordinal).state).1
  · rintro rfl
    exact ⟨(Constructible.Model.stageHistoryData ordinal).relation,
      (Constructible.Model.stageHistoryData ordinal).state⟩

/-! ## Replacement of the earlier stages -/

/-- Replacement produces the set of all stages strictly below `bound`. -/
theorem exists_stageValueFamily (bound : Ordinal.{u}) :
    exists family : LCarrier.{u},
      forall stage : LCarrier.{u},
        stage.1 ∈ family.1 ↔
          exists ordinal : Ordinal.{u},
            ordinal < bound /\ stage = stageLCarrier ordinal := by
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 ->
        ExistsUnique fun stage : LCarrier.{u} =>
          FOFormula.Satisfies LMem stageValueAtFormula
            (snoc (snoc Constructible.Model.stageHistoryFixedParameters
              index) stage) := by
    intro index hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨stageLCarrier ordinal, ?_, ?_⟩
    · apply (satisfies_stageValueAtFormula
        (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
      exact (stageValueAt_ordinal_iff ordinal
        (stageLCarrier ordinal)).mpr rfl
    · intro other hother
      exact (stageValueAt_ordinal_iff ordinal other).mp
        ((satisfies_stageValueAtFormula
          (ordinalLCarrier ordinal) other).mp hother)
  rcases Constructible.Model.exists_replacementLCarrier
      stageValueAtFormula
      Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier bound) hfun with ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro stage
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hstage⟩
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinal, hordinal, ?_⟩
    exact (stageValueAt_ordinal_iff ordinal stage).mp
      ((satisfies_stageValueAtFormula
        (ordinalLCarrier ordinal) stage).mp hstage)
  · rintro ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff bound ordinal).mpr hordinal,
      ?_⟩
    apply (satisfies_stageValueAtFormula
      (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
    exact (stageValueAt_ordinal_iff ordinal
      (stageLCarrier ordinal)).mpr rfl

/-- The canonical choice of the Replacement-generated earlier-stage family.
Only its extensional specification is used below. -/
noncomputable def stageValueFamily (bound : Ordinal.{u}) : LCarrier.{u} :=
  Classical.choose (exists_stageValueFamily bound)

@[simp]
theorem mem_stageValueFamily_iff
    (bound : Ordinal.{u}) (stage : LCarrier.{u}) :
    stage.1 ∈ (stageValueFamily bound).1 ↔
      exists ordinal : Ordinal.{u},
        ordinal < bound /\ stage = stageLCarrier ordinal :=
  Classical.choose_spec (exists_stageValueFamily bound) stage

/-- At a nonzero limit, the union of the internally represented earlier-stage
family is exactly the limit stage itself. -/
theorem sUnion_stageValueFamily_eq_stageLCarrier
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    Constructible.Model.sUnionLCarrier (stageValueFamily limit) =
      stageLCarrier limit := by
  apply Constructible.Model.lCarrier_extensionality
  intro z
  rw [Constructible.Model.mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstageFamily, hzStage⟩
    rcases (mem_stageValueFamily_iff limit stage).mp hstageFamily with
      ⟨ordinal, hordinal, rfl⟩
    change z.1 ∈ LStageZF limit
    exact (mem_LStageZF_limit_iff hl).mpr
      ⟨ordinal, hordinal, hzStage⟩
  · intro hzLimit
    change z.1 ∈ LStageZF limit at hzLimit
    rcases (mem_LStageZF_limit_iff hl).mp hzLimit with
      ⟨ordinal, hordinal, hzStage⟩
    refine ⟨stageLCarrier ordinal, ?_, hzStage⟩
    exact (mem_stageValueFamily_iff limit
      (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩

/-! ## The internally represented index-to-stage graph -/

/-- Rename `(fixed13,index,stage)` into
`(fixed13,bound,index,stage)`. -/
def boundedStageValueAtRename : Fin 15 -> Fin 16 :=
  Fin.lastCases
    (15 : Fin 16)
    (fun i14 => Fin.lastCases
      (14 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13,bound,index,stage)`. -/
def boundedStageValueAtFormula : FOFormula 16 :=
  .conj
    (.mem (14 : Fin 16) (13 : Fin 16))
    (FOFormula.rename boundedStageValueAtRename stageValueAtFormula)

/-- Direct assignment for the bounded stage-valued relation. -/
def boundedStageValueAtAssignment
    (bound index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc
    (snoc Constructible.Model.stageHistoryFixedParameters bound)
    index) stage

theorem comp_boundedStageValueAtRename
    (bound index stage : LCarrier.{u}) :
    (fun i => boundedStageValueAtAssignment bound index stage
      (boundedStageValueAtRename i)) =
      stageValueAtAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun _i13 => ?_) i14
    · rfl
    · simp only [boundedStageValueAtRename, Fin.lastCases_castSucc]
      rw [show Fin.castLE (by decide) _i13 =
          _i13.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [boundedStageValueAtAssignment, stageValueAtAssignment,
        snoc_castSucc]

@[simp]
theorem satisfies_boundedStageValueAtFormula
    (bound index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem boundedStageValueAtFormula
        (boundedStageValueAtAssignment bound index stage) ↔
      index.1 ∈ bound.1 /\ StageValueAt index stage := by
  simp only [boundedStageValueAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [comp_boundedStageValueAtRename,
    satisfies_stageValueAtFormula]
  rfl

/-- A support containing both the ordinal index set and the family of stage
values. -/
def stageValueGraphSupport (bound : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.unionLCarrier
    (ordinalLCarrier bound) (stageValueFamily bound)

/-- The actual constructible graph sending each `beta < bound` to `L_beta`. -/
noncomputable def stageValueGraph (bound : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.canonicalDefinableRelationGraph
    boundedStageValueAtFormula
    (snoc Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier bound))
    (stageValueGraphSupport bound)

@[simp]
theorem graphValue_stageValueGraph_iff
    (bound : Ordinal.{u}) (index stage : LCarrier.{u}) :
    GraphValue LMem (stageValueGraph bound) index stage ↔
      index.1 ∈ (ordinalLCarrier bound).1 /\
        StageValueAt index stage := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [stageValueGraph,
    Constructible.Model.graphRel_canonicalDefinableRelationGraph_iff]
  change
    (index.1 ∈ (stageValueGraphSupport bound).1 /\
      stage.1 ∈ (stageValueGraphSupport bound).1 /\
        FOFormula.Satisfies LMem boundedStageValueAtFormula
          (boundedStageValueAtAssignment
            (ordinalLCarrier bound) index stage)) ↔ _
  rw [satisfies_boundedStageValueAtFormula]
  constructor
  · rintro ⟨_hindexSupport, _hstageSupport, hindex, hstage⟩
    exact ⟨hindex, hstage⟩
  · rintro ⟨hindex, hstage⟩
    have hindexSupport :
        index.1 ∈ (stageValueGraphSupport bound).1 := by
      apply (Constructible.Model.mem_unionLCarrier_iff
        (ordinalLCarrier bound) (stageValueFamily bound) index).mpr
      exact Or.inl hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hstage
    have hstageFamily : stage.1 ∈ (stageValueFamily bound).1 := by
      rw [hstageEq]
      exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    have hstageSupport :
        stage.1 ∈ (stageValueGraphSupport bound).1 := by
      apply (Constructible.Model.mem_unionLCarrier_iff
        (ordinalLCarrier bound) (stageValueFamily bound) stage).mpr
      exact Or.inr hstageFamily
    exact ⟨hindexSupport, hstageSupport, hindex, hstage⟩

/-- The stage graph is a total internally represented function from the
ordinal index to the Replacement-generated family of earlier stages. -/
theorem stageValueGraph_isFunctionGraph (bound : Ordinal.{u}) :
    IsFunctionGraph LMem (stageValueGraph bound)
      (ordinalLCarrier bound) (stageValueFamily bound) := by
  constructor
  · intro pair hpair
    have hmem :=
      (Constructible.Model.mem_canonicalDefinableRelationGraph_iff
        boundedStageValueAtFormula
        (snoc Constructible.Model.stageHistoryFixedParameters
          (ordinalLCarrier bound))
        (stageValueGraphSupport bound) pair).mp hpair
    rcases hmem with
      ⟨index, stage, _hindexSupport, _hstageSupport,
        hpairEq, hformula⟩
    have hbounded :=
      (satisfies_boundedStageValueAtFormula
        (ordinalLCarrier bound) index stage).mp hformula
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem
        hbounded.1 with ⟨ordinal, hordinal, rfl⟩
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hbounded.2
    have hstageFamily : stage.1 ∈ (stageValueFamily bound).1 := by
      rw [hstageEq]
      exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff bound ordinal).mpr hordinal,
      stage, hstageFamily, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff
      pair (ordinalLCarrier ordinal) stage).mpr hpairEq
  · intro index hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨stageLCarrier ordinal, ?_, ?_, ?_⟩
    · exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    · apply (graphValue_stageValueGraph_iff bound
        (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
      exact ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          bound ordinal).mpr hordinal,
        (stageValueAt_ordinal_iff ordinal
          (stageLCarrier ordinal)).mpr rfl⟩
    · intro other _hotherFamily hother
      exact (stageValueAt_ordinal_iff ordinal other).mp
        ((graphValue_stageValueGraph_iff bound
          (ordinalLCarrier ordinal) other).mp hother).2

/-! ## The standard limit-cardinal step -/

/-- The exact internal limit step.  The indexed family of stages and its
functionality are now canonical.  The hypotheses retain only the genuinely
separate graph obligations: selecting a containing fiber and internally
collecting the fiber injections. -/
theorem injects_limitStage_to_prod_of_internalFamilies
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    {kappa selector injectionFamily graphFamily : LCarrier.{u}}
    (hselector : SelectsContainingFiber LMem selector
      (stageLCarrier limit) (ordinalLCarrier limit)
      (stageValueGraph limit))
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
  have hfibers : IsFiberInjectionFamily LMem
      (stageValueGraph limit) injectionFamily
      (ordinalLCarrier limit) (stageValueFamily limit)
      graphFamily kappa := by
    refine ⟨stageValueGraph_isFunctionGraph limit,
      hinjectionFamily, ?_⟩
    intro index fiber injection hindex hfiber hinjection
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hfiberEq : fiber = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal fiber).mp
        ((graphValue_stageValueGraph_iff limit
          (ordinalLCarrier ordinal) fiber).mp hfiber).2
    subst fiber
    exact hinjections ordinal hordinal injection hinjection
  have hselectorUnion : SelectsContainingFiber LMem selector
      (Constructible.Model.sUnionLCarrier (stageValueFamily limit))
      (ordinalLCarrier limit) (stageValueGraph limit) := by
    simpa only [sUnion_stageValueFamily_eq_stageLCarrier hl] using hselector
  have hinjects := injects_sUnion_to_prod_lCarrier
    hselectorUnion hfibers
  simpa only [sUnion_stageValueFamily_eq_stageLCarrier hl] using hinjects

/-- The remaining limit-stage route to `HartogsStageBound`.  Besides the
canonical stage family proved above, it requires exactly an internal selector,
an internally collected family of the Hartogs-provided fiber injections, and
an internally represented product absorption. -/
theorem injects_hartogsStage_of_internal_limit_data
    (kappa : LCarrier.{u})
    (hlimit : Order.IsSuccLimit (internalHartogsOrdinal kappa))
    {selector injectionFamily graphFamily : LCarrier.{u}}
    (hselector : SelectsContainingFiber LMem selector
      (stageLCarrier (internalHartogsOrdinal kappa))
      (internalHartogsLCarrier kappa)
      (stageValueGraph (internalHartogsOrdinal kappa)))
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
  exact (injects_limitStage_to_prod_of_internalFamilies hlimit
    hselector hinjectionFamily hinjections).trans_lCarrier hproduct

end

end Constructible.ContinuumFormula
