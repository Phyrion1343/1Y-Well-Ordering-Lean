/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistory
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationAssembly
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationFixedParameters

/-!
# Condensation from a locally correct relation-free stage predicate

The central hypothesis in this file is deliberately an exact semantic
contract, not a renamed reflection hypothesis.  `BareStageCorrectAt theta`
says that, for every ordinal code and candidate stage which belong to
`L_theta`, the relation-free first-order stage formula holds in `L_theta` if
and only if the candidate is the externally constructed `L_alpha`.

From that biconditional and full elementarity, this file derives the three
stage interfaces used by the usual Mostowski-collapse proof.  The remaining
task for arbitrary limit levels above `omega` is therefore stated without
ambiguity: prove `BareStageCorrectAt theta` from the ordinary limit
hypothesis.  No theorem in this file silently assumes that implication.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace BareStageCondensation

/-- Raw layout `(fixed13,index,stage)`, shared with
`Model.bareStageAtFormula`. -/
def bareStageAssignment (index stage : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) index)
    stage

/--
Exact local correctness of the relation-free stage predicate.

All quantifiers and membership assumptions are visible: both the ordinal
code and candidate output must be elements of `L_theta`, and satisfaction is
the raw semantics whose quantifiers range over exactly `L_theta`.
-/
def BareStageCorrectAt (theta : Ordinal.{u}) : Prop :=
  ∀ (alpha : Ordinal.{u}) (stage : ZFSet.{u}),
    alpha.toZFSet ∈ LStageZF theta → stage ∈ LStageZF theta →
      (Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
          Model.bareStageAtFormula
          (bareStageAssignment alpha.toZFSet stage) ↔
        stage = LStageZF alpha)

/-- An ordinal code in `L_theta` has index strictly below `theta`. -/
theorem ordinal_lt_of_toZFSet_mem_LStageZF
    {theta alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ LStageZF theta) : alpha < theta := by
  have hrank := (ordinal_stage_invariants theta).1
    (ZFSet.isOrdinal_toZFSet alpha) halpha
  have heq : (alpha.toZFSet : ZFSet.{u}).rank = alpha := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet alpha).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- Every correctly indexed actual stage is itself available in the ambient
level. -/
theorem actualStage_mem_of_index_mem
    {theta alpha : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ LStageZF theta) :
    LStageZF alpha ∈ LStageZF theta :=
  LStageZF_mem_of_lt (ordinal_lt_of_toZFSet_mem_LStageZF halpha)

/-- Layout `(fixed13,x)`. -/
def bareConstructibleParameters (x : ZFSet.{u}) : Tuple ZFSet.{u} 14 :=
  snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x

/-- Layout `(fixed13,x,index,stage)`. -/
def bareConstructibleWitnessAssignment
    (x index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (bareConstructibleParameters x) index) stage

/-- With the fixed evaluator prefix and `x` displayed, assert that `x`
belongs to a stage at an internally recognized ordinal index. -/
def bareConstructibleFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (Model.ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename Model.constructibleInternalStageRename
          Model.bareStageAtFormula)
        (.mem (13 : Fin 16) (15 : Fin 16)))))

private theorem bareConstructibleStageRename_assignment
    (x index stage : ZFSet.{u}) :
    (fun i => bareConstructibleWitnessAssignment x index stage
      (Model.constructibleInternalStageRename i)) =
      bareStageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
        Model.constructibleInternalStageRename i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc := by
        simp only [Model.constructibleInternalStageRename,
          Fin.lastCases_castSucc]
        apply Fin.ext
        rfl
      rw [hrename]
      simp [bareConstructibleWitnessAssignment,
        bareConstructibleParameters, bareStageAssignment]

/-- Full elementarity and exact local correctness put every internally
indexed constructible level into the elementary domain. -/
theorem stage_mem
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta)
    (alpha : Ordinal.{u}) (halpha : alpha.toZFSet ∈ domain) :
    LStageZF alpha ∈ domain := by
  let params : Tuple ZFSet.{u} 14 :=
    snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1)
      alpha.toZFSet
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact halpha
    · simpa [params] using hfixed j
  have halphaTheta : alpha.toZFSet ∈ LStageZF theta := hsubset halpha
  have hstageTheta : LStageZF alpha ∈ LStageZF theta :=
    actualStage_mem_of_index_mem halphaTheta
  have hstageSatTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula
        (bareStageAssignment alpha.toZFSet (LStageZF alpha)) :=
    (hcorrect alpha (LStageZF alpha) halphaTheta hstageTheta).mpr rfl
  have hexTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (.ex Model.bareStageAtFormula) params := by
    refine ⟨LStageZF alpha, hstageTheta, ?_⟩
    simpa [params, bareStageAssignment] using hstageSatTheta
  have hexDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        (.ex Model.bareStageAtFormula) params :=
    (helem (.ex Model.bareStageAtFormula) params hparamsDomain).mpr hexTheta
  rcases hexDomain with ⟨stage, hstageDomain, hstageSatDomain⟩
  change stage ∈ domain at hstageDomain
  have hfullDomain : ∀ i, snoc params stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hstageDomain
    · simpa using hparamsDomain j
  have hstageSatTheta' :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (snoc params stage) :=
    (helem Model.bareStageAtFormula (snoc params stage)
      hfullDomain).mp hstageSatDomain
  have hstageEq : stage = LStageZF alpha :=
    (hcorrect alpha stage halphaTheta (hsubset hstageDomain)).mp
      (by simpa [params, bareStageAssignment] using hstageSatTheta')
  simpa only [← hstageEq] using hstageDomain

/-- Exact local correctness reflects a stage containing each domain member,
with the ordinal index itself in the domain. -/
theorem internallyStageCovered
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta) :
    InternallyStageCovered domain := by
  intro x hxDomain
  have hxTheta : x ∈ LStageZF theta := hsubset hxDomain
  rcases (mem_LStageZF_limit_iff htheta).mp hxTheta with
    ⟨alpha, halphaTheta, hxAlpha⟩
  have hindexTheta : alpha.toZFSet ∈ LStageZF theta :=
    ordinal_toZFSet_mem_LStageZF_of_lt halphaTheta
  have hstageTheta : LStageZF alpha ∈ LStageZF theta :=
    LStageZF_mem_of_lt halphaTheta
  let params := bareConstructibleParameters x
  let full := bareConstructibleWitnessAssignment
    x alpha.toZFSet (LStageZF alpha)
  have hfullTheta : ∀ i, full i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · exact hstageTheta
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · exact hindexTheta
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · exact hxTheta
        · simpa [full, bareConstructibleWitnessAssignment,
            bareConstructibleParameters] using hsubset (hfixed i13)
  have hordinalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (14 : Fin 16)) full :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (14 : Fin 16) full hfullTheta).mpr
      (ZFSet.isOrdinal_toZFSet alpha)
  have hstageThetaSat :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (FOFormula.rename Model.constructibleInternalStageRename
          Model.bareStageAtFormula) full := by
    rw [Model.satisfiesIn_rename,
      bareConstructibleStageRename_assignment]
    exact (hcorrect alpha (LStageZF alpha)
      hindexTheta hstageTheta).mpr rfl
  have hformulaTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        bareConstructibleFormula params := by
    exact ⟨alpha.toZFSet, hindexTheta, LStageZF alpha, hstageTheta,
      hordinalTheta, hstageThetaSat, hxAlpha⟩
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hxDomain
    · simpa [params, bareConstructibleParameters] using hfixed j
  have hformulaDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        bareConstructibleFormula params :=
    (helem bareConstructibleFormula params hparamsDomain).mpr hformulaTheta
  rcases hformulaDomain with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexFormula, hstageFormula, hxStage⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change x ∈ stage at hxStage
  let full' := bareConstructibleWitnessAssignment x index stage
  have hfull'Domain : ∀ i, full' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · exact hindexDomain
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · exact hxDomain
        · simpa [full', bareConstructibleWitnessAssignment,
            bareConstructibleParameters] using hfixed i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (14 : Fin 16)) full' :=
    (helem (Model.ordinalAt (14 : Fin 16)) full' hfull'Domain).mp
      (by simpa [full', params,
          bareConstructibleWitnessAssignment] using hindexFormula)
  have hindexOrdinal : index.IsOrdinal :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (14 : Fin 16) full'
      (fun i => hsubset (hfull'Domain i))).mp hindexThetaFormula
  let alpha' : Ordinal.{u} := index.rank
  have hindexEq : index = alpha'.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.bareStageAtFormula Model.constructibleInternalStageRename
        full').mp (by simpa [full', params,
          bareConstructibleWitnessAssignment] using hstageFormula)
    rw [bareConstructibleStageRename_assignment] at hrenamed
    exact hrenamed
  have hstageParamsDomain : ∀ i,
      bareStageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hindexDomain
      · simpa [bareStageAssignment] using hfixed i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) :=
    (helem Model.bareStageAtFormula (bareStageAssignment index stage)
      hstageParamsDomain).mp hstageDirectDomain
  have hstageEq : stage = LStageZF alpha' :=
    (hcorrect alpha' stage
      (hsubset (by simpa only [← hindexEq] using hindexDomain))
      (hsubset hstageDomain)).mp
      (by simpa only [← hindexEq] using hstageThetaFormula)
  refine ⟨alpha', ?_, ?_⟩
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq] using hxStage

/-! ## Bounded earlier-stage witnesses -/

/-- Layout `(fixed13,x,bound,index,stage)` projected to
`(fixed13,index,stage)`. -/
def bareBoundedStageRename : Fin 15 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13,x,bound)`. -/
def bareBoundedStageParameters
    (x bound : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x)
    bound

/-- Layout `(fixed13,x,bound,index,stage)`. -/
def bareBoundedStageWitnessAssignment
    (x bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (bareBoundedStageParameters x bound) index) stage

private theorem bareBoundedStageRename_assignment
    (x bound index stage : ZFSet.{u}) :
    (fun i => bareBoundedStageWitnessAssignment x bound index stage
      (bareBoundedStageRename i)) =
      bareStageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
        bareBoundedStageRename i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc.castSucc := by
        simp only [bareBoundedStageRename, Fin.lastCases_castSucc]
        apply Fin.ext
        rfl
      rw [hrename]
      simp [bareBoundedStageWitnessAssignment,
        bareBoundedStageParameters, bareStageAssignment]

/-- There is an internally indexed smaller stage containing `x`.
The free layout is `(fixed13,x,bound)`. -/
def bareBoundedStageContainsFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (.mem (15 : Fin 17) (14 : Fin 17))
      (.conj
        (Model.ordinalAt (15 : Fin 17))
        (.conj
          (FOFormula.rename bareBoundedStageRename
            Model.bareStageAtFormula)
          (.mem (13 : Fin 17) (16 : Fin 17))))))

/-- Exact stage correctness supplies the bounded witness needed at a limit
index in the elementary domain. -/
theorem smallerStageWitnesses
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixed : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta)
    (limit : Ordinal.{u}) (hlimit : Order.IsSuccLimit limit)
    (hlimitDomain : limit.toZFSet ∈ domain) :
    HasSmallerInternalLStageWitnesses domain limit := by
  intro x hxDomain hxLimit
  rcases (mem_LStageZF_limit_iff hlimit).mp hxLimit with
    ⟨delta, hdeltaLimit, hxDelta⟩
  have hlimitTheta : limit.toZFSet ∈ LStageZF theta :=
    hsubset hlimitDomain
  have hlimitLtTheta : limit < theta :=
    ordinal_lt_of_toZFSet_mem_LStageZF hlimitTheta
  have hdeltaTheta : delta.toZFSet ∈ LStageZF theta :=
    ordinal_toZFSet_mem_LStageZF_of_lt
      (hdeltaLimit.trans hlimitLtTheta)
  have hstageTheta : LStageZF delta ∈ LStageZF theta :=
    LStageZF_mem_of_lt (hdeltaLimit.trans hlimitLtTheta)
  let params := bareBoundedStageParameters x limit.toZFSet
  let full := bareBoundedStageWitnessAssignment
    x limit.toZFSet delta.toZFSet (LStageZF delta)
  have hfullTheta : ∀ i, full i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · exact hstageTheta
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · exact hdeltaTheta
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · exact hlimitTheta
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · exact hsubset hxDomain
          · simpa [full, bareBoundedStageWitnessAssignment,
              bareBoundedStageParameters] using hsubset (hfixed i13)
  have hordinalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (15 : Fin 17) full hfullTheta).mpr
      (ZFSet.isOrdinal_toZFSet delta)
  have hstageThetaSat :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (FOFormula.rename bareBoundedStageRename
          Model.bareStageAtFormula) full := by
    rw [Model.satisfiesIn_rename, bareBoundedStageRename_assignment]
    exact (hcorrect delta (LStageZF delta)
      hdeltaTheta hstageTheta).mpr rfl
  have hformulaTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        bareBoundedStageContainsFormula params := by
    exact ⟨delta.toZFSet, hdeltaTheta, LStageZF delta, hstageTheta,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr hdeltaLimit,
      hordinalTheta, hstageThetaSat, hxDelta⟩
  have hparamsDomain : ∀ i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hlimitDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hxDomain
      · simpa [params, bareBoundedStageParameters] using hfixed i13
  have hformulaDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        bareBoundedStageContainsFormula params :=
    (helem bareBoundedStageContainsFormula params hparamsDomain).mpr
      hformulaTheta
  rcases hformulaDomain with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexBound, hindexFormula, hstageFormula, hxStage⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change index ∈ limit.toZFSet at hindexBound
  change x ∈ stage at hxStage
  let full' := bareBoundedStageWitnessAssignment
    x limit.toZFSet index stage
  have hfull'Domain : ∀ i, full' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · exact hindexDomain
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · exact hlimitDomain
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · exact hxDomain
          · simpa [full', bareBoundedStageWitnessAssignment,
              bareBoundedStageParameters] using hfixed i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full' :=
    (helem (Model.ordinalAt (15 : Fin 17)) full' hfull'Domain).mp
      (by simpa [full', params,
          bareBoundedStageWitnessAssignment] using hindexFormula)
  have hindexOrdinal : index.IsOrdinal :=
    (CondensationHull.satisfiesIn_ordinalAt_iff
      (LStageZF_isTransitive theta) (15 : Fin 17) full'
      (fun i => hsubset (hfull'Domain i))).mp hindexThetaFormula
  let delta' : Ordinal.{u} := index.rank
  have hindexEq : index = delta'.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.bareStageAtFormula bareBoundedStageRename full').mp
        (by simpa [full', params,
            bareBoundedStageWitnessAssignment] using hstageFormula)
    rw [bareBoundedStageRename_assignment] at hrenamed
    exact hrenamed
  have hstageParamsDomain : ∀ i,
      bareStageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact hindexDomain
      · simpa [bareStageAssignment] using hfixed i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.bareStageAtFormula (bareStageAssignment index stage) :=
    (helem Model.bareStageAtFormula (bareStageAssignment index stage)
      hstageParamsDomain).mp hstageDirectDomain
  have hstageEq : stage = LStageZF delta' :=
    (hcorrect delta' stage
      (hsubset (by simpa only [← hindexEq] using hindexDomain))
      (hsubset hstageDomain)).mp
      (by simpa only [← hindexEq] using hstageThetaFormula)
  refine ⟨delta', ?_, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mp
      (by simpa only [← hindexEq] using hindexBound)
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq] using hxStage

/-- Above `omega`, exact local correctness of the bare stage predicate turns
ordinary full elementarity into every explicit interface required by the
collapse assembly. -/
theorem stageInterfaces_of_fixedParameters
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hfixedDomain : ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain)
    (hcorrect : BareStageCorrectAt theta) :
    StageCondensationInterfaces theta domain := by
  exact
    { isLimit := htheta
      subset_stage := hsubset
      satisfactionAbsolute := helem
      empty_mem := by
        have hempty := hfixedDomain (2 : Fin 13)
        rw [Model.stageHistoryFixedParameters_empty] at hempty
        exact hempty
      stage_mem := stage_mem hsubset helem hfixedDomain hcorrect
      internallyStageCovered :=
        internallyStageCovered htheta hsubset helem hfixedDomain hcorrect
      smallerStageWitnesses := by
        intro limit hlimit hlimitDomain
        exact smallerStageWitnesses hsubset helem hfixedDomain hcorrect
          limit hlimit hlimitDomain }

/-- Above `omega`, the canonical fixed parameters follow from ordinary full
elementarity.  Consequently exact local correctness of the bare stage
formula is the only remaining premise needed by the transparent assembly. -/
theorem stageInterfaces_of_bareStageCorrect
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hcorrect : BareStageCorrectAt theta) :
    StageCondensationInterfaces theta domain :=
  stageInterfaces_of_fixedParameters htheta hsubset helem
    (Model.stageHistoryFixedParameters_mem_of_elementary_limit
      htheta homega hsubset helem)
    hcorrect

/-- Conditional arbitrary-limit Condensation above `omega`, with the exact
remaining local stage-correctness obligation kept in the theorem type. -/
theorem exists_range_eq_LStageZF_of_bareStageCorrect
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hcorrect : BareStageCorrectAt theta) :
    ∃ beta : Ordinal.{u},
      MostowskiCollapse.range domain = LStageZF beta :=
  (stageInterfaces_of_bareStageCorrect
    htheta homega hsubset helem hcorrect).exists_range_eq_LStageZF

end BareStageCondensation

end

end MostowskiCollapse

end Constructible
