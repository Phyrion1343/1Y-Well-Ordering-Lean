/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationReflection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefZFCollapse
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiCollapseOrdinals

/-!
# Condensation for constructible levels

This file assembles the order-theoretic condensation core with full
elementarity and the Mostowski collapse.  The only set-recursion input is the
explicit predicate `CollapseDefZFCommutes`: it records that collapse commutes
with one successor step of the constructible hierarchy.  The corresponding
theorem is proved separately from the definability of `DefZF` and is not
silently assumed here.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The exact successor-step interface needed by the condensation proof. -/
def CollapseDefZFCommutes (domain : ZFSet.{u}) : Prop :=
  forall {a : ZFSet.{u}}, a ∈ domain -> DefZF a ∈ domain ->
    collapse domain (DefZF a) = DefZF (collapse domain a)

/-- Internal proof package for a set-sized elementary hull of a condensation
reflection level. The `fixed_mem` field is derived from full elementarity by
`CondensationHull.of_elementary`; callers need not assume it separately. -/
structure CondensationHull (theta : Ordinal.{u}) (domain : ZFSet.{u}) : Prop where
  reflection : Model.IsCondensationReflectionLevel theta
  subset_stage : domain ⊆ LStageZF theta
  satisfactionAbsolute :
    SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})
  fixed_mem : forall i : Fin 13,
    (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain

namespace CondensationHull

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}

/--
The thirteen evaluator parameters are not an extra hull hypothesis. At a
condensation reflection level their canonical specification has a witness;
full elementarity pulls a witness into the hull, and uniqueness identifies
that witness with `stageHistoryFixedParameters`.
-/
theorem fixedParameters_mem_of_elementary
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem :
      SatisfactionAbsolute (domain : Set ZFSet.{u})
        (LStageZF theta : Set ZFSet.{u})) :
    ∀ i : Fin 13,
      (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain := by
  let fixed : Tuple ZFSet.{u} 13 :=
    fun i => (Model.stageHistoryFixedParameters.{u} i).1
  let closedBounded :
      FirstOrder.Language.setTheory.BoundedFormula Empty 0 :=
    (Model.toBoundedFormula
      Model.canonicalStageParametersFormula).exs
  let closed : FOFormula 0 :=
    Model.fromBoundedFormula closedBounded
  let emptyRaw : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  let fixedTheta : Tuple (Model.StageCarrier theta) 13 :=
    fun i => ⟨fixed i, hreflection.2.1 i⟩
  letI stageStructure :
      FirstOrder.Language.setTheory.Structure (Model.StageCarrier theta) :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
  have hcanonicalTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.canonicalStageParametersFormula fixed :=
    (Model.satisfiesIn_vEqualsLCore_of_condensationReflectionLevel
      hreflection).1
  have hcanonicalThetaTyped :
      FOFormula.Satisfies
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        Model.canonicalStageParametersFormula fixedTheta := by
    apply (Model.satisfies_stageCarrier_iff_satisfiesIn
      Model.canonicalStageParametersFormula fixedTheta).mpr
    simpa only [fixedTheta, fixed] using hcanonicalTheta
  have hboundedTheta :
      Model.realizes
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        (Model.toBoundedFormula
          Model.canonicalStageParametersFormula) fixedTheta :=
    (Model.realizes_toBoundedFormula
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
      Model.canonicalStageParametersFormula fixedTheta).mpr
      hcanonicalThetaTyped
  let emptyTheta : Tuple (Model.StageCarrier theta) 0 :=
    fun i => Fin.elim0 i
  have hexBoundedTheta :
      Model.realizes
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        closedBounded emptyTheta := by
    change
      ((Model.toBoundedFormula
        Model.canonicalStageParametersFormula).exs).Realize
          Empty.elim
    rw [FirstOrder.Language.BoundedFormula.realize_exs]
    exact ⟨fixedTheta, hboundedTheta⟩
  have hclosedThetaTyped :
      FOFormula.Satisfies
        (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
        closed emptyTheta := by
    exact (Model.realize_fromBoundedFormula
      (fun x y : Model.StageCarrier theta => x.1 ∈ y.1)
      closedBounded emptyTheta).mp hexBoundedTheta
  have hclosedTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        closed emptyRaw := by
    have hbridge := Model.satisfies_stageCarrier_iff_satisfiesIn
      closed emptyTheta
    apply hbridge.mp
    exact hclosedThetaTyped
  have hclosedDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        closed emptyRaw :=
    (helem closed emptyRaw (fun i => Fin.elim0 i)).mpr
      hclosedTheta
  let DomainCarrier :=
    Model.ClassCarrier (domain : Set ZFSet.{u})
  letI domainStructure :
      FirstOrder.Language.setTheory.Structure DomainCarrier :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : DomainCarrier => x.1 ∈ y.1)
  let emptyDomain : Tuple DomainCarrier 0 :=
    fun i => Fin.elim0 i
  have hclosedDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        closed emptyDomain := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) closed emptyDomain).mpr
    rw [show (fun i => (emptyDomain i).1) = emptyRaw by
      exact Subsingleton.elim _ _]
    exact hclosedDomain
  have hexBoundedDomain :
      Model.realizes
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        closedBounded emptyDomain := by
    exact (Model.realize_fromBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      closedBounded emptyDomain).mpr hclosedDomainTyped
  change
    ((Model.toBoundedFormula
      Model.canonicalStageParametersFormula).exs).Realize
        Empty.elim at hexBoundedDomain
  rw [FirstOrder.Language.BoundedFormula.realize_exs] at hexBoundedDomain
  rcases hexBoundedDomain with ⟨sDomain, hsDomainBounded⟩
  have hsDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        Model.canonicalStageParametersFormula sDomain := by
    apply (Model.realizes_toBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      Model.canonicalStageParametersFormula sDomain).mp
    exact hsDomainBounded
  let sRaw : Tuple ZFSet.{u} 13 := fun i => (sDomain i).1
  have hsDomainRaw :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u})
      Model.canonicalStageParametersFormula sDomain).mp
    exact hsDomainTyped
  have hsThetaRaw :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw :=
    (helem Model.canonicalStageParametersFormula sRaw
      (fun i => (sDomain i).2)).mp hsDomainRaw
  have hcloseCanonical :
      ClosesFrom Model.canonicalStageParametersFormula theta theta := by
    have hcloseCore := hreflection.2.2.1
    change
      ClosesFrom Model.canonicalStageParametersFormula theta theta ∧
        ClosesFrom
          (FOFormula.all Model.constructibleWithParametersFormula)
          theta theta at hcloseCore
    exact hcloseCore.1
  have hsLRaw :
      Model.SatisfiesIn (L : Set ZFSet.{u})
        Model.canonicalStageParametersFormula sRaw :=
    (satisfiesIn_stage_iff_L_of_closes
      Model.canonicalStageParametersFormula theta hcloseCanonical
      sRaw (fun i => hsubset (sDomain i).2)).mp hsThetaRaw
  let sL : Tuple Model.LCarrier.{u} 13 :=
    fun i =>
      ⟨sRaw i,
        mem_L_of_mem (hsubset (sDomain i).2)
          (LStageZF_mem_L theta)⟩
  have hsLTyped :
      FOFormula.Satisfies Model.lCarrierMem
        Model.canonicalStageParametersFormula sL := by
    apply (Model.satisfies_lCarrier_iff_satisfiesIn_L
      Model.canonicalStageParametersFormula sL).mpr
    simpa only [sL, sRaw] using hsLRaw
  have hsLEq :
      sL = Model.stageHistoryFixedParameters :=
    (Model.satisfies_canonicalStageParametersFormula sL).mp hsLTyped
  intro i
  have hvalue :
      (sDomain i).1 =
        (Model.stageHistoryFixedParameters.{u} i).1 := by
    exact congrArg (fun s : Tuple Model.LCarrier.{u} 13 => (s i).1) hsLEq
  rw [← hvalue]
  exact (sDomain i).2

/-- Package a genuinely elementary substructure at a condensation reflection
level. The fixed evaluator parameters are derived, not assumed. -/
theorem of_elementary
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem :
      SatisfactionAbsolute (domain : Set ZFSet.{u})
        (LStageZF theta : Set ZFSet.{u})) :
    CondensationHull theta domain where
  reflection := hreflection
  subset_stage := hsubset
  satisfactionAbsolute := helem
  fixed_mem := fixedParameters_mem_of_elementary hreflection hsubset helem

/-- The bounded ordinal formula has its ambient meaning in every transitive
set. -/
theorem satisfiesIn_isOrdinal_iff {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFSet.{u}) (hx : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        OrdinalFormula.isOrdinal ![x] ↔ x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hx⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU xU
  have hraw : (fun i => (![xU] i).1) = ![x] := by
    funext i
    fin_cases i
    rfl
  rw [hraw] at hbridge
  exact hbridge.symm.trans hsemantic

/-- Coordinate form of `satisfiesIn_isOrdinal_iff`. -/
theorem satisfiesIn_ordinalAt_iff {U : ZFSet.{u}} (hU : U.IsTransitive)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u}) (Model.ordinalAt i) s ↔
      (s i).IsOrdinal := by
  rw [Model.ordinalAt,
    Model.satisfiesIn_rename (U : Set ZFSet.{u})]
  have hone : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    fin_cases j
    rfl
  rw [hone, satisfiesIn_isOrdinal_iff hU (s i) (hs i)]

/-- Full elementarity in a transitive level gives the extensionality required
by the Mostowski collapse. -/
theorem isExtensional (h : CondensationHull theta domain) :
    IsExtensional domain := by
  intro x hx y hy hsame
  apply restricted_extensionality_of_closesWithinAll
    h.subset_stage (LStageZF_isTransitive theta)
    (closesWithinAll_of_satisfactionAbsolute h.satisfactionAbsolute)
    hx hy
  intro z hz
  exact hsame z hz

/-- Raw tuple consisting of the thirteen fixed parameters followed by an
index and a proposed stage. -/
def stageAssignment (index stage : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) index)
    stage

@[simp]
theorem stageAssignment_fixed (index stage : ZFSet.{u}) (i : Fin 13) :
    stageAssignment index stage i.castSucc.castSucc =
      (Model.stageHistoryFixedParameters.{u} i).1 := by
  simp [stageAssignment]

@[simp]
theorem stageAssignment_index (index stage : ZFSet.{u}) :
    stageAssignment index stage (13 : Fin 15) = index := by
  rfl

@[simp]
theorem stageAssignment_stage (index stage : ZFSet.{u}) :
    stageAssignment index stage (14 : Fin 15) = stage := by
  rfl

/-- At a reflection level, a raw witness for the internal stage formula is
the actual external constructible level. -/
theorem stage_eq_of_satisfiesIn
    (h : CondensationHull theta domain) (alpha : Ordinal.{u})
    (halpha : alpha.toZFSet ∈ LStageZF theta)
    (stage : ZFSet.{u}) (hstage : stage ∈ LStageZF theta)
    (hsat : Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
      Model.internalLStageAtFormula
      (stageAssignment alpha.toZFSet stage)) :
    stage = LStageZF alpha := by
  have hparams : forall i,
      stageAssignment alpha.toZFSet stage i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · rw [show Fin.last 14 = (14 : Fin 15) by rfl,
        stageAssignment_stage]
      exact hstage
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rw [show (Fin.last 13).castSucc = (13 : Fin 15) by rfl,
          stageAssignment_index]
        exact halpha
      · simpa [stageAssignment] using h.reflection.2.1 i13
  have hsatL :=
    (Model.satisfiesIn_internalLStageAt_iff_L_of_condensationReflectionLevel
      h.reflection (stageAssignment alpha.toZFSet stage) hparams).mp hsat
  let indexL : Model.LCarrier.{u} :=
    ⟨alpha.toZFSet, ordinal_toZFSet_mem_L alpha⟩
  let stageL : Model.LCarrier.{u} :=
    ⟨stage, mem_L_of_mem hstage (LStageZF_mem_L theta)⟩
  have htyped :
      FOFormula.Satisfies Model.lCarrierMem Model.internalLStageAtFormula
        (Model.internalLStageAtLAssignment indexL stageL) := by
    apply (Model.satisfies_lCarrier_iff_satisfiesIn_L
      Model.internalLStageAtFormula
      (Model.internalLStageAtLAssignment indexL stageL)).mpr
    convert hsatL using 1
    funext i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · simp [Model.internalLStageAtLAssignment, stageAssignment,
          indexL, stageL]
  have hinternal :=
    (Model.satisfies_internalLStageAtFormula indexL stageL).mp htyped
  have heq := (Model.internalLStageAt_ordinal_iff alpha stageL).mp hinternal
  exact congrArg Subtype.val heq

/-- Every constructible stage whose ordinal index belongs to the hull is
itself an element of the hull.  This lemma uses the full-elementarity field
at the fixed stage formula; the later bounded-stage theorem uses a further
formula instance at every limit index. -/
theorem stage_mem (h : CondensationHull theta domain)
    (alpha : Ordinal.{u}) (halpha : alpha.toZFSet ∈ domain) :
    LStageZF alpha ∈ domain := by
  let params : Tuple ZFSet.{u} 14 :=
    snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1)
      alpha.toZFSet
  have hparamsDomain : forall i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show Fin.last 13 = (13 : Fin 14) by rfl]
      change alpha.toZFSet ∈ domain
      exact halpha
    · simpa [params] using h.fixed_mem j
  have hordinalStage : alpha.toZFSet ∈ LStageZF theta :=
    h.subset_stage halpha
  rcases Model.exists_internalLStageIn_condensationReflectionLevel
      h.reflection alpha hordinalStage with ⟨stage, hstageTheta, hstageSat⟩
  have hexTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (.ex Model.internalLStageAtFormula) params := by
    refine ⟨stage, hstageTheta, ?_⟩
    simpa [params, stageAssignment] using hstageSat
  have hexDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        (.ex Model.internalLStageAtFormula) params :=
    (h.satisfactionAbsolute (.ex Model.internalLStageAtFormula)
      params hparamsDomain).mpr hexTheta
  rcases hexDomain with ⟨stage', hstage'Domain, hstage'DomainSat⟩
  have hfullParamsDomain : forall i, snoc params stage' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show Fin.last 14 = (14 : Fin 15) by rfl]
      change stage' ∈ domain
      exact hstage'Domain
    · simpa using hparamsDomain j
  have hstage'ThetaSat :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.internalLStageAtFormula (snoc params stage') :=
    (h.satisfactionAbsolute Model.internalLStageAtFormula
      (snoc params stage') hfullParamsDomain).mp hstage'DomainSat
  have hstageEq : stage' = LStageZF alpha :=
    stage_eq_of_satisfiesIn h alpha (h.subset_stage halpha) stage'
      (h.subset_stage hstage'Domain) (by
        simpa [params, stageAssignment] using hstage'ThetaSat)
  rw [← hstageEq]
  exact hstage'Domain

/-- The raw assignment selected by the stage subformula of
`constructibleWithParametersFormula`. -/
private theorem constructibleStageRename_assignment
    (x index stage : ZFSet.{u}) :
    (fun i =>
      snoc
        (snoc
          (snoc
            (fun j => (Model.stageHistoryFixedParameters.{u} j).1) x)
          index)
        stage (Model.constructibleInternalStageRename i)) =
      stageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
          Model.constructibleInternalStageRename
              i13.castSucc.castSucc =
            i13.castSucc.castSucc.castSucc := by
          simp only [Model.constructibleInternalStageRename,
            Fin.lastCases_castSucc]
          apply Fin.ext
          rfl
      rw [hrename]
      simp [stageAssignment]

/-- Every element of the hull is covered by a constructible stage whose
ordinal index also belongs to the hull. -/
theorem internallyStageCovered
    (h : CondensationHull theta domain) :
    InternallyStageCovered domain := by
  classical
  let fixed : Tuple ZFSet.{u} 13 :=
    fun i => (Model.stageHistoryFixedParameters.{u} i).1
  have hfixedDomain : forall i, fixed i ∈ domain := by
    intro i
    exact h.fixed_mem i
  have hcoreTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.vEqualsLCoreFormula fixed := by
    simpa only [fixed] using
      Model.satisfiesIn_vEqualsLCore_of_condensationReflectionLevel
        h.reflection
  have hcoreDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.vEqualsLCoreFormula fixed :=
    (h.satisfactionAbsolute Model.vEqualsLCoreFormula fixed
      hfixedDomain).mpr hcoreTheta
  have hall : forall x : ZFSet.{u}, x ∈ domain ->
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.constructibleWithParametersFormula (snoc fixed x) := by
    have hraw := hcoreDomain.2
    intro x hx
    by_contra hnot
    exact hraw ⟨x, hx, hnot⟩
  intro x hx
  rcases hall x hx with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexFormula, hstageFormula, hxStage⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change x ∈ stage at hxStage
  let full : Tuple ZFSet.{u} 16 :=
    snoc (snoc (snoc fixed x) index) stage
  have hfullDomain : forall i, full i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · change stage ∈ domain
      exact hstageDomain
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · change index ∈ domain
        exact hindexDomain
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · change x ∈ domain
          exact hx
        · simpa [full, fixed] using hfixedDomain i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (14 : Fin 16)) full :=
    (h.satisfactionAbsolute (Model.ordinalAt (14 : Fin 16)) full
      hfullDomain).mp (by simpa only [full] using hindexFormula)
  have hindexRaw :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        OrdinalFormula.isOrdinal ![index] := by
    have hrenamed :=
      (Model.satisfiesIn_rename (LStageZF theta : Set ZFSet.{u})
        OrdinalFormula.isOrdinal (fun _ : Fin 1 => (14 : Fin 16))
        full).mp hindexThetaFormula
    convert hrenamed using 1
    funext i
    fin_cases i
    rfl
  let indexTheta : ZFCarrier (LStageZF theta) :=
    ⟨index, h.subset_stage hindexDomain⟩
  have hindexTyped :
      FOFormula.Satisfies (zfCarrierMem (LStageZF theta))
        OrdinalFormula.isOrdinal ![indexTheta] := by
    apply (Model.satisfies_subtype_iff_satisfiesIn
      (LStageZF theta : Set ZFSet.{u}) OrdinalFormula.isOrdinal
      ![indexTheta]).mpr
    convert hindexRaw using 1
    funext i
    fin_cases i
    rfl
  have hindexOrdinal : index.IsOrdinal :=
    (OrdinalFormula.satisfies_isOrdinal
      (LStageZF_isTransitive theta) indexTheta).mp hindexTyped
  let alpha : Ordinal.{u} := index.rank
  have hindexEq : index = alpha.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.internalLStageAtFormula (stageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.internalLStageAtFormula
        Model.constructibleInternalStageRename
        (snoc (snoc (snoc fixed x) index) stage)).mp hstageFormula
    rw [constructibleStageRename_assignment x index stage] at hrenamed
    exact hrenamed
  have hstageParamsDomain : forall i,
      stageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · rw [show Fin.last 14 = (14 : Fin 15) by rfl,
        stageAssignment_stage]
      exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rw [show (Fin.last 13).castSucc = (13 : Fin 15) by rfl,
          stageAssignment_index]
        exact hindexDomain
      · simpa [stageAssignment, fixed] using hfixedDomain i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.internalLStageAtFormula (stageAssignment index stage) :=
    (h.satisfactionAbsolute Model.internalLStageAtFormula
      (stageAssignment index stage) hstageParamsDomain).mp
      hstageDirectDomain
  have hstageEq : stage = LStageZF alpha := by
    apply stage_eq_of_satisfiesIn h alpha
      (h.subset_stage (by simpa only [← hindexEq] using hindexDomain)) stage
      (h.subset_stage hstageDomain)
    simpa only [← hindexEq] using hstageThetaFormula
  refine ⟨alpha, ?_, ?_⟩
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq] using hxStage

/-! ## Bounded stage witnesses for the limit step -/

/-- Select `(fixed13, index, stage)` from the layout
`(fixed13, x, bound, index, stage)`. -/
def boundedStageInternalRename : Fin 15 -> Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13, x, bound)`. -/
def boundedStageParameters (x bound : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x)
    bound

/-- Layout `(fixed13, x, bound, index, stage)`. -/
def boundedStageWitnessAssignment
    (x bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (boundedStageParameters x bound) index) stage

private theorem boundedStageInternalRename_assignment
    (x bound index stage : ZFSet.{u}) :
    (fun i => boundedStageWitnessAssignment x bound index stage
      (boundedStageInternalRename i)) =
      stageAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · have hrename :
          boundedStageInternalRename i13.castSucc.castSucc =
            i13.castSucc.castSucc.castSucc.castSucc := by
          simp only [boundedStageInternalRename, Fin.lastCases_castSucc]
          apply Fin.ext
          rfl
      rw [hrename]
      simp [boundedStageWitnessAssignment, boundedStageParameters,
        stageAssignment]

/-- There is an ordinal `index ∈ bound` whose internally computed stage
contains `x`.  The free layout is `(fixed13, x, bound)`. -/
def boundedStageContainsFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (.mem (15 : Fin 17) (14 : Fin 17))
      (.conj
        (Model.ordinalAt (15 : Fin 17))
        (.conj
          (FOFormula.rename boundedStageInternalRename
            Model.internalLStageAtFormula)
          (.mem (13 : Fin 17) (16 : Fin 17))))))

/-- At a limit index in the hull, every hull element of that level already
belongs to an earlier level whose index and level are both in the hull. -/
theorem exists_bounded_stage
    (h : CondensationHull theta domain)
    {gamma : Ordinal.{u}} (hgammaLimit : Order.IsSuccLimit gamma)
    (hgamma : gamma.toZFSet ∈ domain)
    {x : ZFSet.{u}} (hxDomain : x ∈ domain)
    (hxStage : x ∈ LStageZF gamma) :
    exists delta : Ordinal.{u},
      delta < gamma ∧ delta.toZFSet ∈ domain ∧
        LStageZF delta ∈ domain ∧ x ∈ LStageZF delta := by
  classical
  rcases (mem_LStageZF_limit_iff hgammaLimit).mp hxStage with
    ⟨delta, hdeltaGamma, hxDelta⟩
  have hgammaTheta : gamma.toZFSet ∈ LStageZF theta :=
    h.subset_stage hgamma
  have hgammaLtTheta : gamma < theta := by
    have hrank := (ordinal_stage_invariants theta).1
      (ZFSet.isOrdinal_toZFSet gamma) hgammaTheta
    have heq : gamma.toZFSet.rank = gamma := by
      apply Ordinal.toZFSet_injective
      exact (ZFSet.isOrdinal_toZFSet gamma).toZFSet_rank_eq
    simpa only [heq] using hrank
  have hdeltaTheta : delta.toZFSet ∈ LStageZF theta := by
    apply (ordinal_stage_invariants theta).2
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (hdeltaGamma.trans hgammaLtTheta)
  have hLDeltaTheta : LStageZF delta ∈ LStageZF theta :=
    LStageZF_mem_of_lt (hdeltaGamma.trans hgammaLtTheta)
  rcases Model.exists_internalLStageIn_condensationReflectionLevel
      h.reflection delta hdeltaTheta with
    ⟨stage, hstageTheta, hstageSat⟩
  have hstageEq : stage = LStageZF delta :=
    stage_eq_of_satisfiesIn h delta hdeltaTheta stage hstageTheta
      (by simpa [stageAssignment] using hstageSat)
  subst stage
  let params := boundedStageParameters x gamma.toZFSet
  let full :=
    boundedStageWitnessAssignment x gamma.toZFSet
      delta.toZFSet (LStageZF delta)
  have hfullTheta : forall i, full i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · change LStageZF delta ∈ LStageZF theta
      exact hLDeltaTheta
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · change delta.toZFSet ∈ LStageZF theta
        exact hdeltaTheta
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · change gamma.toZFSet ∈ LStageZF theta
          exact hgammaTheta
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · change x ∈ LStageZF theta
            exact h.subset_stage hxDomain
          · simpa [full, boundedStageWitnessAssignment,
              boundedStageParameters] using h.reflection.2.1 i13
  have hordinalFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full :=
    (satisfiesIn_ordinalAt_iff (LStageZF_isTransitive theta)
      (15 : Fin 17) full hfullTheta).mpr
      (ZFSet.isOrdinal_toZFSet delta)
  have hstageFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (FOFormula.rename boundedStageInternalRename
          Model.internalLStageAtFormula) full := by
    rw [Model.satisfiesIn_rename,
      boundedStageInternalRename_assignment]
    simpa [stageAssignment] using hstageSat
  have hformulaTheta :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        boundedStageContainsFormula params := by
    refine ⟨delta.toZFSet, hdeltaTheta,
      LStageZF delta, hLDeltaTheta, ?_, hordinalFormula,
      hstageFormula, ?_⟩
    · change delta.toZFSet ∈ gamma.toZFSet
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hdeltaGamma
    · exact hxDelta
  have hparamsDomain : forall i, params i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · change gamma.toZFSet ∈ domain
      exact hgamma
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · change x ∈ domain
        exact hxDomain
      · simpa [params, boundedStageParameters] using h.fixed_mem i13
  have hformulaDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        boundedStageContainsFormula params :=
    (h.satisfactionAbsolute boundedStageContainsFormula params
      hparamsDomain).mpr hformulaTheta
  rcases hformulaDomain with
    ⟨index, hindexDomain, stage, hstageDomain,
      hindexBound, hindexFormula, hstageFormulaDomain, hxStage'⟩
  change index ∈ domain at hindexDomain
  change stage ∈ domain at hstageDomain
  change index ∈ gamma.toZFSet at hindexBound
  change x ∈ stage at hxStage'
  let full' :=
    boundedStageWitnessAssignment x gamma.toZFSet index stage
  have hfull'Domain : forall i, full' i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · change stage ∈ domain
      exact hstageDomain
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · change index ∈ domain
        exact hindexDomain
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · change gamma.toZFSet ∈ domain
          exact hgamma
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · change x ∈ domain
            exact hxDomain
          · simpa [full', boundedStageWitnessAssignment,
              boundedStageParameters] using h.fixed_mem i13
  have hindexThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        (Model.ordinalAt (15 : Fin 17)) full' :=
    (h.satisfactionAbsolute (Model.ordinalAt (15 : Fin 17)) full'
      hfull'Domain).mp (by
        simpa [full', params, boundedStageWitnessAssignment] using
          hindexFormula)
  have hindexOrdinal : index.IsOrdinal :=
    (satisfiesIn_ordinalAt_iff (LStageZF_isTransitive theta)
      (15 : Fin 17) full'
      (fun i => h.subset_stage (hfull'Domain i))).mp
      hindexThetaFormula
  let delta' : Ordinal.{u} := index.rank
  have hindexEq : index = delta'.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hstageDirectDomain :
      Model.SatisfiesIn (domain : Set ZFSet.{u})
        Model.internalLStageAtFormula (stageAssignment index stage) := by
    have hrenamed :=
      (Model.satisfiesIn_rename (domain : Set ZFSet.{u})
        Model.internalLStageAtFormula boundedStageInternalRename
        full').mp (by
          simpa [full', params, boundedStageWitnessAssignment] using
            hstageFormulaDomain)
    rw [boundedStageInternalRename_assignment] at hrenamed
    exact hrenamed
  have hstageParamsDomain : forall i,
      stageAssignment index stage i ∈ domain := by
    intro i
    refine Fin.lastCases ?_ (fun i14 => ?_) i
    · rw [show Fin.last 14 = (14 : Fin 15) by rfl,
        stageAssignment_stage]
      exact hstageDomain
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rw [show (Fin.last 13).castSucc = (13 : Fin 15) by rfl,
          stageAssignment_index]
        exact hindexDomain
      · simpa [stageAssignment] using h.fixed_mem i13
  have hstageThetaFormula :
      Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        Model.internalLStageAtFormula (stageAssignment index stage) :=
    (h.satisfactionAbsolute Model.internalLStageAtFormula
      (stageAssignment index stage) hstageParamsDomain).mp
      hstageDirectDomain
  have hstageEq' : stage = LStageZF delta' := by
    apply stage_eq_of_satisfiesIn h delta'
      (h.subset_stage (by simpa only [← hindexEq] using hindexDomain))
      stage (h.subset_stage hstageDomain)
    simpa only [← hindexEq] using hstageThetaFormula
  refine ⟨delta', ?_, ?_, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mp
      (by simpa only [← hindexEq] using hindexBound)
  · simpa only [← hindexEq] using hindexDomain
  · simpa only [← hstageEq'] using hstageDomain
  · simpa only [← hstageEq'] using hxStage'

/-- The bounded formula construction supplies exactly the witness interface
used by the abstract limit-collapse theorem. -/
theorem hasSmallerInternalLStageWitnesses
    (h : CondensationHull theta domain)
    {limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (hlimitDomain : limit.toZFSet ∈ domain) :
    HasSmallerInternalLStageWitnesses domain limit := by
  intro x hxDomain hxLimit
  rcases exists_bounded_stage h hlimit hlimitDomain hxDomain hxLimit with
    ⟨beta, hbetaLimit, hbetaDomain, _hstageDomain, hxBeta⟩
  exact ⟨beta, hbetaLimit, hbetaDomain, hxBeta⟩

/-- Assembly lemma for stage compatibility.  Its three functional inputs are
proved from full elementarity and from the separate `DefZF`-collapse theorem;
the final condensation theorem below does not expose them as assumptions. -/
theorem collapseStageCompatibleAt_of_interfaces
    (h : CondensationHull theta domain)
    (hcommutes : CollapseDefZFCommutes domain)
    (hpredecessor : forall alpha : Ordinal.{u},
      (Order.succ alpha).toZFSet ∈ domain -> alpha.toZFSet ∈ domain)
    (hlimitImage : forall limit : Ordinal.{u},
      Order.IsSuccLimit limit -> limit.toZFSet ∈ domain ->
        Order.IsSuccLimit (collapseOrdinal domain limit)) :
    forall alpha : Ordinal.{u}, alpha.toZFSet ∈ domain ->
      CollapseStageCompatibleAt domain alpha := by
  intro alpha
  induction alpha using Ordinal.limitRecOn with
  | zero =>
      intro _hzero
      exact collapseStageCompatibleAt_zero domain
  | add_one alpha ih =>
      intro hsuccessor
      have halphaDomain : alpha.toZFSet ∈ domain :=
        hpredecessor alpha hsuccessor
      have hstageDomain : LStageZF alpha ∈ domain :=
        h.stage_mem alpha halphaDomain
      have hnextStageDomain : DefZF (LStageZF alpha) ∈ domain := by
        rw [← LStageZF_succ]
        exact h.stage_mem (Order.succ alpha) hsuccessor
      change collapse domain (LStageZF (Order.succ alpha)) =
        LStageZF (collapseOrdinal domain (Order.succ alpha))
      rw [LStageZF_succ, hcommutes hstageDomain hnextStageDomain,
        ih halphaDomain, collapseOrdinal_succ halphaDomain,
        LStageZF_succ]
  | limit limit hlimit ih =>
      intro hlimitDomain
      apply collapseStageCompatibleAt_limit
        (hlimitImage limit hlimit hlimitDomain)
        (h.hasSmallerInternalLStageWitnesses hlimit hlimitDomain)
      intro beta hbeta hbetaDomain
      exact ih beta hbeta hbetaDomain

/-- Stage compatibility transports the hull's stage coverage to its
transitive collapse. -/
theorem internallyStageCovered_range_of_stageCompatible
    (h : CondensationHull theta domain)
    (hstage : forall alpha : Ordinal.{u}, alpha.toZFSet ∈ domain ->
      CollapseStageCompatibleAt domain alpha) :
    InternallyStageCovered (range domain) := by
  intro z hzRange
  rcases mem_range_iff.mp hzRange with ⟨x, hxDomain, hcollapse⟩
  rcases h.internallyStageCovered x hxDomain with
    ⟨alpha, halphaDomain, hxStage⟩
  refine ⟨collapseOrdinal domain alpha, ?_, ?_⟩
  · apply mem_range_iff.mpr
    refine ⟨alpha.toZFSet, halphaDomain, ?_⟩
    exact (collapseOrdinal_toZFSet domain alpha).symm
  · have hmemCollapse :
        collapse domain x ∈ collapse domain (LStageZF alpha) :=
      mem_collapse_iff.mpr ⟨x, hxStage, hxDomain, rfl⟩
    rw [hstage alpha halphaDomain] at hmemCollapse
    simpa only [hcollapse] using hmemCollapse

/-- Stage compatibility also shows that every stage indexed by an ordinal of
the transitive collapse is itself an element of that collapse. -/
theorem containsInternalLStages_range_of_stageCompatible
    (h : CondensationHull theta domain)
    (hstage : forall alpha : Ordinal.{u}, alpha.toZFSet ∈ domain ->
      CollapseStageCompatibleAt domain alpha) :
    ContainsInternalLStages (range domain) := by
  intro alpha halphaRange
  rcases mem_range_iff.mp halphaRange with
    ⟨index, hindexDomain, hindexCollapse⟩
  have hindexOrdinal : index.IsOrdinal :=
    (isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
      h.isExtensional h.subset_stage (LStageZF_isTransitive theta)
      h.satisfactionAbsolute hindexDomain).mpr
      (hindexCollapse ▸ ZFSet.isOrdinal_toZFSet alpha)
  let beta : Ordinal.{u} := index.rank
  have hindexEq : index = beta.toZFSet :=
    hindexOrdinal.toZFSet_rank_eq.symm
  have hbetaDomain : beta.toZFSet ∈ domain := by
    simpa only [← hindexEq] using hindexDomain
  have hcollapsedBeta : collapseOrdinal domain beta = alpha := by
    apply Ordinal.toZFSet_injective
    rw [collapseOrdinal_toZFSet, ← hindexEq]
    exact hindexCollapse
  have hstageDomain : LStageZF beta ∈ domain :=
    h.stage_mem beta hbetaDomain
  apply mem_range_iff.mpr
  refine ⟨LStageZF beta, hstageDomain, ?_⟩
  rw [hstage beta hbetaDomain, hcollapsedBeta]

/-- Once stage compatibility is available, the abstract condensation core
identifies the collapse range with the level at its ordinal height. -/
theorem range_eq_LStageZF_ordinalHeight_of_stageCompatible
    (h : CondensationHull theta domain)
    (hstage : forall alpha : Ordinal.{u}, alpha.toZFSet ∈ domain ->
      CollapseStageCompatibleAt domain alpha) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
  apply eq_LStageZF_ordinalHeight_of_condensationCore
  · exact range_isTransitive domain
  · exact ordinalSuccessorClosed_range_of_elementary_LStage
      h.reflection.1 h.isExtensional h.subset_stage
        h.satisfactionAbsolute
  · exact h.internallyStageCovered_range_of_stageCompatible hstage
  · exact h.containsInternalLStages_range_of_stageCompatible hstage

/-- Full elementarity supplies all interfaces in the transfinite stage
compatibility proof.  In particular, successor compatibility is the theorem
`collapse_DefZF_eq_DefZF_collapse`, not an additional assumption. -/
theorem collapseStageCompatible
    (h : CondensationHull theta domain) :
    forall alpha : Ordinal.{u}, alpha.toZFSet ∈ domain ->
      CollapseStageCompatibleAt domain alpha := by
  have hcommutes : CollapseDefZFCommutes domain := by
    intro a ha hDef
    exact collapse_DefZF_eq_DefZF_collapse h.subset_stage
      (LStageZF_isTransitive theta) h.satisfactionAbsolute ha hDef
  have hpredecessor : forall alpha : Ordinal.{u},
      (Order.succ alpha).toZFSet ∈ domain -> alpha.toZFSet ∈ domain := by
    intro alpha hsuccessor
    exact ordinalPredecessor_mem_of_succ_mem h.subset_stage
      (LStageZF_isTransitive theta) h.satisfactionAbsolute hsuccessor
  have hsourceSuccessor : SourceOrdinalSuccessorClosed domain := by
    apply sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
      h.subset_stage (LStageZF_isTransitive theta)
        h.satisfactionAbsolute
    intro x hxDomain _hxOrdinal
    exact insert_self_mem_LStageZF_of_isSuccLimit h.reflection.1
      (h.subset_stage hxDomain)
  have hempty : (∅ : ZFSet.{u}) ∈ domain := by
    have hfixed := h.fixed_mem (2 : Fin 13)
    rw [Model.stageHistoryFixedParameters_empty] at hfixed
    change (∅ : ZFSet.{u}) ∈ domain at hfixed
    exact hfixed
  have hlimitImage : forall limit : Ordinal.{u},
      Order.IsSuccLimit limit -> limit.toZFSet ∈ domain ->
        Order.IsSuccLimit (collapseOrdinal domain limit) := by
    intro limit hlimit _hlimitDomain
    exact collapseOrdinal_isSuccLimit_of_source_closed
      hlimit hempty hsourceSuccessor
  exact h.collapseStageCompatibleAt_of_interfaces hcommutes
    hpredecessor hlimitImage

/-- The full constructible Condensation Lemma for a set-sized fully
elementary hull of a condensation reflection level. -/
theorem condensation
    (h : CondensationHull theta domain) :
    range domain = LStageZF (ordinalHeight (range domain)) :=
  h.range_eq_LStageZF_ordinalHeight_of_stageCompatible
    h.collapseStageCompatible

/-- Existential formulation of `condensation`, convenient for downstream
applications that do not need the canonical ordinal height. -/
theorem exists_eq_LStageZF
    (h : CondensationHull theta domain) :
    exists beta : Ordinal.{u}, range domain = LStageZF beta :=
  ⟨ordinalHeight (range domain), h.condensation⟩

/-- Condensation with only the mathematical elementarity data exposed. The
ambient-level restriction remains explicit: `theta` must be one of the
cofinal reflection levels at which the internal stage formula is known to be
absolute. -/
theorem condensation_of_elementary_at_reflectionLevel
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem :
      SatisfactionAbsolute (domain : Set ZFSet.{u})
        (LStageZF theta : Set ZFSet.{u})) :
    range domain = LStageZF (ordinalHeight (range domain)) :=
  (of_elementary hreflection hsubset helem).condensation

end CondensationHull

end

end MostowskiCollapse

end Constructible
