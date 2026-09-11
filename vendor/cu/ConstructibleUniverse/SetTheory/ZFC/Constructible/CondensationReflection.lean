/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# Cofinal reflection levels for condensation

A condensation argument needs an ambient level at which the fixed internal
definition of the constructible hierarchy is correct.  This is separate from
the later requirement that a Skolem hull be elementary for *all* formulas.

The single formula below contains both the `V = L` core and, as a syntactic
subformula, the assertion that a stage exists at a supplied index.  Applying
the existing reflection construction to that formula gives arbitrarily high
limit levels at which both relevant subformulas are absolute to `L`.
-/

@[expose] public section

universe u

namespace Constructible

open Set

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-- The formula whose closure supplies both ingredients needed by the
condensation proof.  The second conjunct is used only to place
`exists stage, InternalLStageAt index stage` among its subformulas; it is not
asserted for nonordinal indices. -/
def condensationReflectionFormula : FOFormula 13 :=
  .conj vEqualsLCoreFormula
    (FOFormula.all (.ex internalLStageAtFormula))

/-- A common starting level containing all thirteen fixed evaluator
parameters. -/
noncomputable def condensationParameterBound : Ordinal.{u} :=
  iSup fun i : Fin 13 =>
    stageOf (stageHistoryFixedParameters.{u} i).1
      (stageHistoryFixedParameters.{u} i).2

theorem stageHistoryFixedParameters_mem_parameterBound (i : Fin 13) :
    (stageHistoryFixedParameters.{u} i).1 ∈
      LStageZF condensationParameterBound := by
  unfold condensationParameterBound
  exact LStageZF_mono
    (Ordinal.le_iSup
      (fun j : Fin 13 =>
        stageOf (stageHistoryFixedParameters.{u} j).1
          (stageHistoryFixedParameters.{u} j).2) i)
    (mem_LStageZF_stageOf (stageHistoryFixedParameters.{u} i).1
      (stageHistoryFixedParameters.{u} i).2)

/-- The canonical cofinal family of levels used by condensation. -/
noncomputable def condensationReflectionOrdinal (alpha : Ordinal.{u}) :
    Ordinal.{u} :=
  reflectionOrdinal condensationReflectionFormula
    (max alpha condensationParameterBound)

theorem le_condensationReflectionOrdinal (alpha : Ordinal.{u}) :
    alpha ≤ condensationReflectionOrdinal alpha := by
  exact (le_max_left alpha condensationParameterBound).trans
    (le_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound))

theorem condensationReflectionOrdinal_isSuccLimit (alpha : Ordinal.{u}) :
    Order.IsSuccLimit (condensationReflectionOrdinal alpha) :=
  reflectionOrdinal_isSuccLimit condensationReflectionFormula
    (max alpha condensationParameterBound)

theorem stageHistoryFixedParameters_mem_condensationReflectionOrdinal
    (alpha : Ordinal.{u}) (i : Fin 13) :
    (stageHistoryFixedParameters.{u} i).1 ∈
      LStageZF (condensationReflectionOrdinal alpha) := by
  apply LStageZF_mono _
    (stageHistoryFixedParameters_mem_parameterBound i)
  exact (le_max_right alpha condensationParameterBound).trans
    (le_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound))

/-- Closure data retained from the reflection construction.  Keeping the
closure, rather than only the truth value of one sentence, exposes the two
subformula absoluteness statements needed below. -/
def IsCondensationReflectionLevel (theta : Ordinal.{u}) : Prop :=
  Order.IsSuccLimit theta ∧
    (∀ i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ LStageZF theta) ∧
    ClosesFrom vEqualsLCoreFormula theta theta ∧
    ClosesFrom (.ex internalLStageAtFormula) theta theta

private theorem closes_vEquals_of_closes_condensationReflection
    {theta : Ordinal.{u}}
    (hclose : ClosesFrom condensationReflectionFormula theta theta) :
    ClosesFrom vEqualsLCoreFormula theta theta :=
  hclose.1

private theorem closes_existsStage_of_closes_condensationReflection
    {theta : Ordinal.{u}}
    (hclose : ClosesFrom condensationReflectionFormula theta theta) :
    ClosesFrom (.ex internalLStageAtFormula) theta theta := by
  exact hclose.2.1

/-- Condensation reflection levels occur above every prescribed ordinal. -/
theorem exists_condensationReflectionLevel (alpha : Ordinal.{u}) :
    ∃ theta : Ordinal.{u}, alpha ≤ theta ∧
      IsCondensationReflectionLevel theta := by
  let theta := condensationReflectionOrdinal alpha
  have hclose :
      ClosesFrom condensationReflectionFormula theta theta :=
    closesFrom_reflectionOrdinal condensationReflectionFormula
      (max alpha condensationParameterBound)
  refine ⟨theta, le_condensationReflectionOrdinal alpha,
    condensationReflectionOrdinal_isSuccLimit alpha, ?_,
    closes_vEquals_of_closes_condensationReflection hclose,
    closes_existsStage_of_closes_condensationReflection hclose⟩
  intro i
  exact stageHistoryFixedParameters_mem_condensationReflectionOrdinal alpha i

/-- At a condensation reflection level, the fixed `V = L` core has its
intended canonical assignment. -/
theorem satisfiesIn_vEqualsLCore_of_condensationReflectionLevel
    {theta : Ordinal.{u}} (htheta : IsCondensationReflectionLevel theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u}) vEqualsLCoreFormula
      (fun i => (stageHistoryFixedParameters.{u} i).1) := by
  apply (satisfiesIn_stage_iff_L_of_closes vEqualsLCoreFormula theta
    htheta.2.2.1 (fun i => (stageHistoryFixedParameters.{u} i).1)
    htheta.2.1).mpr
  apply (satisfies_lCarrier_iff_satisfiesIn_L vEqualsLCoreFormula
    (stageHistoryFixedParameters.{u})).mp
  exact (satisfies_vEqualsLCoreFormula
    (stageHistoryFixedParameters.{u})).mpr rfl

/-- The stage-at-index subformula itself is absolute between a condensation
reflection level and the full constructible universe. -/
theorem satisfiesIn_internalLStageAt_iff_L_of_condensationReflectionLevel
    {theta : Ordinal.{u}} (htheta : IsCondensationReflectionLevel theta)
    (s : Tuple ZFSet.{u} 15) (hs : ∀ i, s i ∈ LStageZF theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        internalLStageAtFormula s ↔
      SatisfiesIn L internalLStageAtFormula s := by
  exact satisfiesIn_stage_iff_L_of_closes internalLStageAtFormula theta
    htheta.2.2.2.1 s hs

/-- Every ordinal index belonging to a condensation reflection level has an
internally witnessed constructible stage in that same level. -/
theorem exists_internalLStageIn_condensationReflectionLevel
    {theta : Ordinal.{u}} (htheta : IsCondensationReflectionLevel theta)
    (ordinal : Ordinal.{u}) (hordinal : ordinal.toZFSet ∈ LStageZF theta) :
    ∃ stage : ZFSet.{u}, stage ∈ LStageZF theta ∧
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        internalLStageAtFormula
        (snoc
          (snoc (fun i => (stageHistoryFixedParameters.{u} i).1)
            ordinal.toZFSet)
          stage) := by
  let indexL : LCarrier.{u} := ordinalLCarrier ordinal
  let stageL := stageLCarrier ordinal
  have hstageL :
      FOFormula.Satisfies LMem internalLStageAtFormula
        (internalLStageAtLAssignment indexL stageL) := by
    apply (satisfies_internalLStageAtFormula indexL stageL).mpr
    change ∃ relation : LCarrier.{u},
      StageStateAt (ordinalLCarrier ordinal) (stageLCarrier ordinal) relation
    exact exists_stageStateAt_ordinal ordinal
  have hstageRaw :
      SatisfiesIn L internalLStageAtFormula
        (snoc
          (snoc (fun i => (stageHistoryFixedParameters.{u} i).1)
            ordinal.toZFSet)
          (LStageZF ordinal)) := by
    have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
      internalLStageAtFormula (internalLStageAtLAssignment indexL stageL)
    have hraw := hbridge.mp hstageL
    convert hraw using 1
    funext i
    refine Fin.lastCases ?_ (fun i13 => ?_) i
    · change LStageZF ordinal = (stageLCarrier ordinal).1
      rfl
    · refine Fin.lastCases ?_ (fun j => ?_) i13
      · change ordinal.toZFSet = (ordinalLCarrier ordinal).1
        rfl
      · simp [internalLStageAtLAssignment, indexL, stageL]
  have hexL :
      SatisfiesIn L (.ex internalLStageAtFormula)
        (snoc (fun i => (stageHistoryFixedParameters.{u} i).1)
          ordinal.toZFSet) := by
    exact ⟨LStageZF ordinal, LStageZF_mem_L ordinal, hstageRaw⟩
  have hparams : ∀ i,
      snoc (fun i => (stageHistoryFixedParameters.{u} i).1)
          ordinal.toZFSet i ∈ LStageZF theta := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [snoc_last] using hordinal
    · simpa only [snoc_castSucc] using htheta.2.1 j
  have hexStage :=
    (satisfiesIn_stage_iff_L_of_closes
      (.ex internalLStageAtFormula) theta htheta.2.2.2
      (snoc (fun i => (stageHistoryFixedParameters i).1)
        ordinal.toZFSet) hparams).mpr hexL
  exact hexStage

end

end Model

end Constructible
