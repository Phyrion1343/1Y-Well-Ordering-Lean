/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistorySemantics
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationBareStage

/-!
# From canonical history bounds to exact bare-stage correctness

This file connects the two independent parts of the relation-free stage
argument to the existing, standard `BareStageCorrectAt` contract.

The hypotheses remain explicit:

* the canonical evaluator parameters belong to `L_theta`;
* the internally evaluated successor output is the ambient `godelDef`;
* for every `alpha < theta`, the actual canonical history through `alpha`
  belongs to `L_theta`.

The conclusion is not a weakened replacement: it is exactly
`BareStageCorrectAt theta`, the biconditional used by the Condensation
assembly.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace BareStageCondensation

private theorem bareStageAssignment_eq_raw
    (index stage : ZFSet.{u}) :
    bareStageAssignment index stage =
      Model.bareStageAtRawAssignment
        Model.stageHistoryFixedParametersRaw index stage := by
  rfl

/-- Exact final bridge with the local history bound stated directly at the
ambient level `L_theta`. -/
theorem bareStageCorrectAt_of_canonicalHistory_mem
    (theta : Ordinal.{u})
    (hfixed : ∀ i : Fin 13,
      Model.stageHistoryFixedParametersRaw.{u} i ∈ LStageZF theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
    (hhistory : ∀ alpha : Ordinal.{u}, alpha < theta →
      Model.canonicalBareHistory alpha ∈ LStageZF theta) :
    BareStageCorrectAt theta := by
  intro alpha stage hindex hstage
  have halpha : alpha < theta :=
    ordinal_lt_of_toZFSet_mem_LStageZF hindex
  have hsemantic :=
    Model.satisfiesIn_bareStageAtFormula_ordinal_iff_of_canonicalHistory_mem
      (LStageZF_isTransitive theta)
      Model.stageHistoryFixedParametersRaw hfixed
      Model.stageHistoryFixedParametersRaw_empty hevaluator
      alpha stage hindex hstage (hhistory alpha halpha)
  simpa only [bareStageAssignment_eq_raw] using hsemantic

/-- The usual invariant `H_alpha ∈ L_(alpha + omega)` supplies the direct
history premise at every nonzero limit `theta`. -/
theorem bareStageCorrectAt_of_add_omega_history_bound
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hfixed : ∀ i : Fin 13,
      Model.stageHistoryFixedParametersRaw.{u} i ∈ LStageZF theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
    (hhistoryBound : ∀ alpha : Ordinal.{u},
      Model.canonicalBareHistory alpha ∈
        LStageZF (alpha + Ordinal.omega0)) :
    BareStageCorrectAt theta := by
  apply bareStageCorrectAt_of_canonicalHistory_mem theta
    hfixed hevaluator
  intro alpha halpha
  exact LStageZF_mono
    (Model.add_omega_le_of_lt_isSuccLimit htheta halpha)
    (hhistoryBound alpha)

/-- Above `omega`, canonical fixed-parameter membership is automatic.  Thus
evaluator correctness and the honest canonical-history bound are precisely
the two remaining mathematical inputs to exact local stage correctness. -/
theorem bareStageCorrectAt_of_evaluator_and_history_bounds
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
  (hhistoryBound : ∀ alpha : Ordinal.{u},
      Model.canonicalBareHistory alpha ∈
        LStageZF (alpha + Ordinal.omega0)) :
    BareStageCorrectAt theta := by
  apply bareStageCorrectAt_of_add_omega_history_bound htheta
    (hevaluator := hevaluator)
  · intro i
    simpa only [Model.stageHistoryFixedParametersRaw] using
      (Model.stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
        homega i)
  · exact hhistoryBound

/-- The same bridge fed into the existing transparent Condensation assembly.
No premise of `BareStageCorrectAt` is hidden or discarded. -/
theorem exists_range_eq_LStageZF_of_evaluator_and_history_bounds
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u}))
    (hevaluator : Model.BareGodelDefOutputCorrectIn
      (LStageZF theta) Model.stageHistoryFixedParametersRaw)
    (hhistoryBound : ∀ alpha : Ordinal.{u},
      Model.canonicalBareHistory alpha ∈
        LStageZF (alpha + Ordinal.omega0)) :
    ∃ beta : Ordinal.{u},
      MostowskiCollapse.range domain = LStageZF beta := by
  apply exists_range_eq_LStageZF_of_bareStageCorrect
    htheta homega hsubset helem
  exact bareStageCorrectAt_of_evaluator_and_history_bounds
    htheta homega hevaluator hhistoryBound

end BareStageCondensation

end

end MostowskiCollapse

end Constructible
