/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistorySemantics

/-!
# Exact local correctness from canonical-history bounds

This file packages the two independent parts of the bare-stage argument.
Soundness follows by induction over any internally valid history, whereas
completeness uses the actual graph

`{ <beta, L_beta> | beta <= alpha }`.

The only remaining inputs are stated literally: correctness of the internal
Goedel evaluator and membership of each required canonical graph in the
ambient transitive set.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- Exact correctness of the bare-stage predicate follows once every
canonical history whose index is visible in `U` is itself an element of
`U`.  This is a packaging theorem, not a history-bound assertion. -/
theorem canonicalBareStagesCorrectIn_of_histories_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (hcorrect : BareGodelDefOutputCorrectIn U
      stageHistoryFixedParametersRaw)
    (hhistories : forall ordinal : Ordinal.{u},
      ordinal.toZFSet ∈ U -> canonicalBareHistory ordinal ∈ U) :
    CanonicalBareStagesCorrectIn U stageHistoryFixedParametersRaw := by
  intro ordinal stage hindex hstage
  exact bareStageAtIn_ordinal_iff_of_canonicalHistory_mem hU
    stageHistoryFixedParametersRaw stageHistoryFixedParametersRaw_empty
    hcorrect ordinal stage hindex hstage (hhistories ordinal hindex)

/-- Specialization of the packaging theorem to a constructible level. -/
theorem canonicalBareStagesCorrectIn_LStageZF_of_histories_mem
    (theta : Ordinal.{u})
    (hcorrect : BareGodelDefOutputCorrectIn (LStageZF theta)
      stageHistoryFixedParametersRaw)
    (hhistories : forall ordinal : Ordinal.{u},
      ordinal.toZFSet ∈ LStageZF theta ->
        canonicalBareHistory ordinal ∈ LStageZF theta) :
    CanonicalBareStagesCorrectIn (LStageZF theta)
      stageHistoryFixedParametersRaw :=
  canonicalBareStagesCorrectIn_of_histories_mem
    (LStageZF_isTransitive theta) hcorrect hhistories

end

end Constructible.Model
