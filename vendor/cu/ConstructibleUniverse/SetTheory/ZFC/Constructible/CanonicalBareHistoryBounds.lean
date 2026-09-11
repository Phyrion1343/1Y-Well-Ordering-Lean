/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryOmegaBounds
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareStageCorrectness

/-!
# The global canonical-history bound from explicit local inputs

This file carries out the transfinite induction for the intended invariant

`canonicalBareHistory alpha ∈ LStageZF (alpha + omega)`.

Two inputs remain visible in the theorem statement: the bound at the first
infinite limit, and correctness of the internal Goedel evaluator at every
larger limit level.  In particular, this file does not assert either input
under a disguised name.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

private theorem ordinal_lt_of_toZFSet_mem_LStageZF_for_history_bound
    {theta ordinal : Ordinal.{u}}
    (hordinal : ordinal.toZFSet ∈ LStageZF theta) : ordinal < theta := by
  have hrank := (ordinal_stage_invariants theta).1
    (ZFSet.isOrdinal_toZFSet ordinal) hordinal
  have heq : (ordinal.toZFSet : ZFSet.{u}).rank = ordinal := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet ordinal).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- The global canonical-history bound, conditional on exactly the two
inputs not supplied by the elementary finite and successor arguments:

* the history through `omega` belongs to `L_(omega + omega)`;
* at every limit `lambda > omega`, the internal Goedel evaluator over
  `L_lambda` has its intended ambient semantics.

At a larger limit, local stage correctness is derived only from history
bounds at strictly smaller ordinals.  Thus the proof is a genuine
transfinite induction rather than a circular use of the global conclusion. -/
theorem canonicalBareHistory_global_bound_of_omega_and_limit_evaluator
    (homegaHistory : canonicalBareHistory (Ordinal.omega0 : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 + Ordinal.omega0))
    (hevaluator : ∀ (limit : Ordinal.{u}),
      Order.IsSuccLimit limit → Ordinal.omega0 < limit →
        BareGodelDefOutputCorrectIn (LStageZF limit)
          stageHistoryFixedParametersRaw) :
    ∀ ordinal : Ordinal.{u}, canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0) := by
  intro ordinal
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      simpa using
        canonicalBareHistory_zero_mem_LStageZF_omega
  | add_one ordinal ih =>
      rw [← Order.succ_eq_add_one]
      exact canonicalBareHistory_succ_mem_LStageZF_add_omega ordinal ih
  | limit limit hlimit ih =>
      by_cases hlimitOmega : limit = Ordinal.omega0
      · subst limit
        exact homegaHistory
      · have homegaLimit : Ordinal.omega0 < limit :=
          lt_of_le_of_ne (Ordinal.omega0_le_of_isSuccLimit hlimit)
            (Ne.symm hlimitOmega)
        have hstageCorrectRaw :
            CanonicalBareStagesCorrectIn (LStageZF limit)
              stageHistoryFixedParametersRaw := by
          apply canonicalBareStagesCorrectIn_LStageZF_of_histories_mem
            limit (hevaluator limit hlimit homegaLimit)
          intro earlier hearlierCode
          have hearlier : earlier < limit :=
            ordinal_lt_of_toZFSet_mem_LStageZF_for_history_bound
              hearlierCode
          exact LStageZF_mono
            (add_omega_le_of_lt_isSuccLimit hlimit hearlier)
            (ih earlier hearlier)
        have hstageCorrect :
            CanonicalBareStagesCorrectIn (LStageZF limit)
              canonicalBareFixedParameters := by
          have hfixedEq : canonicalBareFixedParameters =
              stageHistoryFixedParametersRaw := by
            rfl
          rw [hfixedEq]
          exact hstageCorrectRaw
        exact canonicalBareHistory_mem_LStageZF_add_omega_of_limit_of_correct
          hlimit homegaLimit hstageCorrect

end

end Constructible.Model
