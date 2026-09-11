/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryOmega
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryBounds
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareGodelDefFinite

/-!
# The global canonical-history invariant

This file assembles the exact transfinite induction for

`canonicalBareHistory alpha ∈ L_(alpha + omega)`.

The evaluator inputs are kept explicit.  The first is the finite-stage fact
needed only at the exceptional limit `omega`; the second is ordinary local
evaluator correctness at limit levels strictly above `omega`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The exact finite-input evaluator contract needed at the first infinite
history stage.  The predecessor is an actual finite level `L_n`; no claim is
made about arbitrary predecessor inputs in `L_(omega+1)`. -/
theorem finiteBareGodelDefOutputCorrectIn_omega_succ :
    FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw := by
  intro n stage _hpredecessor hstage
  exact bareGodelDefOutputIn_omega_succ_natCast_iff n stage hstage

/-- The honest global history bound from the two exact evaluator facts used
by its proof.  Neither premise is a disguised history-bound assumption. -/
theorem canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators
    (hfinite : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw)
    (hlimitEvaluator : forall limit : Ordinal.{u},
      Order.IsSuccLimit limit -> Ordinal.omega0 < limit ->
        BareGodelDefOutputCorrectIn (LStageZF limit)
          stageHistoryFixedParametersRaw) :
    forall ordinal : Ordinal.{u},
      canonicalBareHistory ordinal ∈
        LStageZF (ordinal + Ordinal.omega0) := by
  apply canonicalBareHistory_global_bound_of_omega_and_limit_evaluator
  · exact
      canonicalBareHistory_omega_mem_LStageZF_add_omega_of_finite_correct
        hfinite
  · exact hlimitEvaluator

/-- Once the exact finite-input fact at `L_(omega+1)` is supplied, the
global history bound is unconditional at all larger limit levels: evaluator
correctness there is the proved limit-level absoluteness theorem. -/
theorem canonicalBareHistory_mem_LStageZF_add_omega_of_finite_correct
    (hfinite : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    forall ordinal : Ordinal.{u},
      canonicalBareHistory ordinal ∈
        LStageZF (ordinal + Ordinal.omega0) := by
  apply canonicalBareHistory_mem_LStageZF_add_omega_of_evaluators hfinite
  intro limit hlimit homega
  exact
    Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
      hlimit homega

/-- The exceptional history through `omega` belongs to the stated target
level, with its finite evaluator obligation now discharged. -/
theorem canonicalBareHistory_omega_mem_LStageZF_add_omega :
    canonicalBareHistory (Ordinal.omega0 : Ordinal.{u}) ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) :=
  canonicalBareHistory_omega_mem_LStageZF_add_omega_of_finite_correct
    finiteBareGodelDefOutputCorrectIn_omega_succ

/-- Unconditional global canonical-history bound. -/
theorem canonicalBareHistory_mem_LStageZF_add_omega
    (ordinal : Ordinal.{u}) :
    canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0) :=
  canonicalBareHistory_mem_LStageZF_add_omega_of_finite_correct
    finiteBareGodelDefOutputCorrectIn_omega_succ ordinal

end

end Constructible.Model
