/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalStageInjectionFamily
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalDefZFInjection

/-!
# Internal cardinal bounds for constructible stages

This file carries out the standard transfinite induction below the Hartogs
ordinal of an internal infinite cardinal.

* The zero stage is empty.
* At a successor, the previous-stage injection and the internal square
  absorption are passed to the genuine `DefZF` injection.
* At a nonzero limit, Replacement collects the earlier injection graphs.
  The canonical least-containing-stage selector injects the union into
  `limit x kappa`; Hartogs supplies `limit -> kappa`, and the internal square
  injection absorbs the product.

No externally indexed family is used as the graph witness at a limit.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/--
Every constructible stage strictly below the Hartogs ordinal of an internal
infinite cardinal internally injects into that cardinal.
-/
theorem injects_stageLCarrier_below_internalHartogs_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    ∀ ordinal : Ordinal.{u},
      ordinal < internalHartogsOrdinal kappa →
        Injects LMem (stageLCarrier ordinal) kappa := by
  have hsquare :
      Injects LMem (prodLCarrier kappa kappa) kappa :=
    injects_infiniteCardinalSquare_lCarrier hcardinal homega
  have hhartogs :=
    internalHartogsLCarrier_isHartogsNumber kappa
  intro ordinal
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro _hzero
      apply injects_of_subset_lCarrier
      intro x hx
      change x.1 ∈ LStageZF (0 : Ordinal.{u}) at hx
      rw [LStageZF_zero] at hx
      exact (ZFSet.notMem_empty x.1 hx).elim
  | add_one ordinal ih =>
      intro hsuccessor
      have hordinal :
          ordinal < internalHartogsOrdinal kappa :=
        (Order.lt_succ ordinal).trans hsuccessor
      have hprevious :
          Injects LMem (stageLCarrier ordinal) kappa :=
        ih hordinal
      have hdef :
          Injects LMem (DefZFLCarrier (stageLCarrier ordinal)) kappa :=
        injects_DefZFLCarrier_lCarrier hprevious homega hsquare
      have hdomain :
          stageLCarrier (Order.succ ordinal) =
            DefZFLCarrier (stageLCarrier ordinal) := by
        apply Subtype.ext
        simp only [stageLCarrier_val, LStageZF_succ,
          DefZFLCarrier_val]
      rw [← Order.succ_eq_add_one, hdomain]
      exact hdef
  | limit limit hlimit ih =>
      intro hlimitHartogs
      have hpointwise : ∀ earlier : Ordinal.{u}, earlier < limit →
          Injects LMem (stageLCarrier earlier) kappa := by
        intro earlier hearlier
        exact ih earlier hearlier
          (hearlier.trans hlimitHartogs)
      rcases exists_canonicalStageInjectionFamily
          limit kappa hpointwise with
        ⟨injectionFamily, graphFamily, hinjectionFamily, hinjections⟩
      have hlimitProduct :
          Injects LMem (stageLCarrier limit)
            (prodLCarrier (ordinalLCarrier limit) kappa) :=
        injects_limitStage_to_prod_of_internalInjectionFamily
          hlimit hinjectionFamily hinjections
      have hlimitMem :
          (ordinalLCarrier limit).1 ∈
            (internalHartogsLCarrier kappa).1 := by
        change (ordinalLCarrier limit).1 ∈
          (ordinalLCarrier
            (internalHartogsOrdinal kappa)).1
        exact (ordinalLCarrier_mem_ordinalLCarrier_iff
          (internalHartogsOrdinal kappa) limit).mpr
            hlimitHartogs
      have hlimitKappa :
          Injects LMem (ordinalLCarrier limit) kappa :=
        hhartogs.2.2 (ordinalLCarrier limit) hlimitMem
      have hproduct :
          Injects LMem
            (prodLCarrier (ordinalLCarrier limit) kappa)
            (prodLCarrier kappa kappa) :=
        injects_prod_of_injects_lCarrier hlimitKappa
          (injects_refl_lCarrier kappa)
      exact hlimitProduct.trans_lCarrier
        (hproduct.trans_lCarrier hsquare)

/--
The full Hartogs-stage bound required by the condensation-to-GCH argument.
-/
theorem hartogsStageBound_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    HartogsStageBound kappa :=
  hartogsStageBound_of_pointwise_stage_injects
    kappa hcardinal homega
      (injects_stageLCarrier_below_internalHartogs_lCarrier
        kappa hcardinal homega)

end

end Constructible.ContinuumFormula
