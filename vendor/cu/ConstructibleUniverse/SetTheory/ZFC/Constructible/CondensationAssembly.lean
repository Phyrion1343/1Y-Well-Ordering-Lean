/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Condensation

/-!
# The assumption-transparent assembly step for Condensation

This file does not state the standard Condensation Lemma under disguised
hypotheses.  It isolates the last part of its usual proof after the uniform
definability of the hierarchy has supplied the following facts about an
elementary substructure `domain` of a limit level `L_theta`:

* the empty set belongs to `domain`;
* every internally indexed level `L_alpha` belongs to `domain`;
* every member of `domain` occurs in such an internally indexed level;
* at a limit index in `domain`, membership in that level has a witness at a
  smaller index which also belongs to `domain`.

These are explicit fields below.  A later theorem may use this assembly for
the standard result only after deriving every field from ordinary
elementarity at an arbitrary limit level.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/--
The exact derived interfaces used by the collapse-induction part of the
standard Condensation proof.  This is a technical proof package, not the
definition of an elementary substructure and not the statement of
Condensation itself.
-/
structure StageCondensationInterfaces
    (theta : Ordinal.{u}) (domain : ZFSet.{u}) : Prop where
  isLimit : Order.IsSuccLimit theta
  subset_stage : domain ⊆ LStageZF theta
  satisfactionAbsolute :
    SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})
  empty_mem : (∅ : ZFSet.{u}) ∈ domain
  stage_mem : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
    LStageZF alpha ∈ domain
  internallyStageCovered : InternallyStageCovered domain
  smallerStageWitnesses : ∀ limit : Ordinal.{u},
    Order.IsSuccLimit limit → limit.toZFSet ∈ domain →
      HasSmallerInternalLStageWitnesses domain limit

namespace StageCondensationInterfaces

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}

/-- The previously proved reflection-level hull supplies every field of the
transparent assembly interface.  This adapter does not turn a reflection
level into an arbitrary limit level; its source type keeps that restriction
visible. -/
theorem ofCondensationHull (h : CondensationHull theta domain) :
    StageCondensationInterfaces theta domain where
  isLimit := h.reflection.1
  subset_stage := h.subset_stage
  satisfactionAbsolute := h.satisfactionAbsolute
  empty_mem := by
    have hempty := h.fixed_mem (2 : Fin 13)
    rw [Model.stageHistoryFixedParameters_empty] at hempty
    exact hempty
  stage_mem := h.stage_mem
  internallyStageCovered := h.internallyStageCovered
  smallerStageWitnesses := by
    intro limit hlimit hlimitDomain
    exact h.hasSmallerInternalLStageWitnesses hlimit hlimitDomain

/-- Full elementarity in a transitive ambient level gives extensionality of
the membership relation restricted to `domain`. -/
theorem isExtensional (h : StageCondensationInterfaces theta domain) :
    IsExtensional domain := by
  intro x hx y hy hsame
  apply restricted_extensionality_of_closesWithinAll
    h.subset_stage (LStageZF_isTransitive theta)
    (closesWithinAll_of_satisfactionAbsolute h.satisfactionAbsolute)
    hx hy
  intro z hz
  exact hsame z hz

/-- The source ordinals in an elementary substructure of a limit level are
closed under von Neumann successor. -/
theorem sourceOrdinalSuccessorClosed
    (h : StageCondensationInterfaces theta domain) :
    SourceOrdinalSuccessorClosed domain := by
  apply sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    h.subset_stage (LStageZF_isTransitive theta)
      h.satisfactionAbsolute
  intro x hxDomain _hxOrdinal
  exact insert_self_mem_LStageZF_of_isSuccLimit h.isLimit
    (h.subset_stage hxDomain)

/-- The three explicit stage interfaces, together with full elementarity,
make collapse commute with every internally indexed constructible level. -/
theorem collapseStageCompatible
    (h : StageCondensationInterfaces theta domain) :
    ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha := by
  have hpredecessor : ∀ alpha : Ordinal.{u},
      (Order.succ alpha).toZFSet ∈ domain → alpha.toZFSet ∈ domain := by
    intro alpha hsuccessor
    exact ordinalPredecessor_mem_of_succ_mem h.subset_stage
      (LStageZF_isTransitive theta) h.satisfactionAbsolute hsuccessor
  have hsuccessor : ∀ alpha : Ordinal.{u},
      alpha.toZFSet ∈ domain →
      (Order.succ alpha).toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha →
        CollapseStageCompatibleAt domain (Order.succ alpha) := by
    intro alpha halpha hnext hcompatible
    have hstage : LStageZF alpha ∈ domain := h.stage_mem alpha halpha
    have hnextStage : DefZF (LStageZF alpha) ∈ domain := by
      rw [← LStageZF_succ]
      exact h.stage_mem (Order.succ alpha) hnext
    change collapse domain (LStageZF (Order.succ alpha)) =
      LStageZF (collapseOrdinal domain (Order.succ alpha))
    rw [LStageZF_succ,
      collapse_DefZF_eq_DefZF_collapse h.subset_stage
        (LStageZF_isTransitive theta) h.satisfactionAbsolute
        hstage hnextStage,
      hcompatible, collapseOrdinal_succ halpha, LStageZF_succ]
  have hlimitImage : ∀ limit : Ordinal.{u},
      Order.IsSuccLimit limit → limit.toZFSet ∈ domain →
        Order.IsSuccLimit (collapseOrdinal domain limit) := by
    intro limit hlimit _hlimitDomain
    exact collapseOrdinal_isSuccLimit_of_source_closed
      hlimit h.empty_mem h.sourceOrdinalSuccessorClosed
  exact collapseStageCompatibleAt_of_zero_succ_limit
    hpredecessor hsuccessor hlimitImage h.smallerStageWitnesses

/-- Stage compatibility transports source stage coverage to the transitive
collapse. -/
theorem internallyStageCovered_range
    (h : StageCondensationInterfaces theta domain)
    (hstage : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha) :
    InternallyStageCovered (range domain) := by
  intro z hzRange
  rcases mem_range_iff.mp hzRange with ⟨x, hxDomain, hcollapse⟩
  rcases h.internallyStageCovered x hxDomain with
    ⟨alpha, halphaDomain, hxStage⟩
  refine ⟨collapseOrdinal domain alpha, ?_, ?_⟩
  · apply mem_range_iff.mpr
    exact ⟨alpha.toZFSet, halphaDomain,
      (collapseOrdinal_toZFSet domain alpha).symm⟩
  · have hxCollapsedStage :
        collapse domain x ∈ collapse domain (LStageZF alpha) :=
      mem_collapse_iff.mpr ⟨x, hxStage, hxDomain, rfl⟩
    rw [hstage alpha halphaDomain] at hxCollapsedStage
    simpa only [hcollapse] using hxCollapsedStage

/-- Stage membership and compatibility put every internally indexed level
into the transitive collapse. -/
theorem containsInternalLStages_range
    (h : StageCondensationInterfaces theta domain)
    (hstage : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
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
  apply mem_range_iff.mpr
  refine ⟨LStageZF beta, h.stage_mem beta hbetaDomain, ?_⟩
  rw [hstage beta hbetaDomain, hcollapsedBeta]

/-- Assumption-transparent assembly theorem.  Its conclusion is exactly the
usual Condensation conclusion, while every still-unproved stage-definability
consequence remains visible in `StageCondensationInterfaces`. -/
theorem range_eq_LStageZF_ordinalHeight
    (h : StageCondensationInterfaces theta domain) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
  let hstage := h.collapseStageCompatible
  apply eq_LStageZF_ordinalHeight_of_condensationCore
  · exact range_isTransitive domain
  · exact ordinalSuccessorClosed_range_of_elementary_LStage
      h.isLimit h.isExtensional h.subset_stage h.satisfactionAbsolute
  · exact h.internallyStageCovered_range hstage
  · exact h.containsInternalLStages_range hstage

/-- Existential form of the transparent assembly theorem. -/
theorem exists_range_eq_LStageZF
    (h : StageCondensationInterfaces theta domain) :
    ∃ beta : Ordinal.{u}, range domain = LStageZF beta :=
  ⟨ordinalHeight (range domain), h.range_eq_LStageZF_ordinalHeight⟩

end StageCondensationInterfaces

end

end MostowskiCollapse

end Constructible
