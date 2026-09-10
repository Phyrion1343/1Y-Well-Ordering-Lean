import OneYTruth.AuxiliarySkolem
import ConstructibleUniverse.SetTheory.ZFC.Constructible.LStageZFCardinality
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Countable bounds below the external first uncountable ordinal

Every countable subset of L_(omega_1) is contained in a smaller L stage.
Applied to the actual auxiliary Skolem hull, this supplies the successor
step for the elementary-stage construction. No internal constructibility
of W, expanded set theory, or reflection principle is assumed here.
-/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Cardinal Ordinal

universe u

abbrev Ambient := ZFCarrier (LStageZF (ω₁ : Ordinal.{u}))
abbrev Index := Set.Iio (ω₁ : Ordinal.{u})

instance : Nonempty Ambient.{u} := by
  refine ⟨⟨LStageZF 0, ?_⟩⟩
  exact LStageZF_mono (show Order.succ 0 ≤ (ω₁ : Ordinal.{u}) from
    (Order.succ_le_iff.mpr (Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one)))
      (LStageZF_mem_succ 0)

def stageSet (α : Ordinal.{u}) : Set Ambient.{u} :=
  {x | x.val ∈ LStageZF α}

theorem stageSet_mono {α β : Ordinal.{u}} (h : α ≤ β) :
    stageSet α ⊆ stageSet β := fun _ hx => LStageZF_mono h hx

theorem countable_LStage {α : Ordinal.{u}} (hα : α < ω₁) :
    Countable (ZFCarrier (LStageZF α)) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_le_aleph0]
  apply (card_LStageZF_le_max α).trans
  exact max_le le_rfl (Cardinal.lt_aleph_one_iff.mp
    (Cardinal.lt_omega_iff_card_lt.mp hα))

theorem countable_stageSet {α : Ordinal.{u}} (hα : α < ω₁) :
    (stageSet α).Countable := by
  haveI := countable_LStage hα
  apply Set.countable_coe_iff.mp
  apply Function.Injective.countable (f :=
    fun x : stageSet α => (⟨x.val.val, x.property⟩ : ZFCarrier (LStageZF α)))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ZFCarrier (LStageZF α) => z.val) h

/-- An actual bound for all elements of a countable subset, above any given index. -/
theorem exists_stage_bound (s : Set Ambient.{u}) (hs : s.Countable) (α : Index.{u}) :
    ∃ β : Index.{u}, α.val < β.val ∧ s ⊆ stageSet β.val := by
  classical
  haveI : Countable s := hs.to_subtype
  have hex : ∀ x : s, ∃ γ < (ω₁ : Ordinal.{u}), x.val.val ∈ LStageZF γ := by
    intro x
    exact (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp x.val.property
  choose γ hγ hxγ using hex
  let β : Ordinal.{u} := max (Order.succ α.val) (⨆ x : s, γ x)
  have hβ : β < ω₁ := max_lt
    ((Cardinal.isSuccLimit_omega 1).succ_lt α.property)
    (Ordinal.iSup_lt_omega_one hγ)
  refine ⟨⟨β, hβ⟩, (Order.lt_succ α.val).trans_le (le_max_left _ _), ?_⟩
  intro x hx
  exact LStageZF_mono
    ((Ordinal.le_iSup γ ⟨x, hx⟩).trans (le_max_right _ _)) (hxγ ⟨x, hx⟩)

/-- One bounded step adjoins all formula witnesses for the smaller L stage. -/
theorem exists_hull_bound (M : Auxiliary.Interpretation Ambient.{u}) (α : Index.{u}) :
    ∃ β : Index.{u}, α.val < β.val ∧
      (Auxiliary.skolemHull M (stageSet α.val) : Set Ambient.{u}) ⊆ stageSet β.val :=
  exists_stage_bound _ (Auxiliary.countable_skolemHull M (countable_stageSet α.property)) α

end OneYTruth.InitialStage
