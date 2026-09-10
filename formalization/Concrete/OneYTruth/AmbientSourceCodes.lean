import OneYTruth.ConstructibleCodeUniverse
import OneYTruth.ConstructibleSubsetBound

/-!
# The actual complete assignment-code set is internal to the ambient stage

Countability bounds all its individual codes in a smaller stage. The already
proved constructibility of the *entire* set then permits the condensation
subset theorem to locate that set in L_(omega_1).
-/

namespace OneYTruth.InitialStage

open Constructible Constructible.FiniteSequenceZF InternalNodes
open ConstructibleAssignmentCodes
open scoped Cardinal Ordinal

universe u

theorem countable_of_mem_ambient {a : ZFSet.{u}}
    (ha : a ∈ LStageZF (ω₁ : Ordinal.{u})) : Countable (ZFCarrier a) := by
  obtain ⟨γ, hγκ, haγ⟩ := (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp ha
  haveI := countable_LStage hγκ
  apply Function.Injective.countable (f := fun x : ZFCarrier a =>
    (⟨x.val, (LStageZF_isTransitive γ).mem_trans x.property haγ⟩ : ZFCarrier (LStageZF γ)))
  intro x y h
  exact Subtype.ext (congrArg (fun z : ZFCarrier (LStageZF γ) => z.val) h)

/-- Countability gives a bound, while constructibility of the whole subset
is an independent and indispensable input. -/
theorem countable_constructible_subset_mem_ambient {s : ZFSet.{u}}
    [Countable (ZFCarrier s)] (hs : s ⊆ LStageZF (ω₁ : Ordinal.{u})) (hsL : s ∈ L) :
    s ∈ LStageZF (ω₁ : Ordinal.{u}) := by
  let t : Set Ambient.{u} := {x | x.val ∈ s}
  have ht : t.Countable := by
    apply Set.countable_coe_iff.mp
    apply Function.Injective.countable (f := fun x : t =>
      (⟨x.val.val, x.property⟩ : ZFCarrier s))
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ZFCarrier s => z.val) h))
  obtain ⟨β, _, hβ⟩ := exists_stage_bound t ht
    ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩
  have hsβ : s ⊆ LStageZF β.val := by
    intro p hp
    have hpT : (⟨p, hs hp⟩ : Ambient.{u}) ∈ t := hp
    exact hβ hpT
  have hLβ : LStageZF β.val ∈ LStageZF (ω₁ : Ordinal.{u}) :=
    LStageZF_mono (Order.succ_le_iff.mpr β.property) (LStageZF_mem_succ β.val)
  exact constructible_subset_mem_ambient hLβ hsβ hsL

theorem assignmentCodes_mem_ambient {U : ZFSet.{u}}
    (hU : U ∈ LStageZF (ω₁ : Ordinal.{u})) :
    assignmentCodes U ∈ LStageZF (ω₁ : Ordinal.{u}) := by
  haveI := countable_of_mem_ambient hU
  haveI : Countable (ZFCarrier (assignmentCodes U)) :=
    CountableSetHull.countable_range (fun a : PackedAssignment U => assignmentCode a.2)
  apply countable_constructible_subset_mem_ambient
  · intro p hp
    obtain ⟨⟨n, v⟩, rfl⟩ := ZFSet.mem_range.mp hp
    apply assignmentCode_mem_LStageZF (Cardinal.isSuccLimit_omega 1)
    exact fun x hx => (LStageZF_isTransitive _).mem_trans hx hU
  · exact assignmentCodes_mem_L (mem_L_of_mem hU (LStageZF_mem_L _))

end OneYTruth.InitialStage
