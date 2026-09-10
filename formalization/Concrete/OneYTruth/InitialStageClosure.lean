import OneYTruth.InitialStageBounds

/-!
# Actual elementary L stages for the auxiliary language

Starting above any countable ordinal, alternate inclusion of an entire
constructible stage with its countable auxiliary Skolem hull. The supremum
of the resulting strictly increasing omega sequence is still below the
external omega_1. Its L stage satisfies the Tarski--Vaught criterion.

This proves the initial elementarity supply. It does not yet prove that the
expanded stages satisfy ZF minus Power Set, or that the chosen W belongs to L.
-/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Cardinal Ordinal

universe u

variable (M : Auxiliary.Interpretation Ambient.{u})

noncomputable def nextStage (α : Index.{u}) : Index.{u} :=
  Classical.choose (exists_hull_bound M α)

theorem lt_nextStage (α : Index.{u}) : α.val < (nextStage M α).val :=
  (Classical.choose_spec (exists_hull_bound M α)).1

theorem hull_subset_nextStage (α : Index.{u}) :
    (Auxiliary.skolemHull M (stageSet α.val) : Set Ambient.{u}) ⊆
      stageSet (nextStage M α).val :=
  (Classical.choose_spec (exists_hull_bound M α)).2

noncomputable def stageIter (α : Index.{u}) : Nat → Index.{u}
  | 0 => α
  | n + 1 => nextStage M (stageIter α n)

theorem stageIter_strictMono (α : Index.{u}) :
    StrictMono (fun n => (stageIter M α n).val) :=
  strictMono_nat_of_lt_succ (fun n => lt_nextStage M (stageIter M α n))

noncomputable def limitStage (α : Index.{u}) : Ordinal.{u} :=
  ⨆ n : Nat, (stageIter M α n).val

theorem limitStage_lt_omega_one (α : Index.{u}) : limitStage M α < ω₁ :=
  Ordinal.iSup_lt_omega_one (fun n => (stageIter M α n).property)

theorem stageIter_lt_limitStage (α : Index.{u}) (n : Nat) :
    (stageIter M α n).val < limitStage M α :=
  (lt_nextStage M (stageIter M α n)).trans_le
    (Ordinal.le_iSup (fun m => (stageIter M α m).val) (n + 1))

theorem lt_limitStage (α : Index.{u}) : α.val < limitStage M α :=
  stageIter_lt_limitStage M α 0

theorem limitStage_isSuccLimit (α : Index.{u}) : Order.IsSuccLimit (limitStage M α) := by
  apply Ordinal.isSuccLimit_iff.mpr
  refine ⟨(lt_of_le_of_lt (show 0 ≤ α.val from zero_le) (lt_limitStage M α)).ne', ?_⟩
  apply Order.isSuccPrelimit_of_succ_lt
  intro γ hγ
  exact Ordinal.succ_lt_iSup_of_ne_iSup
    (fun n => (stageIter_lt_limitStage M α n).ne) hγ

theorem mem_limitStage_iff (α : Index.{u}) (x : Ambient.{u}) :
    x ∈ stageSet (limitStage M α) ↔ ∃ n, x ∈ stageSet (stageIter M α n).val := by
  constructor
  · intro hx
    obtain ⟨γ, hγ, hxγ⟩ := (mem_LStageZF_limit_iff (limitStage_isSuccLimit M α)).mp hx
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hγ
    exact ⟨n, LStageZF_mono hn.le hxγ⟩
  · rintro ⟨n, hn⟩
    exact LStageZF_mono (stageIter_lt_limitStage M α n).le hn

/-- The induced auxiliary structure on exactly the prescribed L stage. -/
def stageSubstructure (β : Ordinal.{u}) :
    @Auxiliary.language.Substructure Ambient.{u} M.structure := by
  letI := M.structure
  exact { carrier := stageSet β, fun_mem := fun {_} e => nomatch e }

theorem limitStage_isElementary (α : Index.{u}) :
    letI := M.structure
    (stageSubstructure M (limitStage M α)).IsElementary := by
  classical
  letI := M.structure
  apply Substructure.isElementary_of_exists
  intro n φ xs a ha
  have hxs : ∀ i : Fin n, ∃ j : Nat,
      (xs i).val ∈ stageSet (stageIter M α j).val := by
    intro i
    exact (mem_limitStage_iff M α (xs i).val).mp (xs i).property
  choose j hj using hxs
  let N : Nat := Finset.univ.sup j
  have hxsN : ∀ i : Fin n, (xs i).val ∈ stageSet (stageIter M α N).val := by
    intro i
    apply stageSet_mono ((stageIter_strictMono M α).monotone
      (Finset.le_sup (f := j) (Finset.mem_univ i))) (hj i)
  obtain ⟨b, hb, hφb⟩ := Auxiliary.witness_mem_skolemHull M φ
    (fun i => (xs i).val) hxsN a ha
  have hbNext := hull_subset_nextStage M (stageIter M α N) hb
  have hbLimit : b ∈ stageSet (limitStage M α) :=
    (mem_limitStage_iff M α b).mpr ⟨N + 1, hbNext⟩
  exact ⟨⟨b, hbLimit⟩, hφb⟩

/-- Unboundedly many actual L stages are elementary in the one-W ambient structure. -/
theorem exists_elementary_LStage (α : Index.{u}) :
    letI := M.structure
    ∃ β : Ordinal.{u}, α.val < β ∧ β < ω₁ ∧ Order.IsSuccLimit β ∧
      (stageSubstructure M β).IsElementary :=
  ⟨limitStage M α, lt_limitStage M α, limitStage_lt_omega_one M α,
    limitStage_isSuccLimit M α, limitStage_isElementary M α⟩

end OneYTruth.InitialStage
