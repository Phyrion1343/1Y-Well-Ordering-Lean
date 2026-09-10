import OneYTruth.DeltaSyntaxSoundness

/-! # The actual cumulative Delta-zero grammar has an omega family in L -/

namespace OneYTruth.DeltaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.Model Constructible.IndexedSequenceZF
open FormulaCode ConstructibleBoundedIteration

universe u v

noncomputable def stages (B A : LCarrier.{u}) (k : Nat) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (filterStep ruleFormula 0 (ConstructibleSyntaxStages.params B A k)) emptyLCarrier

theorem mem_stages_succ_iff (B A : LCarrier.{u}) (k m : Nat) (p : ZFSet.{u}) :
    p ∈ (stages B A k (m+1)).val ↔ p ∈ B.val ∧
      (p ∈ (stages B A k m).val ∨
        ∃ n ∈ Ordinal.omega0.toZFSet, ∃ f ∈ B.val,
          p = ZFSet.pair n f ∧ RawRule B.val A.val Ordinal.omega0.toZFSet
            (natCode k) (stages B A k m).val n f) := by
  change p ∈ deltaSep ruleFormula
    (snoc (fun i => (ConstructibleSyntaxStages.params B A k i).val) (stages B A k m).val) B.val ↔ _
  rw [deltaSep, ZFSet.mem_sep]
  have hp : snoc (snoc (fun i => (ConstructibleSyntaxStages.params B A k i).val)
      (stages B A k m).val) p =
      SyntaxGrammar.parameters B.val A.val Ordinal.omega0.toZFSet (natCode k) (stages B A k m).val p := by
    simp only [constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  rw [hp, satisfies_ruleFormula]

theorem stages_subset_bound (B A : LCarrier.{u}) (k m : Nat) : (stages B A k m).val ⊆ B.val := by
  cases m with
  | zero => intro p hp; exact (ZFSet.notMem_empty p hp).elim
  | succ m => intro p hp; exact ((mem_stages_succ_iff B A k m p).mp hp).1

theorem stages_subset_succ (B A : LCarrier.{u}) (k m : Nat) :
    (stages B A k m).val ⊆ (stages B A k (m+1)).val := by
  intro p hp
  exact (mem_stages_succ_iff B A k m p).mpr ⟨stages_subset_bound B A k m hp, Or.inl hp⟩

theorem stages_mono (B A : LCarrier.{u}) (k : Nat) {m n : Nat} (h : m ≤ n) :
    (stages B A k m).val ⊆ (stages B A k n).val := by
  induction h with
  | refl => exact fun _ hp => hp
  | @step n h ih => exact fun _ hp => stages_subset_succ B A k n (ih hp)

noncomputable def grammarFamily (B A : LCarrier.{u}) (k : Nat) : ParametricUniformOmegaFamilySpec.{u} 12 :=
  family ruleFormula 0 (ConstructibleSyntaxStages.params B A k) emptyLCarrier

noncomputable def allStages (B A : LCarrier.{u}) (k : Nat) : LCarrier.{u} :=
  parametricUniformOmegaUnion (grammarFamily B A k)

theorem mem_allStages_iff (B A : LCarrier.{u}) (k : Nat) (p : ZFSet.{u}) :
    p ∈ (allStages B A k).val ↔ ∃ m, p ∈ (stages B A k m).val := by
  constructor
  · intro hp
    exact (mem_parametricUniformOmegaUnion_iff (grammarFamily B A k)
      ⟨p, mem_L_of_mem hp (allStages B A k).property⟩).mp hp
  · rintro ⟨m, hm⟩
    exact (mem_parametricUniformOmegaUnion_iff (grammarFamily B A k)
      ⟨p, mem_L_of_mem hm (stages B A k m).property⟩).mpr ⟨m, hm⟩

theorem stages_sound {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) (m : Nat) :
    ∀ p ∈ (stages B A k m).val, ∃ φ : DeltaPacked k I, packedCode indexCode φ.val = p := by
  induction m with
  | zero => intro p hp; exact (ZFSet.notMem_empty p hp).elim
  | succ m ih =>
      intro p hp
      obtain ⟨_, hp⟩ := (mem_stages_succ_iff B A k m p).mp hp
      rcases hp with hp | ⟨n, hn, f, _, hpf, hf⟩
      · exact ih p hp
      · obtain ⟨n, rfl⟩ := (mem_omega_iff_exists_natCode n).mp hn
        obtain ⟨φ, hδ, hφ⟩ := rawRule_sound hA
          (fun n g hg => scoped_of_packed (ih _ hg)) n hf
        exact ⟨⟨⟨n, φ⟩, hδ⟩, (congrArg (ZFSet.pair (natCode n)) hφ).trans hpf.symm⟩

end OneYTruth.DeltaSyntaxGrammar

#print axioms OneYTruth.DeltaSyntaxGrammar.stages_sound
#print axioms OneYTruth.DeltaSyntaxGrammar.mem_allStages_iff
