import OneYTruth.SyntaxGrammarSoundness
import OneYTruth.ConstructibleBoundedIteration

/-! The whole omega family of the actual scoped grammar exists in L. -/

namespace OneYTruth.ConstructibleSyntaxStages

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.IndexedSequenceZF FormulaCode SyntaxGrammar
open ConstructibleBoundedIteration

universe u v

noncomputable def params (B A : LCarrier.{u}) (k : Nat) : Tuple LCarrier.{u} 11 :=
  ![B, A, omegaLCarrier, natLCarrier k, emptyLCarrier,
    natLCarrier 1, natLCarrier 2, natLCarrier 3, natLCarrier 4, natLCarrier 5, natLCarrier 6]

noncomputable def stages (B A : LCarrier.{u}) (k : Nat) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (filterStep ruleFormula 0 (params B A k)) emptyLCarrier

theorem mem_stages_succ_iff (B A : LCarrier.{u}) (k m : Nat) (p : ZFSet.{u}) :
    p ∈ (stages B A k (m + 1)).val ↔ p ∈ B.val ∧
      ∃ n ∈ Ordinal.omega0.toZFSet, ∃ f ∈ B.val,
        p = ZFSet.pair n f ∧
          RawRule B.val A.val Ordinal.omega0.toZFSet (natCode k) (stages B A k m).val n f := by
  change p ∈ deltaSep ruleFormula
    (snoc (fun i => (params B A k i).val) (stages B A k m).val) B.val ↔ _
  rw [deltaSep, ZFSet.mem_sep]
  have hparams : snoc (snoc (fun i => (params B A k i).val) (stages B A k m).val) p =
      parameters B.val A.val Ordinal.omega0.toZFSet (natCode k) (stages B A k m).val p := by
    rw [constructible_snoc_eq, constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  rw [hparams, satisfies_ruleFormula]

noncomputable def grammarFamily (B A : LCarrier.{u}) (k : Nat) :
    ParametricUniformOmegaFamilySpec.{u} 12 :=
  family ruleFormula 0 (params B A k) emptyLCarrier

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
    {indexCode : I → ZFSet.{u}} (B A : LCarrier.{u})
    (hA : A.val = ZFSet.range indexCode) (m : Nat) :
    ∀ p ∈ (stages B A k m).val, ∃ φ : Packed k I, packedCode indexCode φ = p := by
  induction m with
  | zero => intro p hp; exact (ZFSet.notMem_empty p hp).elim
  | succ m ih =>
    intro p hp
    obtain ⟨_, n, hn, f, _, hpf, hf⟩ := (mem_stages_succ_iff B A k m p).mp hp
    obtain ⟨n, rfl⟩ := (mem_omega_iff_exists_natCode n).mp hn
    obtain ⟨φ, hφ⟩ := rawRule_sound hA
      (fun n g hg => scoped_of_packed (ih _ hg)) n hf
    exact ⟨⟨n, φ⟩, (congrArg (ZFSet.pair (natCode n)) hφ).trans hpf.symm⟩

end OneYTruth.ConstructibleSyntaxStages
