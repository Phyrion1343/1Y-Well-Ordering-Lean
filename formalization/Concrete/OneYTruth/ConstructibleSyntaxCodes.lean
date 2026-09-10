import OneYTruth.ConstructibleSyntaxStages

/-!
# The complete mixed-language syntax-code set is constructible

Completeness is proved by the actual formula depth; soundness was proved
directly for all literal grammar rules. Together these identify the entire
internally collected omega union with the specified Mathlib formula codes.
-/

namespace OneYTruth.ConstructibleSyntaxStages

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF
open Constructible.Model Constructible.IndexedSequenceZF
open FormulaCode SyntaxGrammar SyntaxDiagram InternalNodes ConstructibleCodeUniverse

universe u v

theorem stages_complete {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B A : LCarrier.{u})
    (hA : ∀ i, indexCode i ∈ A.val)
    (hraw : ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), formulaCode indexCode φ ∈ B.val)
    (hpacked : ∀ φ : Packed k I, packedCode indexCode φ ∈ B.val) (m : Nat) :
    ∀ {n : Nat} (φ : (language k I).BoundedFormula Empty n), formulaDepth φ < m →
      packedCode indexCode ⟨n, φ⟩ ∈ (stages B A k m).val := by
  induction m with
  | zero => intro n φ hφ; omega
  | succ m ih =>
    intro n φ hφ
    apply (mem_stages_succ_iff B A k m _).mpr
    refine ⟨hpacked ⟨n, φ⟩, natCode n,
      (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩,
      formulaCode indexCode φ, hraw n φ, rfl, ?_⟩
    cases φ with
    | falsum => exact Or.inl rfl
    | equal t s =>
      right; left
      exact ⟨natCode (termIndex t).val,
        (natCode_mem_natCode_iff _ _).mpr (termIndex t).isLt,
        natCode (termIndex s).val,
        (natCode_mem_natCode_iff _ _).mpr (termIndex s).isLt, rfl⟩
    | rel r ts =>
      cases r with
      | mem =>
        right; right; left
        exact ⟨natCode (termIndex (ts 0)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
          natCode (termIndex (ts 1)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt, rfl⟩
      | diagonal j =>
        right; right; right; left
        exact ⟨natCode j.val, (natCode_mem_natCode_iff _ _).mpr j.isLt,
          natCode (termIndex (ts 0)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
          natCode (termIndex (ts 1)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt,
          natCode (termIndex (ts 2)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 2)).isLt, rfl⟩
      | named i =>
        right; right; right; right; left
        exact ⟨indexCode i, hA i, natCode (termIndex (ts 0)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
          natCode (termIndex (ts 1)).val,
          (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt, rfl⟩
    | imp φ ψ =>
      right; right; right; right; right; left
      refine ⟨formulaCode indexCode φ, hraw n φ, formulaCode indexCode ψ, hraw n ψ,
        rfl, ih φ ?_, ih ψ ?_⟩ <;> simp only [formulaDepth] at hφ <;> omega
    | all φ =>
      right; right; right; right; right; right
      refine ⟨formulaCode indexCode φ, hraw (n + 1) φ, natCode (n + 1),
        (mem_omega_iff_exists_natCode _).mpr ⟨n + 1, rfl⟩,
        natCode_succ_eq_insert n, rfl, ih φ ?_⟩
      simp only [formulaDepth] at hφ
      omega

theorem allStages_eq_syntaxCodes {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) :
    (allStages (codeUniverse A) A k).val = syntaxCodes (k := k) indexCode := by
  have hi : ∀ i, indexCode i ∈ A.val := fun i => hA ▸ ZFSet.mem_range_self i
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := (mem_allStages_iff (codeUniverse A) A k p).mp hp
    exact ZFSet.mem_range.mpr (stages_sound (codeUniverse A) A hA m p hm)
  · intro hp
    obtain ⟨⟨n, φ⟩, rfl⟩ := ZFSet.mem_range.mp hp
    apply (mem_allStages_iff (codeUniverse A) A k _).mpr
    refine ⟨formulaDepth φ + 1, stages_complete (codeUniverse A) A hi
      (fun _ ψ => rawCode_mem hi (toRaw ψ))
      (fun ψ => pair_mem (natCode_mem A ψ.1) (rawCode_mem hi (toRaw ψ.2)))
      (formulaDepth φ + 1) φ (Nat.lt_succ_self _)⟩

theorem syntaxCodes_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (hA : ZFSet.range indexCode ∈ L) :
    syntaxCodes (k := k) indexCode ∈ L := by
  let A : LCarrier.{u} := ⟨ZFSet.range indexCode, hA⟩
  rw [← allStages_eq_syntaxCodes (k := k) A rfl]
  exact (allStages (codeUniverse A) A k).property

end OneYTruth.ConstructibleSyntaxStages
