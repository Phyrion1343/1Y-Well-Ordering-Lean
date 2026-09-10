import OneYTruth.DeltaSyntaxStages

/-! # The complete genuine Delta-zero code set belongs to L -/

namespace OneYTruth.DeltaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF FormulaCode
open Constructible.Model Constructible.IndexedSequenceZF SyntaxDiagram ConstructibleCodeUniverse

universe u v

theorem stages_complete {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u})
    (hA : ∀ i, indexCode i ∈ A.val) (m : Nat) :
    ∀ {n : Nat} (φ : (language k I).BoundedFormula Empty n), IsDeltaZero φ →
      formulaDepth φ < m → packedCode indexCode ⟨n, φ⟩ ∈ (stages (codeUniverse A) A k m).val := by
  induction m with
  | zero => intro n φ hδ hφ; omega
  | succ m ih =>
      intro n φ hδ hφ
      apply (mem_stages_succ_iff (codeUniverse A) A k m _).mpr
      refine ⟨pair_mem (natCode_mem A n) (rawCode_mem hA (toRaw φ)), Or.inr ?_⟩
      refine ⟨natCode n, (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩,
        formulaCode indexCode φ, rawCode_mem hA (toRaw φ), rfl, ?_⟩
      cases hδ with
      | falsum => exact Or.inl rfl
      | equal t s =>
          right; left
          exact ⟨natCode (termIndex t).val, (natCode_mem_natCode_iff _ _).mpr (termIndex t).isLt,
            natCode (termIndex s).val, (natCode_mem_natCode_iff _ _).mpr (termIndex s).isLt, rfl⟩
      | rel r ts =>
          cases r with
          | mem =>
              right; right; left
              exact ⟨natCode (termIndex (ts 0)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
                natCode (termIndex (ts 1)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt, rfl⟩
          | diagonal j =>
              right; right; right; left
              exact ⟨natCode j.val, (natCode_mem_natCode_iff _ _).mpr j.isLt,
                natCode (termIndex (ts 0)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
                natCode (termIndex (ts 1)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt,
                natCode (termIndex (ts 2)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 2)).isLt, rfl⟩
          | named i =>
              right; right; right; right; left
              exact ⟨indexCode i, hA i, natCode (termIndex (ts 0)).val,
                (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 0)).isLt,
                natCode (termIndex (ts 1)).val, (natCode_mem_natCode_iff _ _).mpr (termIndex (ts 1)).isLt, rfl⟩
      | @imp n φ ψ hδφ hδψ =>
          right; right; right; right; right; left
          refine ⟨formulaCode indexCode φ, rawCode_mem hA (toRaw φ),
            formulaCode indexCode ψ, rawCode_mem hA (toRaw ψ), rfl,
            ih φ hδφ ?_, ih ψ hδψ ?_⟩ <;> simp only [formulaDepth] at hφ <;> omega
      | @boundedAll n t φ hδφ =>
          right; right; right; right; right; right
          let i := (termIndex t).val
          let atom := FiniteSequenceZF.sequenceCode [natCode 2, natCode n, natCode i]
          let impl := FiniteSequenceZF.sequenceCode [natCode 5, atom, formulaCode indexCode φ]
          have hAtom : atom ∈ (codeUniverse A).val := rawCode_mem hA (Raw.mem n i)
          have hImpl : impl ∈ (codeUniverse A).val := rawCode_mem hA (Raw.imp (Raw.mem n i) (toRaw φ))
          refine ⟨natCode i, (natCode_mem_natCode_iff _ _).mpr (termIndex t).isLt,
            formulaCode indexCode φ, rawCode_mem hA (toRaw φ), natCode (n+1),
            (mem_omega_iff_exists_natCode _).mpr ⟨n+1, rfl⟩, atom, hAtom, impl, hImpl,
            natCode_succ_eq_insert n, rfl, rfl, formulaCode_boundedAll indexCode t φ, ih φ hδφ ?_⟩
          simp only [OneYTruth.boundedAll, formulaDepth] at hφ
          omega

theorem allStages_eq_deltaCodes {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) :
    (allStages (codeUniverse A) A k).val = deltaCodes (k := k) indexCode := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := (mem_allStages_iff (codeUniverse A) A k p).mp hp
    exact ZFSet.mem_range.mpr (stages_sound (codeUniverse A) A hA m p hm)
  · intro hp
    obtain ⟨⟨⟨n, φ⟩, hδ⟩, rfl⟩ := ZFSet.mem_range.mp hp
    apply (mem_allStages_iff (codeUniverse A) A k _).mpr
    exact ⟨formulaDepth φ+1, stages_complete A (fun i => hA ▸ ZFSet.mem_range_self i)
      (formulaDepth φ+1) φ hδ (Nat.lt_succ_self _)⟩

theorem deltaCodes_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (hA : ZFSet.range indexCode ∈ L) :
    deltaCodes (k := k) indexCode ∈ L := by
  let A : LCarrier.{u} := ⟨ZFSet.range indexCode, hA⟩
  rw [← allStages_eq_deltaCodes (k := k) A rfl]
  exact (allStages (codeUniverse A) A k).property

end OneYTruth.DeltaSyntaxGrammar

#print axioms OneYTruth.DeltaSyntaxGrammar.deltaCodes_mem_L
