import OneYTruth.SigmaSyntaxGrammar

/-! # The complete genuine Sigma-one code and comparison-node sets belong to L -/

namespace OneYTruth.SigmaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.Model Constructible.IndexedSequenceZF
open FormulaCode ConstructibleBoundedIteration ConstructibleCodeUniverse SigmaComparison

universe u v

noncomputable def params (B : LCarrier.{u}) : Tuple LCarrier.{u} 8 :=
  ![B, omegaLCarrier, emptyLCarrier,
    ⟨FiniteSequenceZF.sequenceCode [natCode 0], FiniteSequenceZF.sequenceCode_mem_L (by
      intro z hz
      have hz' : z = natCode 0 := by simpa using hz
      subst z
      exact natCode_mem_L 0)⟩,
    natLCarrier 5, natLCarrier 6, natLCarrier 2, natLCarrier 3]

noncomputable def stages (B D : LCarrier.{u}) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (filterStep ruleFormula 0 (params B)) D

theorem mem_stages_succ_iff (B D : LCarrier.{u}) (m : Nat) (p : ZFSet.{u}) :
    p ∈ (stages B D (m+1)).val ↔ p ∈ B.val ∧
      (p ∈ (stages B D m).val ∨ ∃ n ∈ Ordinal.omega0.toZFSet, ∃ f ∈ B.val,
        p = ZFSet.pair n f ∧ exRule B.val Ordinal.omega0.toZFSet (stages B D m).val n f) := by
  change p ∈ deltaSep ruleFormula (snoc (fun i => (params B i).val) (stages B D m).val) B.val ↔ _
  rw [deltaSep, ZFSet.mem_sep]
  have ht : snoc (snoc (fun i => (params B i).val) (stages B D m).val) p =
      parameters B.val Ordinal.omega0.toZFSet (stages B D m).val p := by
    simp only [constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  rw [ht, satisfies_ruleFormula]

noncomputable def grammarFamily (B D : LCarrier.{u}) : ParametricUniformOmegaFamilySpec.{u} 9 :=
  family ruleFormula 0 (params B) D

noncomputable def allStages (B D : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion (grammarFamily B D)

theorem mem_allStages_iff (B D : LCarrier.{u}) (p : ZFSet.{u}) :
    p ∈ (allStages B D).val ↔ ∃ m, p ∈ (stages B D m).val := by
  constructor
  · intro hp
    exact (mem_parametricUniformOmegaUnion_iff (grammarFamily B D)
      ⟨p, mem_L_of_mem hp (allStages B D).property⟩).mp hp
  · rintro ⟨m, hm⟩
    exact (mem_parametricUniformOmegaUnion_iff (grammarFamily B D)
      ⟨p, mem_L_of_mem hm (stages B D m).property⟩).mpr ⟨m, hm⟩

theorem scoped_of_sigmaPacked {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    {n : Nat} {f : ZFSet.{u}}
    (h : ∃ p : SigmaPacked k I, packedCode indexCode p.val = ZFSet.pair (natCode n) f) :
    ∃ φ : (language k I).BoundedFormula Empty n, IsSigmaOne φ ∧ formulaCode indexCode φ = f := by
  obtain ⟨⟨⟨m, φ⟩, hφ⟩, he⟩ := h
  obtain ⟨hn, hf⟩ := ZFSet.pair_inj.mp he
  have hmn : m = n := natCode_injective hn
  subst m
  exact ⟨φ, hφ, hf⟩

theorem stages_sound {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (B D : LCarrier.{u})
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode) (m : Nat) :
    ∀ p ∈ (stages B D m).val, ∃ φ : SigmaPacked k I, packedCode indexCode φ.val = p := by
  induction m with
  | zero =>
      intro p hp
      change p ∈ D.val at hp
      rw [hD] at hp
      obtain ⟨⟨φ, hδ⟩, he⟩ := ZFSet.mem_range.mp hp
      exact ⟨⟨φ, .deltaZero hδ⟩, he⟩
  | succ m ih =>
      intro p hp
      obtain ⟨_, hp⟩ := (mem_stages_succ_iff B D m p).mp hp
      rcases hp with hp | ⟨n, hn, f, _, hpf, g, _, j, _, a, _, b, _, hj, ha, hb, hf, hg⟩
      · exact ih p hp
      · obtain ⟨n, rfl⟩ := (mem_omega_iff_exists_natCode n).mp hn
        have hj' : j = natCode (n+1) := hj.trans (natCode_succ_eq_insert n).symm
        rw [hj'] at hg
        obtain ⟨φ, hSigma, hφ⟩ := scoped_of_sigmaPacked (ih _ hg)
        refine ⟨⟨⟨n, φ.ex⟩, .ex hSigma⟩, ?_⟩
        have hcode : formulaCode indexCode φ.ex = f := by
          rw [formulaCode_ex, hφ, ← ha, ← hb]
          exact hf.symm
        exact (congrArg (ZFSet.pair (natCode n)) hcode).trans hpf.symm

theorem stages_complete {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A D : LCarrier.{u})
    (hA : ∀ i, indexCode i ∈ A.val)
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode)
    {n : Nat} (φ : (language k I).BoundedFormula Empty n) (hSigma : IsSigmaOne φ) :
    ∃ m, packedCode indexCode ⟨n, φ⟩ ∈ (stages (codeUniverse A) D m).val := by
  induction hSigma with
  | deltaZero hδ =>
      refine ⟨0, ?_⟩
      change packedCode indexCode _ ∈ D.val
      rw [hD]
      exact ZFSet.mem_range_self (f := fun ψ : DeltaSyntaxGrammar.DeltaPacked k I => packedCode indexCode ψ.val)
        ⟨_, hδ⟩
  | @ex n φ hSigma ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨m+1, (mem_stages_succ_iff (codeUniverse A) D m _).mpr ?_⟩
      refine ⟨pair_mem (natCode_mem A n) (rawCode_mem hA (toRaw φ.ex)), Or.inr ?_⟩
      refine ⟨natCode n, (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩,
        formulaCode indexCode φ.ex, rawCode_mem hA (toRaw φ.ex), rfl, ?_⟩
      let a := FiniteSequenceZF.sequenceCode [natCode 5, formulaCode indexCode φ, FiniteSequenceZF.sequenceCode [natCode 0] ]
      let b := FiniteSequenceZF.sequenceCode [natCode 6, a]
      have ha : a ∈ (codeUniverse A).val := rawCode_mem hA (Raw.imp (toRaw φ) Raw.falsum)
      have hb : b ∈ (codeUniverse A).val := rawCode_mem hA (Raw.all (Raw.imp (toRaw φ) Raw.falsum))
      exact ⟨formulaCode indexCode φ, rawCode_mem hA (toRaw φ), natCode (n+1),
        (mem_omega_iff_exists_natCode _).mpr ⟨n+1, rfl⟩, a, ha, b, hb,
        natCode_succ_eq_insert n, rfl, rfl, formulaCode_ex indexCode φ, hm⟩

theorem allStages_eq_sigmaCodes {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A D : LCarrier.{u})
    (hA : A.val = ZFSet.range indexCode)
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode) :
    (allStages (codeUniverse A) D).val = sigmaCodes (k := k) indexCode := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := (mem_allStages_iff (codeUniverse A) D p).mp hp
    exact ZFSet.mem_range.mpr (stages_sound (codeUniverse A) D hD m p hm)
  · intro hp
    obtain ⟨⟨⟨n, φ⟩, hSigma⟩, rfl⟩ := ZFSet.mem_range.mp hp
    exact (mem_allStages_iff (codeUniverse A) D _).mpr
      (stages_complete A D (fun i => hA ▸ ZFSet.mem_range_self i) hD φ hSigma)

theorem sigmaCodes_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (hA : ZFSet.range indexCode ∈ L) :
    sigmaCodes (k := k) indexCode ∈ L := by
  let A : LCarrier.{u} := ⟨ZFSet.range indexCode, hA⟩
  let D : LCarrier.{u} := ⟨DeltaSyntaxGrammar.deltaCodes (k := k) indexCode,
    DeltaSyntaxGrammar.deltaCodes_mem_L hA⟩
  rw [← allStages_eq_sigmaCodes (k := k) A D rfl rfl]
  exact (allStages (codeUniverse A) D).property

theorem sigmaNodes_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} {U : ZFSet.{u}}
    (hA : ZFSet.range indexCode ∈ L) (hU : U ∈ L) :
    sigmaNodes (k := k) indexCode U ∈ L :=
  sigmaNodes_mem_L_of_sigmaCodes (sigmaCodes_mem_L hA) hU

end OneYTruth.SigmaSyntaxGrammar

#print axioms OneYTruth.SigmaSyntaxGrammar.sigmaCodes_mem_L
#print axioms OneYTruth.SigmaSyntaxGrammar.sigmaNodes_mem_L
