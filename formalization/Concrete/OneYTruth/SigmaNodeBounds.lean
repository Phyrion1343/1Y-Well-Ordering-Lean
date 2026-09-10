import OneYTruth.SigmaSyntaxCodes
import OneYTruth.ConstructibleSubsetBound
import OneYTruth.ConstructibleCodes

/-! # Genuine Sigma-one comparison nodes are internal to the ambient stage

The two inputs are the actual alphabet-code set and the assignment domain.
The complete node set is already proved constructible by syntax generation;
a common smaller limit stage bounds its finite codes. Condensation then
places the whole node set in the ambient stage.
-/

namespace OneYTruth.SigmaComparison

open Constructible FormulaCode
open scoped Cardinal Ordinal

universe u v

theorem ordinalIndexCode_range (η : Ordinal.{u}) :
    ZFSet.range (ordinalIndexCode (η := η)) = η.toZFSet := by
  apply ZFSet.ext
  intro p
  rw [ZFSet.mem_range, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨⟨ξ, hξ⟩, rfl⟩
    exact ⟨ξ, hξ, rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨⟨ξ, hξ⟩, rfl⟩

theorem sigmaNodes_subset_scopedPairs {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) :
    sigmaNodes (k := k) indexCode U ⊆ scopedPairs (k := k) U indexCode := by
  intro p hp
  obtain ⟨n, φ, _, xs, rfl⟩ := (mem_sigmaNodes_iff indexCode U p).mp hp
  exact SyntaxDiagram.nodeCode_mem_scopedPairs indexCode ⟨⟨n, φ⟩, xs⟩

theorem sigmaNodes_subset_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (hU : U ⊆ LStageZF θ) {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ LStageZF θ) :
    sigmaNodes (k := k) indexCode U ⊆ LStageZF θ :=
  fun _ hp => scopedPairs_subset_LStageZF hθ hU hi
    (sigmaNodes_subset_scopedPairs indexCode U hp)

theorem sigmaNodes_mem_ambient {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hA : ZFSet.range indexCode ∈ LStageZF (ω₁ : Ordinal.{u}))
    (hU : U ∈ LStageZF (ω₁ : Ordinal.{u})) :
    sigmaNodes (k := k) indexCode U ∈ LStageZF (ω₁ : Ordinal.{u}) := by
  obtain ⟨γ, hγκ, hAγ⟩ :=
    (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp hA
  obtain ⟨ε, hεκ, hUε⟩ :=
    (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp hU
  let θ : Ordinal.{u} := max γ ε + Ordinal.omega0
  have hθ : Order.IsSuccLimit θ :=
    Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hθκ : θ < (ω₁ : Ordinal.{u}) :=
    Ordinal.isPrincipal_add_omega 1 (max_lt hγκ hεκ) Ordinal.omega0_lt_omega_one
  have hγθ : γ ≤ θ := (le_max_left γ ε).trans le_self_add
  have hεθ : ε ≤ θ := (le_max_right γ ε).trans le_self_add
  have hiθ : ∀ i, indexCode i ∈ LStageZF θ := fun i => LStageZF_mono hγθ
    ((LStageZF_isTransitive γ).mem_trans (ZFSet.mem_range_self i) hAγ)
  have hUθ : U ⊆ LStageZF θ := fun _ hz => LStageZF_mono hεθ
    ((LStageZF_isTransitive ε).mem_trans hz hUε)
  apply InitialStage.constructible_subset_mem_ambient
    (LStageZF_mono (Order.succ_le_iff.mpr hθκ) (LStageZF_mem_succ θ))
    (sigmaNodes_subset_LStageZF hθ hUθ hiθ)
  exact SigmaSyntaxGrammar.sigmaNodes_mem_L
    (mem_L_of_mem hA (LStageZF_mem_L _)) (mem_L_of_mem hU (LStageZF_mem_L _))

theorem ordinal_sigmaNodes_mem_L (k : Nat) (η : Ordinal.{u})
    {U : ZFSet.{u}} (hU : U ∈ L) :
    sigmaNodes (k := k) (ordinalIndexCode (η := η)) U ∈ L := by
  apply SigmaSyntaxGrammar.sigmaNodes_mem_L _ hU
  rw [ordinalIndexCode_range]
  exact ordinal_toZFSet_mem_L η

theorem ordinal_sigmaNodes_mem_ambient (k : Nat) {η : Ordinal.{u}}
    (hη : η < (ω₁ : Ordinal.{u})) {U : ZFSet.{u}}
    (hU : U ∈ LStageZF (ω₁ : Ordinal.{u})) :
    sigmaNodes (k := k) (ordinalIndexCode (η := η)) U ∈ LStageZF (ω₁ : Ordinal.{u}) := by
  apply sigmaNodes_mem_ambient _ hU
  rw [ordinalIndexCode_range]
  exact ordinal_toZFSet_mem_LStageZF_of_lt hη

end OneYTruth.SigmaComparison

#print axioms OneYTruth.SigmaComparison.sigmaNodes_mem_ambient
#print axioms OneYTruth.SigmaComparison.ordinal_sigmaNodes_mem_ambient
