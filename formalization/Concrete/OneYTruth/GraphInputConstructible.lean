import OneYTruth.GraphInputTower
import OneYTruth.StageStepFormula
import OneYTruth.ConstructibleGraphInput
import OneYTruth.SigmaNodeBounds

/-! # Constructibility of the actual graph-input step

This connects the literal graph-query satisfaction construction to the
operator used in the real external tower recursion.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model FormulaCode

universe u

theorem graphInterpretation_eq_predecessorInterpretation {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (q : ZFSet.{u}) :
    graphInterpretation U s q =
      PredecessorGraph.interpretation s.1 U ordinalIndexCode κ.toZFSet q := by
  unfold graphInterpretation PredecessorGraph.interpretation
  congr 1
  funext j ξCode e a
  apply propext
  constructor
  · rintro ⟨ξ, hξ, h⟩
    refine ⟨?_, ?_⟩
    · rw [hξ]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ξ.property
    · rw [hξ]
      exact h
  · rintro ⟨hξ, h⟩
    obtain ⟨ξ, hξlt, he⟩ := Ordinal.mem_toZFSet_iff.mp hξ
    exact ⟨⟨ξ, hξlt⟩, he.symm, by
      simpa only [← he, graphTruth, stageCode, PredecessorGraph.Read] using h⟩

theorem graphInputStep_eq_predecessorStep (κ : Ordinal.{u}) (U z q : ZFSet.{u}) :
    graphInputStep κ U z q = PredecessorGraph.step (decodeStage κ z).1 U
      (ordinalIndexCode (η := (decodeStage κ z).2.val)) κ.toZFSet q := by
  unfold graphInputStep graphStageStep PredecessorGraph.step
  rw [graphInterpretation_eq_predecessorInterpretation]

theorem graphInputStep_code_eq_predecessorStep {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (q : ZFSet.{u}) :
    graphInputStep κ U (stageCode s) q = PredecessorGraph.step s.1 U
      (ordinalIndexCode (η := s.2.val)) κ.toZFSet q := by
  rw [graphInputStep, decodeStage_code, graphStageStep]
  rw [graphInterpretation_eq_predecessorInterpretation]
  rfl

/-- One-step constructibility is unconditional for constructible U and q;
in particular q need not already be a correct predecessor graph. -/
theorem graphInputStep_mem_L (κ : Ordinal.{u}) {U z q : ZFSet.{u}}
    (hU : U ∈ L) (hq : q ∈ L) : graphInputStep κ U z q ∈ L := by
  rw [graphInputStep_eq_predecessorStep]
  apply PredecessorGraph.step_mem_L ordinalIndexCode_injective hU
  · rw [SigmaComparison.ordinalIndexCode_range]
    exact ordinal_toZFSet_mem_L _
  · exact ordinal_toZFSet_mem_L _
  · exact hq

/-- The only remaining input is exactness of one fixed first-order formula
for the whole one-step output. Stage syntax, one-step closure, recursive
collection, and identification with the actual truth tower are all supplied. -/
theorem graph_mem_L_of_stepFormula {κ : Ordinal.{u}} {U : ZFSet.{u}}
    (hU : U ∈ L) {n : Nat} (params : Tuple LCarrier.{u} n) (φ : FOFormula (n + 3))
    (hφ : ∀ x q v : LCarrier.{u}, x.val ∈ stageSet κ →
      (FOFormula.Satisfies lCarrierMem φ (snoc (snoc (snoc params x) q) v) ↔
        v.val = graphInputStep κ U x.val q.val)) : @graph κ U ∈ L := by
  apply graph_mem_L_of_stepPresentation U
  exact stageStepPresentationOfFormula κ (graphInputStep κ U) params φ hφ
    (fun _ q _ => graphInputStep_mem_L κ hU q.property)

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.graphInputStep_mem_L
#print axioms OneYTruth.ExternalTower.graph_mem_L_of_stepFormula
