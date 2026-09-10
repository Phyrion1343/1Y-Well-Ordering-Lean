import OneYTruth.UniformFromGraph
import OneYTruth.GraphStepCorrect
import OneYTruth.InitialCanonicalSupply

/-! # Constructibility of the actual complete bounded truth tower

The one-step formula is the actual fixed formula with its constructed
canonical witnesses. The whole graph is then obtained by the proved
well-founded L-recursion theorem. No semantic presentation remains an input.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

theorem graph_mem_L (κ : Ordinal.{u}) {U : ZFSet.{u}} (hU : U ∈ L) : @graph κ U ∈ L := by
  let UL : LCarrier.{u} := ⟨U, hU⟩
  apply graph_mem_L_of_stepFormula hU (GraphStepMatrix.fixedParameters κ UL) GraphStepMatrix.formula
  intro x q v hx
  obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hx
  have h := GraphStepMatrix.formula_correct κ s.2.val s.2.property s.1 UL x q v hs.symm
  apply h.trans
  rw [← hs, graphInputStep_code_eq_predecessorStep]

theorem uniformSet_mem_L (κ : Ordinal.{u}) {U : ZFSet.{u}} (hU : U ∈ L) :
    @uniformSet κ U ∈ L :=
  uniformSet_mem_L_of_graph U (graph_mem_L κ hU)

end OneYTruth.ExternalTower

namespace OneYTruth.RootSemantics

open Constructible
open scoped Ordinal

universe u

/-- The former initial-representation semantic hypothesis is now a theorem
about the actual uniform truth set over the actual ambient Lω₁. -/
theorem ambientTruth_mem_L : ambientTruth.{u} ∈ L :=
  ExternalTower.uniformSet_mem_L (ω₁ : Ordinal.{u}) (LStageZF_mem_L _)

end OneYTruth.RootSemantics

#print axioms OneYTruth.ExternalTower.graph_mem_L
#print axioms OneYTruth.RootSemantics.ambientTruth_mem_L
