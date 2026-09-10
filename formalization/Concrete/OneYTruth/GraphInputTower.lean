import OneYTruth.StageRecursionL

/-! # The actual truth operator with a set graph as input

The graph-input operator is total even on malformed graphs. On the real
predecessor graph it is exactly the operator used by `ExternalTower.truth`.
This is the precise operator to which a uniform one-step formula must refer.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model FormulaCode

universe u

/-- Existential lookup in an arbitrary graph, followed by membership in the
displayed truth set. No uniqueness is assumed for malformed input graphs. -/
def graphTruth (q key entry : ZFSet.{u}) : Prop :=
  ∃ T : ZFSet.{u}, ZFSet.pair key T ∈ q ∧ entry ∈ T

theorem graphTruth_restrictionGraph {d key entry : ZFSet.{u}}
    (F : ZFSet.{u} → ZFSet.{u}) (hk : key ∈ d) :
    graphTruth (predecessorRestrictionGraph d F) key entry ↔ entry ∈ F key := by
  simp only [graphTruth, pair_mem_restrictionGraph_iff]
  constructor
  · rintro ⟨T, ⟨_, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨F key, ⟨hk, rfl⟩, h⟩

/-- The interpretation obtained by literal lookup in the input graph. -/
noncomputable def graphInterpretation {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (q : ZFSet.{u}) :
    Interpretation s.1 {ξ : Ordinal.{u} // ξ < s.2.val} (ZFCarrier U) where
  mem a b := a.val ∈ b.val
  named ξ e a := graphTruth q
    (stageCode (s.1, ⟨ξ.val, le_trans ξ.property.le s.2.property⟩)) (ZFSet.pair e.val a.val)
  diagonal j ξCode e a := ∃ ξ : {ξ : Ordinal.{u} // ξ < κ},
    ξCode.val = ξ.val.toZFSet ∧ graphTruth q
      (stageCode (j.val, ⟨ξ.val, ξ.property.le⟩)) (ZFSet.pair e.val a.val)

theorem graphInterpretation_restrictionGraph {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (F : ZFSet.{u} → ZFSet.{u}) :
    graphInterpretation U s (predecessorRestrictionGraph
      (stagePredecessors κ (stageCode s)) F) =
      stageInterpretation U s (fun t _ => F (stageCode t)) := by
  unfold graphInterpretation stageInterpretation
  congr 1
  · funext j ξCode e a
    apply propext
    apply exists_congr
    intro ξ
    apply and_congr_right
    intro _
    apply graphTruth_restrictionGraph
    apply mem_stagePredecessors.mpr
    exact (codedEarlier_codes _ _).mpr (Prod.Lex.left _ _ j.isLt)
  · funext ξ e a
    apply propext
    apply graphTruth_restrictionGraph
    apply mem_stagePredecessors.mpr
    exact (codedEarlier_codes _ _).mpr (Prod.Lex.right _ ξ.property)

/-- Satisfaction after reading a predecessor graph at a typed stage. -/
noncomputable def graphStageStep {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (q : ZFSet.{u}) : ZFSet.{u} :=
  satisfactionSet ordinalIndexCode (graphInterpretation U s q)

/-- Total operator on a coded stage and a set-sized predecessor graph. -/
noncomputable def graphInputStep (κ : Ordinal.{u}) (U z q : ZFSet.{u}) : ZFSet.{u} :=
  graphStageStep U (decodeStage κ z) q

/-- The already constructed external truth family, expressed on raw stage codes. -/
noncomputable def codedTruth (κ : Ordinal.{u}) (U z : ZFSet.{u}) : ZFSet.{u} :=
  truth U (decodeStage κ z)

@[simp] theorem codedTruth_code {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :
    codedTruth κ U (stageCode s) = truth U s := by
  rw [codedTruth, decodeStage_code]

/-- The actual external truth values obey the graph-input recursion equation. -/
theorem codedTruth_graphInputStep {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :
    codedTruth κ U (stageCode s) = graphInputStep κ U (stageCode s)
      (predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) (codedTruth κ U)) := by
  rw [graphInputStep, decodeStage_code, graphStageStep, graphInterpretation_restrictionGraph]
  simp only [codedTruth_code]
  exact truth_eq_satisfactionSet U s

theorem graph_eq_restrictionGraph {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    @graph κ U = predecessorRestrictionGraph (stageSet κ) (codedTruth κ U) := by
  apply ZFSet.ext
  intro pair
  constructor
  · intro hp
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hp
    exact mem_predecessorRestrictionGraph_iff.mpr
      ⟨stageCode s, stageCode_mem_stageSet s, by simpa only [codedTruth_code] using hs⟩
  · intro hp
    obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_range.mpr ⟨s, by simpa only [codedTruth_code] using he⟩

/-- Conditional only on the explicit uniform one-step presentation. The
well-founded recursion, predecessor collection, and whole-graph Replacement
are already proved; they are not extra hypotheses of this theorem. -/
theorem graph_mem_L_of_stepPresentation {κ : Ordinal.{u}} (U : ZFSet.{u})
    (P : StageStepPresentation κ (graphInputStep κ U)) : @graph κ U ∈ L := by
  rw [graph_eq_restrictionGraph]
  exact P.stageGraph_mem_L (codedTruth κ U) (codedTruth_graphInputStep U)

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.codedTruth_graphInputStep
#print axioms OneYTruth.ExternalTower.graph_mem_L_of_stepPresentation
