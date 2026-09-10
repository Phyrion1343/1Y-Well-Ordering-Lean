import OneYTruth.AtomicTruthCorrect

/-!
# Actual atomic truth and satisfaction from constructible predicate graphs

All syntax, assignment, lookup and structural-diagram sets are supplied by
their proved constructions. The only interpretation-dependent hypotheses
are the actual named and diagonal relation graphs.
-/

namespace OneYTruth.ConstructibleDiagramSources

open Constructible Constructible.FiniteSequenceZF Constructible.Model
open FormulaCode SyntaxDiagram AtomicRelationGraphs AtomicTruthFormula
open ConstructibleAssignmentCodes AssignmentLookup

universe u v

theorem atomic_parameters_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) (hU : U ∈ L)
    (hA : ZFSet.range indexCode ∈ L)
    (hN : namedGraph indexCode M ∈ L) (hD : diagonalGraph M ∈ L) :
    ∀ i, parameters indexCode M i ∈ L := by
  intro i
  fin_cases i
  · exact hU
  · exact lookupSet_mem_L hU
  · exact assignmentCodes_mem_L hU
  · exact ordinal_toZFSet_mem_L _
  · exact hA
  · exact hN
  · exact hD
  all_goals exact natCode_mem_L _

theorem trueAtomSet_mem_L_of_relation_graphs {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hmem : ∀ x y, M.mem x y ↔ x.val ∈ y.val)
    (hU : U ∈ L) (hA : ZFSet.range indexCode ∈ L)
    (hN : namedGraph indexCode M ∈ L) (hD : diagonalGraph M ∈ L) :
    trueAtomSet indexCode M ∈ L := by
  let ps : Tuple LCarrier.{u} 11 := fun i =>
    ⟨parameters indexCode M i, atomic_parameters_mem_L M hU hA hN hD i⟩
  apply filtered_range_mem_L AtomicTruthFormula.formula ps
    (fun z : AtomicAssignment (k := k) I U => nodeCode indexCode z.val)
    (fun z => OneYTruth.realize M z.val.1.2 Empty.elim z.val.2)
    (atomSet_mem_L (scopedPairs_mem_L hU hA))
  intro z
  exact satisfies_formula_atomic hi M hmem z.val.1.2 z.val.2 z.property

theorem satisfactionSet_mem_L_of_relation_graphs {k : Nat} {I : Type v} [Small.{u} I]
    {U : ZFSet.{u}} {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U))
    (hmem : ∀ x y, M.mem x y ↔ x.val ∈ y.val)
    (hU : U ∈ L) (hA : ZFSet.range indexCode ∈ L)
    (hN : namedGraph indexCode M ∈ L) (hD : diagonalGraph M ∈ L) :
    satisfactionSet indexCode M ∈ L :=
  satisfactionSet_mem_L_of_atomic_table hi M hU hA
    (trueAtomSet_mem_L_of_relation_graphs hi M hmem hU hA hN hD)

end OneYTruth.ConstructibleDiagramSources
