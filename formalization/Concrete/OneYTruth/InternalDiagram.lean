import OneYTruth.ChildrenCodeFormula
import OneYTruth.QuantifiedCodeFormula
import OneYTruth.EvaluationStep
import OneYTruth.ConstructibleCodes

/-!
# Five canonical diagram sets from the two complete source collections

Only ordinary expanded Collection and Separation and elementary pair/union
closure are assumed. The atomic truth table is kept separate: an arbitrary
external interpretation need not be amenable to the ambient model.
-/

namespace OneYTruth.InternalDiagram

open Constructible Constructible.FiniteSequenceZF InternalClosure InternalProducts
open InternalNodes SyntaxDiagram BoundedEvaluation

universe u v w

theorem structural_sets_mem {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (hfive : (natCode 5 : ZFSet.{u}) ∈ V) (hsix : (natCode 6 : ZFSet.{u}) ∈ V)
    (hU : U ∈ V) (indexCode : I → ZFSet.{u})
    (hSyntax : syntaxCodes (k := k) indexCode ∈ V) (hAssignments : assignmentCodes U ∈ V) :
    scopedPairs (k := k) U indexCode ∈ V ∧ atomSet (k := k) U indexCode ∈ V ∧
    implicationSet (k := k) U indexCode ∈ V ∧ quantifiedSet (k := k) U indexCode ∈ V ∧
    childrenSet (k := k) U indexCode ∈ V := by
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  have hRepPair := hRep 1 (pairFormula K J)
  have hRepSlice := hRep 1 (mixedSliceGraphFormula K J)
  have hnodes := scopedPairs_mem_of_internal_sources hV N hmem hRepPair hRepSlice
    (hSep 0 (mixedMatchingArityFormula K J)) hpair hUnion indexCode hSyntax hAssignments
  exact ⟨hnodes,
    AtomicCodeFormula.atomSet_mem_of_separation hV N hmem
      (hSep 1 (AtomicCodeFormula.mixedAtomicFormula K J)) hfive indexCode hnodes,
    ImplicationCodeFormula.implicationSet_mem_of_separation hV N hmem hRepPair hRepSlice
      (hSep 1 (ImplicationCodeFormula.mixedImplicationFormula K J))
      hpair hUnion hfive indexCode hnodes,
    QuantifiedCodeFormula.quantifiedSet_mem_of_separation hV N hmem
      (hSep 1 (QuantifiedCodeFormula.mixedQuantifiedFormula K J)) hsix indexCode hnodes,
    ChildrenCodeFormula.childrenSet_mem_of_separation hV N hmem hRepPair hRepSlice
      (hSep 2 (ChildrenCodeFormula.mixedChildrenFormula K J))
      hpair hUnion hsix hU indexCode hnodes⟩

/-- Specialization to a specified limit constructible level; no full ZF model hypothesis. -/
theorem structural_sets_mem_LStageZF {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U : ZFSet.{u}} {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (N : Interpretation K J (ZFCarrier (LStageZF θ)))
    (hmem : N.mem = Constructible.zfCarrierMem (LStageZF θ))
    (hCol : HasCollection N) (hSep : HasSeparation N) (hU : U ∈ LStageZF θ)
    (indexCode : I → ZFSet.{u}) (hSyntax : syntaxCodes (k := k) indexCode ∈ LStageZF θ)
    (hAssignments : assignmentCodes U ∈ LStageZF θ) :
    scopedPairs (k := k) U indexCode ∈ LStageZF θ ∧ atomSet (k := k) U indexCode ∈ LStageZF θ ∧
    implicationSet (k := k) U indexCode ∈ LStageZF θ ∧ quantifiedSet (k := k) U indexCode ∈ LStageZF θ ∧
    childrenSet (k := k) U indexCode ∈ LStageZF θ :=
  structural_sets_mem (LStageZF_isTransitive θ) N hmem hCol hSep
    (fun _ ha _ hb => orderedPair_mem_LStageZF_of_isSuccLimit hθ ha hb)
    (fun _ ha => sUnion_mem_LStageZF_of_isSuccLimit hθ ha)
    (natCode_mem_LStageZF_of_isSuccLimit hθ 5) (natCode_mem_LStageZF_of_isSuccLimit hθ 6)
    hU indexCode hSyntax hAssignments

theorem diagram_parameters_mem {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {U V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (hfive : (natCode 5 : ZFSet.{u}) ∈ V) (hsix : (natCode 6 : ZFSet.{u}) ∈ V)
    (hU : U ∈ V) (indexCode : I → ZFSet.{u})
    (hSyntax : syntaxCodes (k := k) indexCode ∈ V) (hAssignments : assignmentCodes U ∈ V)
    (M : Interpretation k I (ZFCarrier U)) (hAtoms : trueAtomSet indexCode M ∈ V)
    {S : ZFSet.{u}} (hS : S ∈ V) : ∀ i, parameters (diagram indexCode M) S i ∈ V := by
  obtain ⟨hn, ha, hi, hq, hc⟩ := structural_sets_mem hV N hmem hCol hSep
    hpair hUnion hfive hsix hU indexCode hSyntax hAssignments
  intro i
  fin_cases i
  · exact hS
  · exact hn
  · exact ha
  · exact hAtoms
  · exact hi
  · exact hq
  · exact hc

end OneYTruth.InternalDiagram
