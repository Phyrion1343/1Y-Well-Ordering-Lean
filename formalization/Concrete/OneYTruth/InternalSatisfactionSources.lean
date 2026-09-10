import OneYTruth.InternalSatisfaction
import OneYTruth.InternalDiagram

/-! Full local satisfaction from the complete syntax, assignment, and atomic source sets. -/

namespace OneYTruth

open Constructible Constructible.FiniteSequenceZF InternalClosure InternalNodes
open SyntaxDiagram BoundedEvaluation InternalDiagram

universe u v w

theorem satisfactionSet_mem_of_internal_sources {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hOmega : Ordinal.omega0.toZFSet ∈ V)
    (hempty : (∅ : ZFSet.{u}) ∈ V) (hfive : (natCode 5 : ZFSet.{u}) ∈ V)
    (hsix : (natCode 6 : ZFSet.{u}) ∈ V) (hU : U ∈ V)
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (hSyntax : syntaxCodes (k := k) indexCode ∈ V) (hAssignments : assignmentCodes U ∈ V)
    (M : Interpretation k I (ZFCarrier U)) (hAtoms : trueAtomSet indexCode M ∈ V) :
    satisfactionSet indexCode M ∈ V :=
  satisfactionSet_mem_of_diagram hV N hmem (hSep 7 (mixedStepFormula K J))
    (hSep 8 (eventualFormula K J)) hpair hUnion hOmega hi M
    (diagram_parameters_mem hV N hmem hCol hSep hpair hUnion hfive hsix hU
      indexCode hSyntax hAssignments M hAtoms hempty)

theorem satisfactionSet_mem_LStageZF_of_internal_sources
    {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I] {U : ZFSet.{u}}
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (N : Interpretation K J (ZFCarrier (LStageZF θ)))
    (hmem : N.mem = Constructible.zfCarrierMem (LStageZF θ))
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hOmega : Ordinal.omega0.toZFSet ∈ LStageZF θ) (hU : U ∈ LStageZF θ)
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (hSyntax : syntaxCodes (k := k) indexCode ∈ LStageZF θ)
    (hAssignments : assignmentCodes U ∈ LStageZF θ)
    (M : Interpretation k I (ZFCarrier U)) (hAtoms : trueAtomSet indexCode M ∈ LStageZF θ) :
    satisfactionSet indexCode M ∈ LStageZF θ := by
  apply satisfactionSet_mem_of_internal_sources (LStageZF_isTransitive θ) N hmem hCol hSep
    (fun _ ha _ hb => orderedPair_mem_LStageZF_of_isSuccLimit hθ ha hb)
    (fun _ ha => sUnion_mem_LStageZF_of_isSuccLimit hθ ha) hOmega
    ?_ (natCode_mem_LStageZF_of_isSuccLimit hθ 5)
    (natCode_mem_LStageZF_of_isSuccLimit hθ 6) hU hi hSyntax hAssignments M hAtoms
  simpa [natCode] using (natCode_mem_LStageZF_of_isSuccLimit hθ 0 :
    (natCode 0 : ZFSet.{u}) ∈ LStageZF θ)

end OneYTruth
