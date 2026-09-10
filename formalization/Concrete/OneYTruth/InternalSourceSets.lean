import OneYTruth.InternalSyntaxCodes
import OneYTruth.AssignmentGrammar

/-! # Genuine complete source sets at any adequate limit constructible stage

The endpoint theorem assumes only the actual Collection and Separation
schemas of the displayed interpretation, the two primitive source inputs,
and the ordinal-stage bounds. No complete-code or node-set field remains.
-/

namespace OneYTruth.InternalSourceSets

open Constructible Constructible.FiniteSequenceZF Constructible.Model
open InternalClosure InternalProducts InternalNodes SigmaComparison

universe u v w

theorem sigmaNodes_mem_of_sources {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V U : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (indexCode : I → ZFSet.{u})
    (hSigma : sigmaCodes (k := k) indexCode ∈ V) (hAssignments : assignmentCodes U ∈ V) :
    sigmaNodes (k := k) indexCode U ∈ V := by
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  have hsource : ZFSet.range (sigmaCrossCode (k := k) (U := U) indexCode) ∈ V := by
    rw [sigmaCrossCode_range]
    exact pairProduct_mem hV N hmem (hRep 1 (pairFormula K J))
      (hRep 1 (mixedSliceGraphFormula K J)) hpair hUnion hSigma hAssignments
  rw [sigmaNodes_eq_filtered_cross]
  apply filtered_range_mem hV N (mixedMatchingArityFormula K J)
    (hSep 0 (mixedMatchingArityFormula K J)) ![]
    (sigmaCrossCode (k := k) (U := U) indexCode) (fun z => z.1.val.1 = z.2.1) hsource
  intro z hz
  rw [mixedMatchingArityFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have ht : Constructible.Delta0Formula.val
      (Fin.snoc ![] (⟨sigmaCrossCode indexCode z, hz⟩ : ZFCarrier V)) =
      ![sigmaCrossCode indexCode z] := by funext i; fin_cases i; rfl
  rw [ht]
  exact satisfies_matchingArityFormula indexCode (z.1.val, z.2)

theorem sourceSets_mem {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (indexCode : I → ZFSet.{u})
    (A U : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) (hAV : A.val ∈ V) (hU : U.val ∈ V) :
    syntaxCodes (k := k) indexCode ∈ V ∧ assignmentCodes U.val ∈ V ∧
      sigmaCodes (k := k) indexCode ∈ V ∧ sigmaNodes (k := k) indexCode U.val ∈ V := by
  have hsyn := InternalSyntaxCodes.syntaxCodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hOmega A hA hAV
  have hass := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  have hsig := InternalSyntaxCodes.sigmaCodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hOmega A hA hAV
  exact ⟨hsyn, hass, hsig, sigmaNodes_mem_of_sources hV N hmem hCol hSep hpair hUnion indexCode hsig hass⟩

theorem sourceSets_mem_LStageZF {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) (hωθ : Ordinal.omega0 < θ)
    (N : Interpretation K J (ZFCarrier (LStageZF θ))) (hmem : N.mem = zfCarrierMem (LStageZF θ))
    (hCol : HasCollection N) (hSep : HasSeparation N) (indexCode : I → ZFSet.{u})
    (hA : ZFSet.range indexCode ∈ LStageZF θ) {U : ZFSet.{u}} (hU : U ∈ LStageZF θ) :
    syntaxCodes (k := k) indexCode ∈ LStageZF θ ∧ assignmentCodes U ∈ LStageZF θ ∧
      sigmaCodes (k := k) indexCode ∈ LStageZF θ ∧ sigmaNodes (k := k) indexCode U ∈ LStageZF θ := by
  let A : LCarrier.{u} := ⟨ZFSet.range indexCode, mem_L_of_mem hA (LStageZF_mem_L θ)⟩
  let UL : LCarrier.{u} := ⟨U, mem_L_of_mem hU (LStageZF_mem_L θ)⟩
  exact sourceSets_mem (LStageZF_isTransitive θ) N hmem hCol hSep
    (fun _ ha _ hb => orderedPair_mem_LStageZF_of_isSuccLimit hθ ha hb)
    (fun _ ha => sUnion_mem_LStageZF_of_isSuccLimit hθ ha)
    (by simpa [natCode] using natCode_mem_LStageZF_of_isSuccLimit hθ 0)
    (ordinal_toZFSet_mem_LStageZF_of_lt hωθ) indexCode A UL rfl hA hU

end OneYTruth.InternalSourceSets

#print axioms OneYTruth.InternalSourceSets.sourceSets_mem_LStageZF
