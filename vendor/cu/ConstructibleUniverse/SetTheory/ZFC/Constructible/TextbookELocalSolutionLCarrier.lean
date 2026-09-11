/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalSolutionLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalDomainLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepBranchesLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion

/-!
# Canonical local E solutions over L

This file verifies the unmodified textbook `localSolutionFormula` for the
actual restriction of `textbookEByKey` to a standard local recursion domain.
Every graph in the proof is an element of `LCarrier`: the local graph is an
explicit hypothesis, and each predecessor restriction is obtained by
Separation from that graph.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

private theorem textbookEByKey_mem_L_of_mem_local_graph
    (a graph : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1))
    {x : ZFSet.{u}}
    (hx : x ∈ (textbookELocalDomainLCarrier m n).1) :
    textbookEByKey a.1 x ∈ L := by
  have hpairGraph :
      ZFSet.pair x (textbookEByKey a.1 x) ∈ graph.1 := by
    rw [hgraph]
    exact pair_mem_predecessorRestrictionGraph
      (textbookEByKey a.1) hx
  have hpairL :
      ZFSet.pair x (textbookEByKey a.1 x) ∈ L :=
    mem_L_of_mem hpairGraph graph.2
  have hunorderedPair :
      ({x, textbookEByKey a.1 x} : ZFSet.{u}) ∈
        ZFSet.pair x (textbookEByKey a.1 x) := by
    simp [ZFSet.pair]
  have hunorderedPairL :
      ({x, textbookEByKey a.1 x} : ZFSet.{u}) ∈ L :=
    mem_L_of_mem hunorderedPair hpairL
  exact mem_L_of_mem (by simp) hunorderedPairL

private theorem formulaRestriction_textbookEByKey_eq
    (a graph top : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1))
    (htop : top.1 ∈ (textbookELocalDomainLCarrier m n).1) :
    (formulaRestrictionLCarrier
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top).1 =
      predecessorRestrictionGraph
        (displayedPredecessors TextbookEDomain TextbookERelation
          textbookERelation_isWellFoundedSetLikeOn.2.2 top.1)
        (textbookEByKey a.1) := by
  have hkeyDomain :
      (textbookEKeyLCarrier m n).1 ∈ TextbookEDomain :=
    textbookEKeyLCarrier_mem_domain m n
  have htopDomain : top.1 ∈ TextbookEDomain := by
    exact localRecursionDomain_subset
      textbookERelation_hasSetPredecessorsOn hkeyDomain htop
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases
        (mem_formulaRestrictionLCarrier_raw_iff
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula
          ![a] graph top pair).mp hpair with
      ⟨hpairGraph, input, output, hpairEq, hinputFormula,
        hrelationFormula⟩
    have hinputDomain : input.1 ∈ TextbookEDomain := by
      have hassign : snoc ![a] input = ![a, input] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEDomainWithParamFormula_lCarrier] at hinputFormula
      exact hinputFormula
    have hinputRelation :
        ClassRel TextbookERelation input.1 top.1 := by
      have hassign :
          snoc (snoc ![a] input) top = ![a, input, top] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookERelationWithParamFormula_lCarrier] at hrelationFormula
      exact hrelationFormula
    have hinputPredecessor :
        input.1 ∈
          displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2 top.1 :=
      (displayedPredecessors_spec
        textbookERelation_isWellFoundedSetLikeOn.2.2
        htopDomain input.1).mpr
        ⟨hinputDomain, hinputRelation⟩
    rw [hgraph] at hpairGraph
    rcases mem_predecessorRestrictionGraph_iff.mp hpairGraph with
      ⟨x, _hx, hgraphPair⟩
    have hcoordinates :=
      ZFSet.pair_inj.mp (hgraphPair.trans hpairEq)
    have hvalue :
        textbookEByKey a.1 input.1 = output.1 := by
      calc
        textbookEByKey a.1 input.1 =
            textbookEByKey a.1 x :=
          congrArg (textbookEByKey a.1) hcoordinates.1.symm
        _ = output.1 := hcoordinates.2
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨input.1, hinputPredecessor, ?_⟩
    calc
      ZFSet.pair input.1 (textbookEByKey a.1 input.1) =
          ZFSet.pair input.1 output.1 := by rw [hvalue]
      _ = pair := hpairEq.symm
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨input, hinputPredecessor, hpairEq⟩
    have hinputSpec :=
      (displayedPredecessors_spec
        textbookERelation_isWellFoundedSetLikeOn.2.2
        htopDomain input).mp hinputPredecessor
    have hinputLocal :
        input ∈ (textbookELocalDomainLCarrier m n).1 := by
      exact localRecursionDomain_predecessorClosed
        textbookERelation_isRelationOn
        textbookERelation_hasSetPredecessorsOn hkeyDomain
        htop hinputSpec.2
    have hpairGraph : pair ∈ graph.1 := by
      rw [hgraph]
      apply mem_predecessorRestrictionGraph_iff.mpr
      exact ⟨input, hinputLocal, hpairEq⟩
    let inputL : LCarrier.{u} :=
      ⟨input, mem_L_of_mem hinputLocal
        (textbookELocalDomainLCarrier m n).2⟩
    let outputL : LCarrier.{u} :=
      ⟨textbookEByKey a.1 input,
        textbookEByKey_mem_L_of_mem_local_graph
          a graph m n hgraph hinputLocal⟩
    apply
      (mem_formulaRestrictionLCarrier_raw_iff
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top pair).mpr
    refine ⟨hpairGraph, inputL, outputL, hpairEq.symm, ?_, ?_⟩
    · have hassign : snoc ![a] inputL = ![a, inputL] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEDomainWithParamFormula_lCarrier]
      exact hinputSpec.1
    · have hassign :
          snoc (snoc ![a] inputL) top = ![a, inputL, top] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookERelationWithParamFormula_lCarrier]
      exact hinputSpec.2

/-- The actual restriction graph of `textbookEByKey` on the canonical local
domain satisfies the exact textbook local-solution formula.  The hypothesis
does not merely assert an external graph predicate: `graph` is an actual
member of `LCarrier` whose underlying `ZFSet` is the displayed restriction
graph. -/
theorem textbookECanonicalLocalGraph_satisfies_localSolution
    (a graph : LCarrier.{u}) (m n : Nat)
    (hgraph :
      graph.1 =
        predecessorRestrictionGraph
          (textbookELocalDomainLCarrier m n).1
          (textbookEByKey a.1)) :
    FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph] := by
  let domain : LCarrier.{u} := textbookELocalDomainLCarrier m n
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  apply
    (satisfies_localSolutionFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula
      ![a] key graph).mpr
  refine ⟨domain, ?_, ?_, ?_⟩
  · have hassign :
        snoc (snoc ![a] key) domain =
          ![a, textbookEKeyLCarrier m n, domain] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    apply
      (satisfies_textbookELocalDomainFormula_lCarrier
        a domain m n).mpr
    rfl
  · constructor
    · intro input hinput
      let value : LCarrier.{u} :=
        ⟨textbookEByKey a.1 input.1,
          textbookEByKey_mem_L_of_mem_local_graph
            a graph m n hgraph hinput⟩
      refine ⟨value, ?_, ?_⟩
      · rw [hgraph]
        exact pair_mem_predecessorRestrictionGraph
          (textbookEByKey a.1) hinput
      · intro other hother
        rw [hgraph] at hother
        rcases mem_predecessorRestrictionGraph_iff.mp hother with
          ⟨x, _hx, hpair⟩
        have hcoordinates := ZFSet.pair_inj.mp hpair
        apply Subtype.ext
        calc
          other.1 = textbookEByKey a.1 x :=
            hcoordinates.2.symm
          _ = textbookEByKey a.1 input.1 :=
            congrArg (textbookEByKey a.1) hcoordinates.1
          _ = value.1 := rfl
    · intro pair hpair
      rw [hgraph] at hpair
      rcases mem_predecessorRestrictionGraph_iff.mp hpair with
        ⟨input, hinput, hpairEq⟩
      let inputL : LCarrier.{u} :=
        ⟨input, mem_L_of_mem hinput domain.2⟩
      let value : LCarrier.{u} :=
        ⟨textbookEByKey a.1 input,
          textbookEByKey_mem_L_of_mem_local_graph
            a graph m n hgraph hinput⟩
      refine ⟨inputL, hinput, value, ?_⟩
      exact hpairEq.symm
  · intro top htop
    let restriction : LCarrier.{u} :=
      formulaRestrictionLCarrier
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        ![a] graph top
    have htopDomain : top.1 ∈ TextbookEDomain := by
      exact localRecursionDomain_subset
        textbookERelation_hasSetPredecessorsOn
        (textbookEKeyLCarrier_mem_domain m n) htop
    let value : LCarrier.{u} :=
      ⟨textbookEByKey a.1 top.1,
        textbookEByKey_mem_L_of_mem_local_graph
          a graph m n hgraph htop⟩
    refine ⟨restriction, value, ?_, ?_, ?_⟩
    · intro pair
      exact
        mem_formulaRestrictionLCarrier_iff
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula
          ![a] graph top pair
    · rw [hgraph]
      exact pair_mem_predecessorRestrictionGraph
        (textbookEByKey a.1) htop
    · have hrestriction :
          restriction.1 =
            predecessorRestrictionGraph
              (displayedPredecessors TextbookEDomain TextbookERelation
                textbookERelation_isWellFoundedSetLikeOn.2.2 top.1)
              (textbookEByKey a.1) := by
        exact formulaRestriction_textbookEByKey_eq
          a graph top m n hgraph htop
      have hrecursion :=
        textbookEByKey_satisfies_classRecursion a.1 top.1 htopDomain
      have hassign :
          snoc (snoc (snoc ![a] top) restriction) value =
            ![a, top, restriction, value] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign,
        satisfies_textbookEStepFormula_lCarrier_iff]
      refine ⟨htopDomain, ?_⟩
      change
        textbookEByKey a.1 top.1 =
          textbookEStep a.1 top.1 restriction.1
      rw [hrestriction]
      exact hrecursion

end

end Model

end Constructible
