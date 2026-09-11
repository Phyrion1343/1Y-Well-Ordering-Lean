/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalSolutionLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepBranchesLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalDomainLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion

/-!
# Decoding textbook E local solutions over L

An `LCarrier` graph satisfying the unchanged textbook local-solution formula
is decoded into an actual `TextbookLocalSolution`.  The textbook agreement
theorem then identifies every value of that graph with `textbookEByKey`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

open FiniteSequenceZF

namespace Model

local notation "LMem" => lCarrierMem

/-- Every `LCarrier` graph satisfying the textbook E local-solution formula
at a standard key decodes to the literal local solution used in the textbook
recursion theorem. -/
theorem exists_textbookELocalSolution_of_satisfies_lCarrier
    (a graph : LCarrier.{u}) (m n : Nat)
    (hformula : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph]) :
    exists solution : TextbookLocalSolution
        TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (textbookEStep a.1) (textbookEKeyLCarrier m n).1,
      solution.graph = graph.1 := by
  classical
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  let localDom : LCarrier.{u} := textbookELocalDomainLCarrier m n
  have hformula' : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      (snoc (snoc ![a] key) graph) := by
    have hassign : snoc (snoc ![a] key) graph = ![a, key, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa only [key] using hformula
  rcases (satisfies_localSolutionFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula ![a] key graph).mp
      hformula' with
    ⟨domain, hdomainFormula, hfunction, hsteps⟩
  have hdomainAssignment :
      snoc (snoc ![a] key) domain = ![a, key, domain] := by
    funext i
    fin_cases i <;> rfl
  have hdomainRaw : domain.1 = localDom.1 := by
    apply (satisfies_textbookELocalDomainFormula_lCarrier
      a domain m n).mp
    rw [← hdomainAssignment]
    simpa only [key] using hdomainFormula
  have hdomainEq : domain = localDom := Subtype.ext hdomainRaw
  subst domain
  let d : ZFSet.{u} := localDom.1
  have hdL : d ∈ L := localDom.2
  let asCarrier : forall t : ZFSet.{u}, t ∈ d -> LCarrier.{u} :=
    fun t ht => ⟨t, mem_L_of_mem ht hdL⟩
  have hfunctionTotal : forall t : ZFSet.{u}, forall ht : t ∈ d,
      exists value : LCarrier.{u},
        ZFSet.pair t value.1 ∈ graph.1 /\
          forall other : LCarrier.{u},
            ZFSet.pair t other.1 ∈ graph.1 -> other = value := by
    intro t ht
    have htLocal : (asCarrier t ht).1 ∈ localDom.1 := by
      simpa only [d, asCarrier] using ht
    simpa only [asCarrier] using hfunction.1 (asCarrier t ht) htLocal
  let chosenValue (t : ZFSet.{u}) (ht : t ∈ d) : LCarrier.{u} :=
    Classical.choose (hfunctionTotal t ht)
  let value : ZFSet.{u} -> ZFSet.{u} := fun t =>
    if ht : t ∈ d then (chosenValue t ht).1 else ∅
  have hchosenSpec (t : ZFSet.{u}) (ht : t ∈ d) :
      ZFSet.pair t (chosenValue t ht).1 ∈ graph.1 /\
        forall other : LCarrier.{u},
          ZFSet.pair t other.1 ∈ graph.1 ->
            other = chosenValue t ht :=
    Classical.choose_spec (hfunctionTotal t ht)
  have hvalueEqChosen (t : ZFSet.{u}) (ht : t ∈ d) :
      value t = (chosenValue t ht).1 := by
    simp only [value, dif_pos ht]
  have hvalueSpec (t : ZFSet.{u}) (ht : t ∈ d) :
      ZFSet.pair t (value t) ∈ graph.1 /\
        forall other : LCarrier.{u},
          ZFSet.pair t other.1 ∈ graph.1 ->
            other.1 = value t := by
    constructor
    · rw [hvalueEqChosen t ht]
      exact (hchosenSpec t ht).1
    · intro other hother
      have hotherEq := (hchosenSpec t ht).2 other hother
      rw [hotherEq, hvalueEqChosen t ht]
  have hvalueL (t : ZFSet.{u}) (ht : t ∈ d) : value t ∈ L := by
    rw [hvalueEqChosen t ht]
    exact (chosenValue t ht).2
  have hgraphEq : graph.1 = predecessorRestrictionGraph d value := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hpairGraph
      let pairL : LCarrier.{u} :=
        ⟨pair, mem_L_of_mem hpairGraph graph.2⟩
      rcases hfunction.2 pairL hpairGraph with
        ⟨input, hinputD, output, hpairEq⟩
      have hinputD' : input.1 ∈ d := by
        simpa only [d] using hinputD
      have houtputEq : output.1 = value input.1 :=
        (hvalueSpec input.1 hinputD').2 output (by
          rw [← hpairEq]
          exact hpairGraph)
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨input.1, hinputD', ?_⟩
      rw [← houtputEq]
      exact hpairEq.symm
    · intro hpairRestriction
      rcases mem_predecessorRestrictionGraph_iff.mp hpairRestriction with
        ⟨input, hinputD, hpairEq⟩
      rw [← hpairEq]
      exact (hvalueSpec input hinputD).1
  have hkeyDomain : key.1 ∈ TextbookEDomain := by
    simpa only [key] using textbookEKeyLCarrier_mem_domain m n
  have hsatisfies : SatisfiesTextbookLocalRecursion
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) key.1 value := by
    intro top htopD
    have htopD' : top ∈ d := by
      simpa only [d, localDom, key,
        textbookELocalDomainLCarrier_val,
        textbookEKeyLCarrier_val] using htopD
    let topL : LCarrier.{u} := asCarrier top htopD'
    have htopLocal : topL.1 ∈ localDom.1 := by
      simpa only [topL, asCarrier, d] using htopD'
    rcases hsteps topL htopLocal with
      ⟨restriction, output, hrestriction, houtputGraph, hstepFormula⟩
    have htopA : top ∈ TextbookEDomain :=
      localRecursionDomain_subset
        textbookERelation_hasSetPredecessorsOn hkeyDomain htopD
    have hrestrictionEq : restriction.1 =
        predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_hasSetPredecessorsOn top) value := by
      apply ZFSet.ext
      intro pair
      constructor
      · intro hpairRestriction
        let pairL : LCarrier.{u} :=
          ⟨pair, mem_L_of_mem hpairRestriction restriction.2⟩
        rcases (hrestriction pairL).mp hpairRestriction with
          ⟨hpairGraph, input, output', hpairEq,
            hinputFormula, hrelationFormula⟩
        have hinputAssignment : snoc ![a] input = ![a, input] := by
          funext i
          fin_cases i <;> rfl
        have hinputA : input.1 ∈ TextbookEDomain := by
          apply (satisfies_textbookEDomainWithParamFormula_lCarrier
            a input).mp
          simpa only [hinputAssignment] using hinputFormula
        have hrelationAssignment :
            snoc (snoc ![a] input) topL = ![a, input, topL] := by
          funext i
          fin_cases i <;> rfl
        have hinputTop : ClassRel TextbookERelation input.1 top := by
          apply (satisfies_textbookERelationWithParamFormula_lCarrier
            a input topL).mp
          simpa only [hrelationAssignment, topL, asCarrier] using
            hrelationFormula
        have hinputPred : input.1 ∈
            displayedPredecessors TextbookEDomain TextbookERelation
              textbookERelation_hasSetPredecessorsOn top :=
          (displayedPredecessors_spec
            textbookERelation_hasSetPredecessorsOn htopA input.1).mpr
              ⟨hinputA, hinputTop⟩
        have hinputD : input.1 ∈ d := by
          apply localRecursionDomain_predecessorClosed
            textbookERelation_isRelationOn
            textbookERelation_hasSetPredecessorsOn hkeyDomain htopD'
          exact hinputTop
        have houtputEq : output'.1 = value input.1 :=
          (hvalueSpec input.1 hinputD).2 output' (by
            rw [hpairEq] at hpairGraph
            exact hpairGraph)
        apply mem_predecessorRestrictionGraph_iff.mpr
        refine ⟨input.1, hinputPred, ?_⟩
        rw [← houtputEq]
        simpa only [pairL] using hpairEq.symm
      · intro hpairExpected
        rcases mem_predecessorRestrictionGraph_iff.mp hpairExpected with
          ⟨input, hinputPred, hpairEq⟩
        have hinputSpec :=
          (displayedPredecessors_spec
            textbookERelation_hasSetPredecessorsOn htopA input).mp
              hinputPred
        have hinputD : input ∈ d := by
          apply localRecursionDomain_predecessorClosed
            textbookERelation_isRelationOn
            textbookERelation_hasSetPredecessorsOn hkeyDomain htopD'
          exact hinputSpec.2
        let inputL : LCarrier.{u} := asCarrier input hinputD
        let valueL : LCarrier.{u} := ⟨value input, hvalueL input hinputD⟩
        let pairL : LCarrier.{u} := orderedPairLCarrier inputL valueL
        have hpairMembership : pairL.1 ∈ restriction.1 := by
          apply (hrestriction pairL).mpr
          refine ⟨?_, inputL, valueL, ?_, ?_, ?_⟩
          · simpa only [pairL, orderedPairLCarrier_val, inputL, valueL]
              using (hvalueSpec input hinputD).1
          · simp only [pairL, orderedPairLCarrier_val, inputL, valueL]
          · have hinputAssignment : snoc ![a] inputL = ![a, inputL] := by
              funext i
              fin_cases i <;> rfl
            rw [hinputAssignment]
            exact (satisfies_textbookEDomainWithParamFormula_lCarrier
              a inputL).mpr hinputSpec.1
          · have hrelationAssignment :
                snoc (snoc ![a] inputL) topL =
                  ![a, inputL, topL] := by
              funext i
              fin_cases i <;> rfl
            rw [hrelationAssignment]
            apply (satisfies_textbookERelationWithParamFormula_lCarrier
              a inputL topL).mpr
            simpa only [inputL, topL, asCarrier] using hinputSpec.2
        rw [← hpairEq]
        simpa only [pairL, orderedPairLCarrier_val, inputL, valueL] using
          hpairMembership
    have houtputEq : output.1 = value top :=
      (hvalueSpec top htopD').2 output (by
        simpa only [topL, asCarrier] using houtputGraph)
    have hstepAssignment :
        snoc (snoc (snoc ![a] topL) restriction) output =
          ![a, topL, restriction, output] := by
      funext i
      fin_cases i <;> rfl
    have hstepSemantic :=
      (satisfies_textbookEStepFormula_lCarrier_iff
        a topL restriction output).mp (by
          rw [← hstepAssignment]
          exact hstepFormula)
    have hstepEq : output.1 = textbookEStep a.1 top restriction.1 := by
      simpa only [topL, asCarrier] using hstepSemantic.2
    rw [← houtputEq, hstepEq, hrestrictionEq]
  let solution : TextbookLocalSolution
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) key.1 :=
    { value := value
      graph := graph.1
      graph_eq := hgraphEq
      satisfies := hsatisfies }
  let solution' : TextbookLocalSolution
      TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (textbookEStep a.1) (textbookEKeyLCarrier m n).1 := by
    simpa only [key] using solution
  refine ⟨solution', ?_⟩
  simp only [solution', solution]

/-- Every value displayed by a formula-satisfying local graph is the value
of the textbook global recursion. -/
theorem textbookEByKey_eq_of_satisfies_localSolution_lCarrier
    (a graph output : LCarrier.{u}) (m n : Nat)
    (hformula : FOFormula.Satisfies LMem
      (localSolutionFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula
        TextbookEFormula.textbookEStepFormula)
      ![a, textbookEKeyLCarrier m n, graph])
    (hvalue : ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈
      graph.1) :
    output.1 = textbookEByKey a.1 (textbookEKeyLCarrier m n).1 := by
  rcases exists_textbookELocalSolution_of_satisfies_lCarrier
      a graph m n hformula with ⟨solution, hsolutionGraph⟩
  have hvalueRestriction :
      ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈
        predecessorRestrictionGraph
          (localRecursionDomain TextbookEDomain TextbookERelation
            textbookERelation_hasSetPredecessorsOn
            (textbookEKeyLCarrier m n).1) solution.value := by
    rw [← solution.graph_eq, hsolutionGraph]
    exact hvalue
  rcases mem_predecessorRestrictionGraph_iff.mp hvalueRestriction with
    ⟨source, _hsource, hpair⟩
  have hcoordinates := ZFSet.pair_inj.mp hpair
  have hlocalValue : output.1 =
      solution.value (textbookEKeyLCarrier m n).1 := by
    rw [hcoordinates.1] at hcoordinates
    exact hcoordinates.2.symm
  have hkeyDomain := textbookEKeyLCarrier_mem_domain m n
  have htopLocal : (textbookEKeyLCarrier m n).1 ∈
      localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (textbookEKeyLCarrier m n).1 :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  have hagree :=
    textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
      textbookERelation_isWellFoundedSetLikeOn
      (textbookEStep a.1) hkeyDomain solution htopLocal
  exact hlocalValue.trans (by
    simpa only [textbookEByKey] using hagree.symm)

end Model

end

end Constructible
