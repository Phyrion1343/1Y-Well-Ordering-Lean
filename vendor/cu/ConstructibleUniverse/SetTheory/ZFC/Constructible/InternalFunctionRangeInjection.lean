/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FullSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FunctionGraphFormulaLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalUnion

/-!
# Internal injections from function ranges

For a represented function graph whose displayed codomain is its actual
range, the canonical constructible well-order selects the least preimage of
each range element.  Replacement collects these selections into an actual
right-inverse graph in `L`, yielding an internal injection of the range into
the original domain.
-/

@[expose] public section

universe u

namespace Constructible

noncomputable section

namespace Model

open ContinuumFormula

local notation "LMem" => lCarrierMem

/-! ## Fibers and their canonical minima -/

/-- Layout `[graph,value,input]`: `graph(input) = value`. -/
def inverseFiberFormula : FOFormula 3 :=
  graphRelAt (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_inverseFiberFormula
    (graph value input : LCarrier.{u}) :
    FOFormula.Satisfies LMem inverseFiberFormula
        ![graph, value, input] <->
      GraphRel graph input value := by
  exact satisfies_graphRelAt
    (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)
    ![graph, value, input]

/-- The actual constructible fiber of `value`, bounded by `domain`. -/
def inverseFiberLCarrier
    (graph domain value : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    inverseFiberFormula ![graph, value] domain)

@[simp]
theorem mem_inverseFiberLCarrier_iff
    (graph domain value input : LCarrier.{u}) :
    input.1 ∈ (inverseFiberLCarrier graph domain value).1 <->
      input.1 ∈ domain.1 /\ GraphRel graph input value := by
  rw [inverseFiberLCarrier]
  rw [Classical.choose_spec (exists_separationLCarrier
    inverseFiberFormula ![graph, value] domain) input]
  have hassign : snoc ![graph, value] input =
      ![graph, value, input] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_inverseFiberFormula]

/-- Layout `[graph,domain,order,value,input]`: `input` is the least member of
the inverse fiber of `value`. -/
def inverseMinimumFormula : FOFormula 5 :=
  .conj (.mem (4 : Fin 5) (1 : Fin 5))
    (.conj
      (graphRelAt (0 : Fin 5) (4 : Fin 5) (3 : Fin 5))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (Fin.last 5) (1 : Fin 5).castSucc)
            (graphRelAt
              (0 : Fin 5).castSucc (Fin.last 5)
              (3 : Fin 5).castSucc))
          (.neg
            (graphRelAt
              (2 : Fin 5).castSucc (Fin.last 5)
              (4 : Fin 5).castSucc)))))

@[simp]
theorem satisfies_inverseMinimumFormula
    (graph domain order value input : LCarrier.{u}) :
    FOFormula.Satisfies LMem inverseMinimumFormula
        ![graph, domain, order, value, input] <->
      input.1 ∈ domain.1 /\
        GraphRel graph input value /\
          forall other : LCarrier.{u}, other.1 ∈ domain.1 ->
            GraphRel graph other value ->
              Not (GraphRel order other input) := by
  simp only [inverseMinimumFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinput, hvalue, hminimum⟩
    exact ⟨hinput, hvalue,
      fun other hother hotherValue =>
        hminimum other ⟨hother, hotherValue⟩⟩
  · rintro ⟨hinput, hvalue, hminimum⟩
    exact ⟨hinput, hvalue,
      fun other hother => hminimum other hother.1 hother.2⟩

/-- The inverse-minimum formula has exactly one output at every covered
range value. -/
theorem existsUnique_inverseMinimumFormula
    (graph domain range value : LCarrier.{u})
    (hcovered : forall y : LCarrier.{u}, y.1 ∈ range.1 ->
      exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
        GraphValue LMem graph x y)
    (hvalue : value.1 ∈ range.1) :
    ExistsUnique fun input : LCarrier.{u} =>
      FOFormula.Satisfies LMem inverseMinimumFormula
        ![graph, domain, canonicalWitnessOrder domain, value, input] := by
  let fiber := inverseFiberLCarrier graph domain value
  have hfiberSubset : forall z : LCarrier.{u}, z.1 ∈ fiber.1 ->
      z.1 ∈ (canonicalWitnessStage domain).1 := by
    intro z hz
    exact seed_subset_canonicalWitnessStage domain
      ((mem_inverseFiberLCarrier_iff graph domain value z).mp hz).1
  have hfiberNonempty : exists z : LCarrier.{u}, z.1 ∈ fiber.1 := by
    rcases hcovered value hvalue with ⟨z, hzDomain, hzValue⟩
    refine ⟨z, (mem_inverseFiberLCarrier_iff
      graph domain value z).mpr ⟨hzDomain, ?_⟩⟩
    exact (ContinuumFormula.graphValue_lCarrier_iff_graphRel
      graph z value).mp hzValue
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders domain)
      hfiberSubset hfiberNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_inverseMinimumFormula
      graph domain (canonicalWitnessOrder domain) value minimum).mpr
    have hminimumFiber :=
      (mem_inverseFiberLCarrier_iff
        graph domain value minimum).mp hminimum.1
    exact ⟨hminimumFiber.1, hminimumFiber.2, fun other hother hgraph =>
      hminimum.2 other
        ((mem_inverseFiberLCarrier_iff
          graph domain value other).mpr ⟨hother, hgraph⟩)⟩
  · intro other hother
    apply hminimumUnique other
    have hotherData :=
      (satisfies_inverseMinimumFormula
        graph domain (canonicalWitnessOrder domain) value other).mp hother
    refine ⟨(mem_inverseFiberLCarrier_iff
      graph domain value other).mpr ⟨hotherData.1, hotherData.2.1⟩, ?_⟩
    intro z hzFiber
    have hzData := (mem_inverseFiberLCarrier_iff
      graph domain value z).mp hzFiber
    exact hotherData.2.2 z hzData.1 hzData.2

/-! ## The represented inverse injection -/

private theorem inverseMinimumAssignment
    (graph domain order value input : LCarrier.{u}) :
    snoc (snoc ![graph, domain, order] value) input =
      ![graph, domain, order, value, input] := by
  funext i
  fin_cases i <;> rfl

/-- A represented function onto its displayed range admits an internally
represented injection of that range back into the original domain. -/
theorem injects_range_into_domain_of_functionGraph
    (graph domain range : LCarrier.{u})
    (hfunction : ContinuumFormula.IsFunctionGraph LMem
      graph domain range)
    (hcovered : forall y : LCarrier.{u}, y.1 ∈ range.1 ->
      exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
        GraphValue LMem graph x y) :
    Injects LMem range domain := by
  let order := canonicalWitnessOrder domain
  let params : Tuple LCarrier.{u} 3 := ![graph, domain, order]
  have hformulaUnique : forall value : LCarrier.{u},
      value.1 ∈ range.1 ->
        ExistsUnique fun input : LCarrier.{u} =>
          FOFormula.Satisfies LMem inverseMinimumFormula
            (snoc (snoc params value) input) := by
    intro value hvalue
    simpa only [params, order, inverseMinimumAssignment] using
      existsUnique_inverseMinimumFormula
        graph domain range value hcovered hvalue
  rcases exists_replacementFunctionGraphLCarrier
      inverseMinimumFormula params range hformulaUnique with
    ⟨inverse, hinverse⟩
  have hgraphValue (value input : LCarrier.{u}) :
      GraphValue LMem inverse value input <->
        value.1 ∈ range.1 /\
          FOFormula.Satisfies LMem inverseMinimumFormula
            ![graph, domain, order, value, input] := by
    constructor
    · rintro ⟨pair, hpairInverse, hpairValue⟩
      rcases (hinverse pair.1).mp hpairInverse with
        ⟨value', hvalue', input', hinput', hpairEq⟩
      have hpairValueRaw :=
        (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
          pair value input).mp hpairValue
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairValueRaw)
      have hvalueEq : value' = value := Subtype.ext hcoordinates.1
      have hinputEq : input' = input := Subtype.ext hcoordinates.2
      subst value'
      subst input'
      exact ⟨hvalue', by
        simpa only [params, order, inverseMinimumAssignment] using hinput'⟩
    · rintro ⟨hvalue, hinput⟩
      let pair := orderedPairLCarrier value input
      refine ⟨pair, ?_, ?_⟩
      · apply (hinverse pair.1).mpr
        refine ⟨value, hvalue, input, ?_, rfl⟩
        simpa only [params, order, inverseMinimumAssignment] using hinput
      · exact (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
          pair value input).mpr rfl
  refine ⟨inverse, ?_, ?_, ?_⟩
  · intro pair hpairInverse
    rcases (hinverse pair.1).mp hpairInverse with
      ⟨value, hvalue, input, hinputFormula, hpairEq⟩
    have hinput :=
      (satisfies_inverseMinimumFormula
        graph domain order value input).mp (by
          simpa only [params, order, inverseMinimumAssignment] using
            hinputFormula) |>.1
    exact ⟨value, hvalue, input, hinput,
      (ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
        pair value input).mpr hpairEq⟩
  · intro value hvalue
    rcases hformulaUnique value hvalue with
      ⟨input, hinputFormula, hinputUnique⟩
    have hinput :=
      (satisfies_inverseMinimumFormula
        graph domain order value input).mp (by
          simpa only [params, order, inverseMinimumAssignment] using
            hinputFormula) |>.1
    refine ⟨input, hinput, (hgraphValue value input).mpr
      ⟨hvalue, by
        simpa only [params, order, inverseMinimumAssignment] using
          hinputFormula⟩, ?_⟩
    intro other hotherDomain hotherValue
    apply hinputUnique other
    have hotherFormula := (hgraphValue value other).mp hotherValue |>.2
    simpa only [params, order, inverseMinimumAssignment] using hotherFormula
  · intro input hinput value hvalue hvalueInput other hother hotherInput
    have hvalueOriginal : GraphValue LMem graph input value := by
      apply (ContinuumFormula.graphValue_lCarrier_iff_graphRel
        graph input value).mpr
      exact (satisfies_inverseMinimumFormula
        graph domain order value input).mp
          ((hgraphValue value input).mp hvalueInput).2 |>.2.1
    have hotherOriginal : GraphValue LMem graph input other := by
      apply (ContinuumFormula.graphValue_lCarrier_iff_graphRel
        graph input other).mpr
      exact (satisfies_inverseMinimumFormula
        graph domain order other input).mp
          ((hgraphValue other input).mp hotherInput).2 |>.2.1
    exact hfunction.graphValue_unique hinput hvalue hother
      hvalueOriginal hotherOriginal |>.symm

end Model

end

end Constructible
