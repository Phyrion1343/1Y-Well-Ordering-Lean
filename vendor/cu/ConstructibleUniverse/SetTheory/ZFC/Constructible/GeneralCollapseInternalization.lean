/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Condensation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalMostowskiCollapse
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.PowerSet

/-!
# Internalizing the collapse of a condensation hull

For a constructible elementary hull, Condensation first identifies the
external Mostowski-collapse range with an actual constructible level.  This
file then constructs the collapse graph in `L` without assuming a
`CollapseFormulaSpec`.

The graph is the union of all constructible partial collapse graphs contained
in `domain x range`.  A partial graph is downward closed and satisfies the
usual local recursion equation.  Well-founded induction shows that all of
its values are the external Mostowski-collapse values.  The same induction
then extends the union at every point, proving that it is the full collapse
graph.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

open Constructible.ContinuumFormula

local notation "LMem" => lCarrierMem

/-! ## Partial collapse graphs -/

/--
A downward-closed partial solution of the Mostowski recursion on `domain`,
with all outputs in `target`.

The recursion clause is exactly
`y = { value(z) | z in x and z in domain }` whenever `(x,y)` is in `graph`.
Functionality is not an extra field: well-founded induction derives it from
this recursion equation.
-/
structure IsPartialCollapseGraph
    (graph domain target : LCarrier.{u}) : Prop where
  graphBetween : IsGraphBetween LMem graph domain target
  predecessor : forall x y : LCarrier.{u},
    GraphValue LMem graph x y ->
      forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ domain.1 ->
        exists value : LCarrier.{u},
          value.1 ∈ target.1 /\ GraphValue LMem graph z value
  recursion : forall x y : LCarrier.{u},
    GraphValue LMem graph x y ->
      forall value : LCarrier.{u},
        value.1 ∈ y.1 <->
          exists z : LCarrier.{u},
            z.1 ∈ x.1 /\ z.1 ∈ domain.1 /\
              GraphValue LMem graph z value

/-- Layout `[domain, target, graph]` for a partial collapse graph. -/
def partialCollapseGraphFormula : FOFormula 3 :=
  .conj (graphBetweenAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (FOFormula.boundedAll (0 : Fin 3)
      (FOFormula.boundedAll (1 : Fin 4)
        (FOFormula.imp
          (graphValueAt (2 : Fin 5) (3 : Fin 5) (4 : Fin 5))
          (.conj
            (FOFormula.boundedAll (3 : Fin 5)
              (FOFormula.imp
                (.mem (5 : Fin 6) (0 : Fin 6))
                (FOFormula.boundedEx (1 : Fin 6)
                  (graphValueAt
                    (2 : Fin 7) (5 : Fin 7) (6 : Fin 7)))))
            (FOFormula.all
              (FOFormula.biimp
                (.mem (5 : Fin 6) (4 : Fin 6))
                (FOFormula.boundedEx (3 : Fin 6)
                  (.conj
                    (.mem (6 : Fin 7) (0 : Fin 7))
                    (graphValueAt
                      (2 : Fin 7) (6 : Fin 7) (5 : Fin 7))))))))))

private theorem partialCollapseGraph_assignment
    (domain target graph : LCarrier.{u}) :
    ![domain, target, graph] =
      snoc (snoc ![domain] target) graph := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_partialCollapseGraphFormula
    (domain target graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem partialCollapseGraphFormula
        ![domain, target, graph] <->
      IsPartialCollapseGraph graph domain target := by
  simp only [partialCollapseGraphFormula, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedEx,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    satisfies_graphValueAt]
  constructor
  · rintro ⟨hbetween, hlocal⟩
    refine ⟨hbetween, ?_, ?_⟩
    · intro x y hxy z hzx hzDomain
      have hbody := hlocal x
        (hbetween.graphValue_mem_lCarrier hxy).1 y
        (hbetween.graphValue_mem_lCarrier hxy).2 hxy
      rcases hbody.1 z hzx hzDomain with ⟨value, hvalue⟩
      exact ⟨value, hvalue⟩
    · intro x y hxy value
      have hbody := hlocal x
        (hbetween.graphValue_mem_lCarrier hxy).1 y
        (hbetween.graphValue_mem_lCarrier hxy).2 hxy
      exact hbody.2 value
  · intro h
    refine ⟨h.graphBetween, ?_⟩
    intro x hxDomain y hyTarget hxy
    refine ⟨?_, h.recursion x y hxy⟩
    intro z hzx hzDomain
    exact h.predecessor x y hxy z hzx hzDomain

/-- Every value in a partial collapse graph is the genuine collapse value. -/
theorem IsPartialCollapseGraph.value_eq_collapse
    {graph domain target : LCarrier.{u}}
    (h : IsPartialCollapseGraph graph domain target) :
    forall x y : LCarrier.{u}, GraphValue LMem graph x y ->
      y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  intro x
  refine ZFSet.inductionOn
    (p := fun xRaw => forall (hxL : xRaw ∈ L) (y : LCarrier.{u}),
      GraphValue LMem graph ⟨xRaw, hxL⟩ y ->
        y.1 = MostowskiCollapse.collapse domain.1 xRaw)
    x.1 ?_ x.2
  intro xRaw ih hxL y hxy
  apply ZFSet.ext
  intro value
  constructor
  · intro hvalueY
    let xL : LCarrier.{u} := ⟨xRaw, hxL⟩
    let valueL : LCarrier.{u} :=
      ⟨value, mem_L_of_mem hvalueY y.2⟩
    rcases (h.recursion xL y hxy valueL).mp hvalueY with
      ⟨z, hzX, hzDomain, hzValue⟩
    have hzCollapse :
        value = MostowskiCollapse.collapse domain.1 z.1 :=
      ih z.1 hzX z.2 valueL hzValue
    exact MostowskiCollapse.mem_collapse_iff.mpr
      ⟨z.1, hzX, hzDomain, hzCollapse.symm⟩
  · intro hvalueCollapse
    rcases MostowskiCollapse.mem_collapse_iff.mp hvalueCollapse with
      ⟨zRaw, hzX, hzDomain, hzCollapse⟩
    let z : LCarrier.{u} :=
      ⟨zRaw, mem_L_of_mem hzDomain domain.2⟩
    rcases h.predecessor ⟨xRaw, hxL⟩ y hxy z hzX hzDomain with
      ⟨image, _himageTarget, hzImage⟩
    have himageCollapse :
        image.1 = MostowskiCollapse.collapse domain.1 zRaw :=
      ih zRaw hzX z.2 image hzImage
    have himageValue : image.1 = value :=
      himageCollapse.trans hzCollapse
    have himageY : image.1 ∈ y.1 :=
      (h.recursion ⟨xRaw, hxL⟩ y hxy image).mpr
        ⟨z, hzX, hzDomain, hzImage⟩
    simpa only [himageValue] using himageY

/-! ## The set of all constructible partial collapse graphs -/

theorem IsPartialCollapseGraph.subset_product
    {graph domain target : LCarrier.{u}}
    (h : IsPartialCollapseGraph graph domain target) :
    graph.1 ⊆ (prodLCarrier domain target).1 := by
  intro pair hpair
  let pairL : LCarrier.{u} :=
    ⟨pair, mem_L_of_mem hpair graph.2⟩
  rcases h.graphBetween pairL hpair with
    ⟨x, hxDomain, y, hyTarget, hpairXY⟩
  have hpairEq :=
    (isKuratowskiPairOf_lCarrier_iff pairL x y).mp hpairXY
  change pair = ZFSet.pair x.1 y.1 at hpairEq
  change pair ∈ ZFSet.prod domain.1 target.1
  rw [hpairEq, ZFSet.pair_mem_prod]
  exact ⟨hxDomain, hyTarget⟩

theorem exists_partialCollapsePower
    (domain target : LCarrier.{u}) :
    exists power : LCarrier.{u}, forall graph : LCarrier.{u},
      graph.1 ∈ power.1 <->
        graph.1 ⊆ (prodLCarrier domain target).1 :=
  exists_powerSetLCarrier (prodLCarrier domain target)

/-- The internal powerset of `domain x target`. -/
noncomputable def partialCollapsePower
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_partialCollapsePower domain target)

@[simp]
theorem mem_partialCollapsePower_iff
    (domain target graph : LCarrier.{u}) :
    graph.1 ∈ (partialCollapsePower domain target).1 <->
      graph.1 ⊆ (prodLCarrier domain target).1 :=
  Classical.choose_spec (exists_partialCollapsePower domain target) graph

theorem exists_partialCollapseGraphFamily
    (domain target : LCarrier.{u}) :
    exists family : LCarrier.{u}, forall graph : LCarrier.{u},
      graph.1 ∈ family.1 <-> IsPartialCollapseGraph graph domain target := by
  rcases exists_separationLCarrier partialCollapseGraphFormula
      ![domain, target] (partialCollapsePower domain target) with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro graph
  rw [hfamily graph, mem_partialCollapsePower_iff]
  have hassignment : snoc ![domain, target] graph =
      ![domain, target, graph] :=
    (partialCollapseGraph_assignment domain target graph).symm
  rw [hassignment, satisfies_partialCollapseGraphFormula]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.subset_product, h⟩

/-- The actual constructible set of all constructible partial collapse graphs. -/
noncomputable def partialCollapseGraphFamily
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_partialCollapseGraphFamily domain target)

@[simp]
theorem mem_partialCollapseGraphFamily_iff
    (domain target graph : LCarrier.{u}) :
    graph.1 ∈ (partialCollapseGraphFamily domain target).1 <->
      IsPartialCollapseGraph graph domain target :=
  Classical.choose_spec
    (exists_partialCollapseGraphFamily domain target) graph

/-- The union of all constructible partial collapse graphs. -/
noncomputable def maximalPartialCollapseGraph
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  sUnionLCarrier (partialCollapseGraphFamily domain target)

@[simp]
theorem mem_maximalPartialCollapseGraph_iff
    (domain target : LCarrier.{u}) (pair : LCarrier.{u}) :
    pair.1 ∈ (maximalPartialCollapseGraph domain target).1 <->
      exists graph : LCarrier.{u},
        IsPartialCollapseGraph graph domain target /\ pair.1 ∈ graph.1 := by
  rw [maximalPartialCollapseGraph, mem_sUnionLCarrier_iff]
  apply exists_congr
  intro graph
  rw [mem_partialCollapseGraphFamily_iff]

private theorem graphValue_maximal_of_graphValue
    {domain target graph x y : LCarrier.{u}}
    (hgraph : IsPartialCollapseGraph graph domain target)
    (hxy : GraphValue LMem graph x y) :
    GraphValue LMem (maximalPartialCollapseGraph domain target) x y := by
  rcases hxy with ⟨pair, hpairGraph, hpairXY⟩
  refine ⟨pair, ?_, hpairXY⟩
  exact (mem_maximalPartialCollapseGraph_iff domain target pair).mpr
    ⟨graph, hgraph, hpairGraph⟩

private theorem graphValue_maximal_eq_collapse
    {domain target x y : LCarrier.{u}}
    (hxy : GraphValue LMem
      (maximalPartialCollapseGraph domain target) x y) :
    y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  rcases hxy with ⟨pair, hpairMaximal, hpairXY⟩
  rcases (mem_maximalPartialCollapseGraph_iff domain target pair).mp
      hpairMaximal with ⟨graph, hgraph, hpairGraph⟩
  exact hgraph.value_eq_collapse x y ⟨pair, hpairGraph, hpairXY⟩

/-- The union of all partial graphs is itself a partial collapse graph. -/
theorem maximalPartialCollapseGraph_isPartial
    (domain target : LCarrier.{u}) :
    IsPartialCollapseGraph
      (maximalPartialCollapseGraph domain target) domain target := by
  let maximal := maximalPartialCollapseGraph domain target
  refine ⟨?_, ?_, ?_⟩
  · intro pair hpair
    rcases (mem_maximalPartialCollapseGraph_iff domain target pair).mp hpair with
      ⟨graph, hgraph, hpairGraph⟩
    exact hgraph.graphBetween pair hpairGraph
  · intro x y hxy z hzX hzDomain
    rcases hxy with ⟨pair, hpairMaximal, hpairXY⟩
    rcases (mem_maximalPartialCollapseGraph_iff domain target pair).mp
        hpairMaximal with ⟨graph, hgraph, hpairGraph⟩
    have hxyGraph : GraphValue LMem graph x y :=
      ⟨pair, hpairGraph, hpairXY⟩
    rcases hgraph.predecessor x y hxyGraph z hzX hzDomain with
      ⟨value, hvalueTarget, hzValue⟩
    exact ⟨value, hvalueTarget,
      graphValue_maximal_of_graphValue hgraph hzValue⟩
  · intro x y hxy value
    rcases hxy with ⟨pair, hpairMaximal, hpairXY⟩
    rcases (mem_maximalPartialCollapseGraph_iff domain target pair).mp
        hpairMaximal with ⟨graph, hgraph, hpairGraph⟩
    have hxyGraph : GraphValue LMem graph x y :=
      ⟨pair, hpairGraph, hpairXY⟩
    constructor
    · intro hvalueY
      rcases (hgraph.recursion x y hxyGraph value).mp hvalueY with
        ⟨z, hzX, hzDomain, hzValue⟩
      exact ⟨z, hzX, hzDomain,
        graphValue_maximal_of_graphValue hgraph hzValue⟩
    · rintro ⟨z, hzX, hzDomain, hzValueMaximal⟩
      have hyCollapse := hgraph.value_eq_collapse x y hxyGraph
      have hvalueCollapse :=
        graphValue_maximal_eq_collapse hzValueMaximal
      rw [hyCollapse]
      exact MostowskiCollapse.mem_collapse_iff.mpr
        ⟨z.1, hzX, hzDomain, hvalueCollapse.symm⟩

/-! ## Extending a partial graph at one point -/

/-- Insert the Kuratowski pair `(x,y)` into a constructible graph. -/
def insertGraphValue
    (graph x y : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier
    (pairLCarrier (orderedPairLCarrier x y) (orderedPairLCarrier x y))
    graph

@[simp]
theorem mem_insertGraphValue_iff
    (graph x y pair : LCarrier.{u}) :
    pair.1 ∈ (insertGraphValue graph x y).1 <->
      pair = orderedPairLCarrier x y \/ pair.1 ∈ graph.1 := by
  rw [insertGraphValue, mem_unionLCarrier_iff,
    mem_pairLCarrier_iff]
  simp only [or_self]

@[simp]
theorem graphValue_insertGraphValue_iff
    (graph x y a b : LCarrier.{u}) :
    GraphValue LMem (insertGraphValue graph x y) a b <->
      GraphValue LMem graph a b \/ (a = x /\ b = y) := by
  constructor
  · rintro ⟨pair, hpair, hpairAB⟩
    rcases (mem_insertGraphValue_iff graph x y pair).mp hpair with
      hnew | hold
    · right
      have hpairNew : pair = orderedPairLCarrier x y := hnew
      have hab := (isKuratowskiPairOf_lCarrier_iff pair a b).mp hpairAB
      rw [hpairNew] at hab
      have habRaw : ZFSet.pair x.1 y.1 = ZFSet.pair a.1 b.1 := by
        simpa only [orderedPairLCarrier_val] using hab
      have hcoordinates := ZFSet.pair_inj.mp habRaw
      exact ⟨Subtype.ext hcoordinates.1.symm,
        Subtype.ext hcoordinates.2.symm⟩
    · exact Or.inl ⟨pair, hold, hpairAB⟩
  · rintro (hold | hnew)
    · rcases hold with ⟨pair, hpair, hpairXY⟩
      exact ⟨pair,
        (mem_insertGraphValue_iff graph x y pair).mpr (Or.inr hpair),
        hpairXY⟩
    · rcases hnew with ⟨ha, hb⟩
      subst a
      subst b
      let pair := orderedPairLCarrier x y
      exact ⟨pair,
        (mem_insertGraphValue_iff graph x y pair).mpr
          (Or.inl rfl),
        (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl⟩

/--
If every restricted predecessor of `x` already has a value, adjoining the
correct value at `x` preserves the partial-collapse recursion.
-/
theorem IsPartialCollapseGraph.insert_correct_value
    {graph domain target x y : LCarrier.{u}}
    (hgraph : IsPartialCollapseGraph graph domain target)
    (hxDomain : x.1 ∈ domain.1)
    (hyTarget : y.1 ∈ target.1)
    (hyCollapse : y.1 = MostowskiCollapse.collapse domain.1 x.1)
    (hpredecessors : forall z : LCarrier.{u},
      z.1 ∈ x.1 -> z.1 ∈ domain.1 ->
        exists value : LCarrier.{u}, GraphValue LMem graph z value) :
    IsPartialCollapseGraph (insertGraphValue graph x y) domain target := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hpair
    rcases (mem_insertGraphValue_iff graph x y pair).mp hpair with
      hnew | hold
    · subst pair
      exact ⟨x, hxDomain, y, hyTarget,
        (isKuratowskiPairOf_lCarrier_iff
          (orderedPairLCarrier x y) x y).mpr rfl⟩
    · exact hgraph.graphBetween pair hold
  · intro a b hab z hzA hzDomain
    rcases (graphValue_insertGraphValue_iff graph x y a b).mp hab with
      hold | ⟨ha, _hb⟩
    · rcases hgraph.predecessor a b hold z hzA hzDomain with
        ⟨value, hvalueTarget, hzValue⟩
      exact ⟨value, hvalueTarget,
        (graphValue_insertGraphValue_iff graph x y z value).mpr
          (Or.inl hzValue)⟩
    · subst a
      rcases hpredecessors z hzA hzDomain with ⟨value, hzValue⟩
      have hvalueTarget :=
        (hgraph.graphBetween.graphValue_mem_lCarrier hzValue).2
      exact ⟨value, hvalueTarget,
        (graphValue_insertGraphValue_iff graph x y z value).mpr
          (Or.inl hzValue)⟩
  · intro a b hab value
    rcases (graphValue_insertGraphValue_iff graph x y a b).mp hab with
      hold | ⟨ha, hb⟩
    · constructor
      · intro hvalueB
        rcases (hgraph.recursion a b hold value).mp hvalueB with
          ⟨z, hzA, hzDomain, hzValue⟩
        exact ⟨z, hzA, hzDomain,
          (graphValue_insertGraphValue_iff graph x y z value).mpr
            (Or.inl hzValue)⟩
      · rintro ⟨z, hzA, hzDomain, hzValue⟩
        rcases (graphValue_insertGraphValue_iff graph x y z value).mp
            hzValue with hzOld | ⟨hzX, hvalueY⟩
        · exact (hgraph.recursion a b hold value).mpr
            ⟨z, hzA, hzDomain, hzOld⟩
        · subst z
          subst value
          rcases hgraph.predecessor a b hold x hzA hxDomain with
            ⟨oldValue, _holdTarget, hxOldValue⟩
          have holdEq := hgraph.value_eq_collapse x oldValue hxOldValue
          have holdY : oldValue = y := by
            apply Subtype.ext
            exact holdEq.trans hyCollapse.symm
          subst oldValue
          exact (hgraph.recursion a b hold y).mpr
            ⟨x, hzA, hxDomain, hxOldValue⟩
    · subst a
      subst b
      constructor
      · intro hvalueY
        rw [hyCollapse] at hvalueY
        rcases MostowskiCollapse.mem_collapse_iff.mp hvalueY with
          ⟨zRaw, hzX, hzDomain, hzCollapse⟩
        let z : LCarrier.{u} :=
          ⟨zRaw, mem_L_of_mem hzDomain domain.2⟩
        rcases hpredecessors z hzX hzDomain with ⟨image, hzImage⟩
        have himageCollapse :=
          hgraph.value_eq_collapse z image hzImage
        have himageValue : image.1 = value.1 :=
          himageCollapse.trans hzCollapse
        have himageEq : image = value := Subtype.ext himageValue
        subst image
        exact ⟨z, hzX, hzDomain,
          (graphValue_insertGraphValue_iff graph x y z value).mpr
            (Or.inl hzImage)⟩
      · rintro ⟨z, hzX, hzDomain, hzValue⟩
        rcases (graphValue_insertGraphValue_iff graph x y z value).mp
            hzValue with hzOld | ⟨hzEq, hvalueEq⟩
        · have hvalueCollapse :=
            hgraph.value_eq_collapse z value hzOld
          rw [hyCollapse]
          exact MostowskiCollapse.mem_collapse_iff.mpr
            ⟨z.1, hzX, hzDomain, hvalueCollapse.symm⟩
        · subst z
          subst value
          exact (ZFSet.mem_irrefl x.1 hzX).elim

/-! ## Totality of the maximal graph -/

/--
Once the external collapse range is represented by `target`, the maximal
partial graph has a value at every member of `domain`.
-/
theorem maximalPartialCollapseGraph_total
    (domain target : LCarrier.{u})
    (htarget : target.1 = MostowskiCollapse.range domain.1) :
    forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
      exists y : LCarrier.{u},
        y.1 ∈ target.1 /\
          y.1 = MostowskiCollapse.collapse domain.1 x.1 /\
            GraphValue LMem
              (maximalPartialCollapseGraph domain target) x y := by
  intro x
  refine ZFSet.inductionOn
    (p := fun xRaw => forall (hxL : xRaw ∈ L), xRaw ∈ domain.1 ->
      exists y : LCarrier.{u},
        y.1 ∈ target.1 /\
          y.1 = MostowskiCollapse.collapse domain.1 xRaw /\
            GraphValue LMem
              (maximalPartialCollapseGraph domain target)
              ⟨xRaw, hxL⟩ y)
    x.1 ?_ x.2
  intro xRaw ih hxL hxDomain
  have hcollapseTarget :
      MostowskiCollapse.collapse domain.1 xRaw ∈ target.1 := by
    rw [htarget]
    exact MostowskiCollapse.mem_range_iff.mpr
      ⟨xRaw, hxDomain, rfl⟩
  let xL : LCarrier.{u} := ⟨xRaw, hxL⟩
  let y : LCarrier.{u} :=
    ⟨MostowskiCollapse.collapse domain.1 xRaw,
      mem_L_of_mem hcollapseTarget target.2⟩
  have hpredecessors : forall z : LCarrier.{u},
      z.1 ∈ xL.1 -> z.1 ∈ domain.1 ->
        exists value : LCarrier.{u},
          GraphValue LMem
            (maximalPartialCollapseGraph domain target) z value := by
    intro z hzX hzDomain
    rcases ih z.1 hzX z.2 hzDomain with
      ⟨value, _hvalueTarget, _hvalueCollapse, hzValue⟩
    exact ⟨value, hzValue⟩
  have hextension : IsPartialCollapseGraph
      (insertGraphValue
        (maximalPartialCollapseGraph domain target) xL y)
      domain target :=
    (maximalPartialCollapseGraph_isPartial domain target).insert_correct_value
      hxDomain hcollapseTarget rfl hpredecessors
  let pair := orderedPairLCarrier xL y
  have hpairExtension : pair.1 ∈
      (insertGraphValue
        (maximalPartialCollapseGraph domain target) xL y).1 :=
    (mem_insertGraphValue_iff
      (maximalPartialCollapseGraph domain target) xL y pair).mpr
      (Or.inl rfl)
  have hpairMaximal : pair.1 ∈
      (maximalPartialCollapseGraph domain target).1 :=
    (mem_maximalPartialCollapseGraph_iff domain target pair).mpr
      ⟨insertGraphValue
          (maximalPartialCollapseGraph domain target) xL y,
        hextension, hpairExtension⟩
  refine ⟨y, hcollapseTarget, rfl, ?_⟩
  exact ⟨pair, hpairMaximal,
    (isKuratowskiPairOf_lCarrier_iff pair xL y).mpr rfl⟩

/-- The maximal partial graph is extensionally the external collapse graph. -/
theorem maximalPartialCollapseGraph_eq_graph
    (domain target : LCarrier.{u})
    (htarget : target.1 = MostowskiCollapse.range domain.1) :
    (maximalPartialCollapseGraph domain target).1 =
      MostowskiCollapse.graph domain.1 := by
  apply ZFSet.ext
  intro pairRaw
  constructor
  · intro hpairMaximal
    let pair : LCarrier.{u} :=
      ⟨pairRaw,
        mem_L_of_mem hpairMaximal
          (maximalPartialCollapseGraph domain target).2⟩
    have hpartial := maximalPartialCollapseGraph_isPartial domain target
    rcases hpartial.graphBetween pair hpairMaximal with
      ⟨x, hxDomain, y, _hyTarget, hpairXY⟩
    have hxy : GraphValue LMem
        (maximalPartialCollapseGraph domain target) x y :=
      ⟨pair, hpairMaximal, hpairXY⟩
    have hyCollapse := hpartial.value_eq_collapse x y hxy
    have hpairEq :=
      (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY
    change pairRaw = ZFSet.pair x.1 y.1 at hpairEq
    apply MostowskiCollapse.mem_graph_iff.mpr
    refine ⟨x.1, hxDomain, ?_⟩
    calc
      ZFSet.pair x.1 (MostowskiCollapse.collapse domain.1 x.1) =
          ZFSet.pair x.1 y.1 := congrArg (ZFSet.pair x.1) hyCollapse.symm
      _ = pairRaw := hpairEq.symm
  · intro hpairGraph
    rcases MostowskiCollapse.mem_graph_iff.mp hpairGraph with
      ⟨xRaw, hxDomain, hpairEq⟩
    let x : LCarrier.{u} :=
      ⟨xRaw, mem_L_of_mem hxDomain domain.2⟩
    rcases maximalPartialCollapseGraph_total domain target htarget x hxDomain with
      ⟨y, _hyTarget, hyCollapse, hxy⟩
    rcases hxy with ⟨pair, hpairMaximal, hpairXY⟩
    have hpairXYEq :=
      (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY
    have hpairRawEq : pair.1 = pairRaw := by
      calc
        pair.1 = ZFSet.pair x.1 y.1 := hpairXYEq
        _ = ZFSet.pair xRaw
            (MostowskiCollapse.collapse domain.1 xRaw) := by
              rw [hyCollapse]
        _ = pairRaw := hpairEq
    rw [← hpairRawEq]
    exact hpairMaximal

/--
If the collapse range of a constructible domain is constructible, then its
entire external collapse (range and exact Kuratowski graph) is internalized in
`L`.  Extensionality is not needed for this construction; it is needed only
later when the graph is used as a bijection.
-/
theorem exists_internalizedCollapse_of_range_mem_L
    (domain : LCarrier.{u})
    (hrange : MostowskiCollapse.range domain.1 ∈ L) :
    exists _witness : InternalizedCollapse domain, True := by
  let target : LCarrier.{u} :=
    ⟨MostowskiCollapse.range domain.1, hrange⟩
  have hgraphEq :
      (maximalPartialCollapseGraph domain target).1 =
        MostowskiCollapse.graph domain.1 :=
    maximalPartialCollapseGraph_eq_graph domain target rfl
  have hgraph : MostowskiCollapse.graph domain.1 ∈ L := by
    rw [← hgraphEq]
    exact (maximalPartialCollapseGraph domain target).2
  exact ⟨InternalizedCollapse.of_mem domain hrange hgraph, trivial⟩

end Model

namespace MostowskiCollapse

open Constructible.Model

/-! ## Condensation hulls -/

/-- Condensation makes the external collapse range of its hull constructible. -/
theorem CondensationHull.collapseRange_mem_L
    {theta : Ordinal.{u}} {domain : Model.LCarrier.{u}}
    (h : CondensationHull theta domain.1) :
    range domain.1 ∈ L := by
  rw [h.condensation]
  exact (Model.stageLCarrier (ordinalHeight (range domain.1))).2

/--
The collapse of a constructible fully elementary condensation hull has both
its range and its exact collapse graph represented by members of `L`.
-/
theorem CondensationHull.exists_internalizedCollapse
    {theta : Ordinal.{u}} {domain : Model.LCarrier.{u}}
    (h : CondensationHull theta domain.1) :
    exists _witness : Model.InternalizedCollapse domain, True :=
  Model.exists_internalizedCollapse_of_range_mem_L domain
    h.collapseRange_mem_L

/-- Named non-method form for downstream construction of controlled hulls. -/
theorem exists_internalizedCollapse_of_condensationHull
    {theta : Ordinal.{u}} {domain : Model.LCarrier.{u}}
    (h : CondensationHull theta domain.1) :
    exists _witness : Model.InternalizedCollapse domain, True :=
  h.exists_internalizedCollapse

/--
Raw full-elementarity interface.  The fixed evaluator parameters are derived
by `CondensationHull.of_elementary`; they are not additional assumptions.
-/
theorem exists_internalizedCollapse_of_elementary_at_reflectionLevel
    {theta : Ordinal.{u}} {domain : Model.LCarrier.{u}}
    (hreflection : Model.IsCondensationReflectionLevel theta)
    (hsubset : domain.1 ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute
      (domain.1 : Set ZFSet.{u}) (LStageZF theta : Set ZFSet.{u})) :
    exists _witness : Model.InternalizedCollapse domain, True :=
  (CondensationHull.of_elementary hreflection hsubset helem).exists_internalizedCollapse

end MostowskiCollapse

end Constructible
