/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph

/-!
# Internally represented injections for indexed unions

This file isolates the graph-theoretic core of the cardinal union argument.
All functions in the statement are represented by actual constructible sets.
In particular, the family of fiber injections is an input graph rather than
an ambient choice function.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-- A total internally represented function graph. -/
def IsFunctionGraph {A : Type u} (E : A -> A -> Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain /\
    forall x : A, E x domain -> HasUniqueImage E graph x codomain

theorem IsInjection.toIsFunctionGraph
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    IsFunctionGraph E graph domain codomain :=
  ⟨h.1, h.2.1⟩

theorem IsFunctionGraph.graphValue_unique
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain x y z : A}
    (h : IsFunctionGraph E graph domain codomain)
    (hx : E x domain) (hy : E y codomain) (hz : E z codomain)
    (hxy : GraphValue E graph x y) (hxz : GraphValue E graph x z) :
    y = z := by
  rcases h.2 x hx with ⟨value, hvalue, hxvalue, hunique⟩
  exact (hunique y hy hxy).trans (hunique z hz hxz).symm

/-- The semantic relation which combines a selected fiber index with the
value of the selected fiber injection. -/
def CardinalUnionRel {A : Type u} (E : A -> A -> Prop)
    (selector indexedFamily injectionFamily x output : A) : Prop :=
  exists index fiber injection value : A,
    GraphValue E selector x index /\
      GraphValue E indexedFamily index fiber /\
        GraphValue E injectionFamily index injection /\
          GraphValue E injection x value /\
            IsKuratowskiPairOf E output index value

/-- Layout `[selector,indexedFamily,injectionFamily,x,output]`.
The four witnesses are respectively the chosen index, its fiber, the
fiber-injection graph, and the image value. -/
def cardinalUnionPredicate : FOFormula 5 :=
  .ex (.ex (.ex (.ex
    (.conj
      (graphValueAt (0 : Fin 9) (3 : Fin 9) (5 : Fin 9))
      (.conj
        (graphValueAt (1 : Fin 9) (5 : Fin 9) (6 : Fin 9))
        (.conj
          (graphValueAt (2 : Fin 9) (5 : Fin 9) (7 : Fin 9))
          (.conj
            (graphValueAt (7 : Fin 9) (3 : Fin 9) (8 : Fin 9))
            (kuratowskiPairAt
              (4 : Fin 9) (5 : Fin 9) (8 : Fin 9)))))))))

private theorem cardinalUnion_assignment
    (selector indexedFamily injectionFamily x output
      index fiber injection value : Constructible.Model.LCarrier.{u}) :
    snoc (snoc (snoc (snoc
      ![selector, indexedFamily, injectionFamily, x, output]
      index) fiber) injection) value =
      ![selector, indexedFamily, injectionFamily, x, output,
        index, fiber, injection, value] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cardinalUnionPredicate
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cardinalUnionPredicate
      ![selector, indexedFamily, injectionFamily, x, output] <->
      CardinalUnionRel Constructible.Model.lCarrierMem
        selector indexedFamily injectionFamily x output := by
  simp only [cardinalUnionPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt, satisfies_kuratowskiPairAt,
    CardinalUnionRel]
  apply exists_congr
  intro index
  apply exists_congr
  intro fiber
  apply exists_congr
  intro injection
  apply exists_congr
  intro value
  rw [cardinalUnion_assignment]
  rfl

private theorem cardinalUnion_relation_assignment
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![selector, indexedFamily, injectionFamily] x) output =
      ![selector, indexedFamily, injectionFamily, x, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cardinalUnionRelation
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cardinalUnionPredicate
      (snoc (snoc ![selector, indexedFamily, injectionFamily] x) output) <->
      CardinalUnionRel Constructible.Model.lCarrierMem
        selector indexedFamily injectionFamily x output := by
  rw [cardinalUnion_relation_assignment,
    satisfies_cardinalUnionPredicate]

/-! ## Conditional internal family interfaces -/

/-- A selector assigns to each member of a union an index of a fiber which
contains it. -/
def SelectsContainingFiber {A : Type u} (E : A -> A -> Prop)
    (selector union index indexedFamily : A) : Prop :=
  IsFunctionGraph E selector union index /\
    forall x i : A, E x union -> GraphValue E selector x i ->
      exists fiber : A,
        GraphValue E indexedFamily i fiber /\ E x fiber

/-- `injectionFamily` assigns to each index a graph injecting the
corresponding fiber into `kappa`.  Both assignments are internal graphs. -/
def IsFiberInjectionFamily {A : Type u} (E : A -> A -> Prop)
    (indexedFamily injectionFamily index family graphFamily kappa : A) : Prop :=
  IsFunctionGraph E indexedFamily index family /\
    IsFunctionGraph E injectionFamily index graphFamily /\
      forall i fiber injection : A, E i index ->
        GraphValue E indexedFamily i fiber ->
          GraphValue E injectionFamily i injection ->
            IsInjection E injection fiber kappa

theorem CardinalUnionRel.mem_sUnion_prod_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa
      x output : Constructible.Model.LCarrier.{u}}
    (hselector : IsFunctionGraph Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa)
    (hrel : CardinalUnionRel Constructible.Model.lCarrierMem
      selector indexedFamily injectionFamily x output) :
    x.1 ∈ (Constructible.Model.sUnionLCarrier family).1 /\
      output.1 ∈ (Constructible.Model.prodLCarrier index kappa).1 := by
  rcases hrel with
    ⟨i, fiber, injection, value, hselect, hfiber, hinjection,
      hvalue, houtput⟩
  have hxUnion := (hselector.1.graphValue_mem_lCarrier hselect).1
  have hiIndex := (hselector.1.graphValue_mem_lCarrier hselect).2
  have hinjects := hfamilies.2.2 i fiber injection
    hiIndex hfiber hinjection
  have hvalueKappa :=
    (hinjects.1.graphValue_mem_lCarrier hvalue).2
  have houtputRaw :=
    (isKuratowskiPairOf_lCarrier_iff output i value).mp houtput
  refine ⟨hxUnion, ?_⟩
  change output.1 ∈ ZFSet.prod index.1 kappa.1
  rw [houtputRaw, ZFSet.pair_mem_prod]
  exact ⟨hiIndex, hvalueKappa⟩

/-- The combined relation has a constructible graph supported on the union
and the internal Cartesian product. -/
theorem exists_cardinalUnionGraph_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa :
      Constructible.Model.LCarrier.{u}}
    (hselector : IsFunctionGraph Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa) :
    exists graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph
        (Constructible.Model.sUnionLCarrier family)
        (Constructible.Model.prodLCarrier index kappa) /\
        forall x output : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x output <->
            CardinalUnionRel Constructible.Model.lCarrierMem
              selector indexedFamily injectionFamily x output := by
  let domain := Constructible.Model.sUnionLCarrier family
  let codomain := Constructible.Model.prodLCarrier index kappa
  let container := unionLCarrier domain codomain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      cardinalUnionPredicate ![selector, indexedFamily, injectionFamily]
      container with
    ⟨graph, hsupport, hgraph⟩
  have hvalue : forall x output : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x output <->
        CardinalUnionRel Constructible.Model.lCarrierMem
          selector indexedFamily injectionFamily x output := by
    intro x output
    rw [graphValue_lCarrier_iff_graphRel, hgraph]
    constructor
    · rintro ⟨_hxContainer, _houtputContainer, hformula⟩
      exact (satisfies_cardinalUnionRelation
        selector indexedFamily injectionFamily x output).mp hformula
    · intro hrel
      have hmem := CardinalUnionRel.mem_sUnion_prod_lCarrier
        hselector hfamilies hrel
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff domain codomain x).mpr
          (Or.inl hmem.1)
      · exact (mem_unionLCarrier_iff domain codomain output).mpr
          (Or.inr hmem.2)
      · exact (satisfies_cardinalUnionRelation
          selector indexedFamily injectionFamily x output).mpr hrel
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, output, _hxContainer, _houtputContainer, hpairEq, hformula⟩
  have hrel := (satisfies_cardinalUnionRelation
    selector indexedFamily injectionFamily x output).mp hformula
  have hmem := CardinalUnionRel.mem_sUnion_prod_lCarrier
    hselector hfamilies hrel
  exact ⟨x, hmem.1, output, hmem.2,
    (isKuratowskiPairOf_lCarrier_iff pair x output).mpr hpairEq⟩

/-- An internally selected family of internal fiber injections combines to
an internal injection from the union into `index x kappa`. -/
theorem injects_sUnion_to_prod_lCarrier
    {selector indexedFamily injectionFamily index family graphFamily kappa :
      Constructible.Model.LCarrier.{u}}
    (hselector : SelectsContainingFiber Constructible.Model.lCarrierMem
      selector (Constructible.Model.sUnionLCarrier family) index indexedFamily)
    (hfamilies : IsFiberInjectionFamily Constructible.Model.lCarrierMem
      indexedFamily injectionFamily index family graphFamily kappa) :
    Injects Constructible.Model.lCarrierMem
      (Constructible.Model.sUnionLCarrier family)
      (Constructible.Model.prodLCarrier index kappa) := by
  rcases exists_cardinalUnionGraph_lCarrier hselector.1 hfamilies with
    ⟨combined, hbetween, hvalue⟩
  refine ⟨combined, hbetween, ?_, ?_⟩
  · intro x hxUnion
    rcases hselector.1.2 x hxUnion with
      ⟨i, hiIndex, hselect, _hiUnique⟩
    rcases hfamilies.1.2 i hiIndex with
      ⟨fiber, hfiberFamily, hindexed, _hfiberUnique⟩
    rcases hfamilies.2.1.2 i hiIndex with
      ⟨injection, hinjectionGraphFamily, hinjectionAt,
        _hinjectionUnique⟩
    rcases hselector.2 x i hxUnion hselect with
      ⟨selectedFiber, hselectedFiber, hxSelectedFiber⟩
    have hselectedFiberFamily :=
      (hfamilies.1.1.graphValue_mem_lCarrier hselectedFiber).2
    have hselectedEq : selectedFiber = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hselectedFiberFamily hfiberFamily hselectedFiber hindexed
    subst selectedFiber
    have hinjects := hfamilies.2.2 i fiber injection
      hiIndex hindexed hinjectionAt
    rcases hinjects.2.1 x hxSelectedFiber with
      ⟨value, hvalueKappa, hxvalue, _hvalueUnique⟩
    let output := Constructible.Model.orderedPairLCarrier i value
    have houtputProduct :
        output.1 ∈ (Constructible.Model.prodLCarrier index kappa).1 := by
      change ZFSet.pair i.1 value.1 ∈ ZFSet.prod index.1 kappa.1
      rw [ZFSet.pair_mem_prod]
      exact ⟨hiIndex, hvalueKappa⟩
    have houtputPair :
        IsKuratowskiPairOf Constructible.Model.lCarrierMem output i value :=
      (isKuratowskiPairOf_lCarrier_iff output i value).mpr rfl
    refine ⟨output, houtputProduct,
      (hvalue x output).mpr
        ⟨i, fiber, injection, value, hselect, hindexed,
          hinjectionAt, hxvalue, houtputPair⟩, ?_⟩
    intro other hotherProduct hxother
    rcases (hvalue x other).mp hxother with
      ⟨i', fiber', injection', value', hselect', hindexed',
        hinjectionAt', hxvalue', hotherPair⟩
    have hi'Index :=
      (hselector.1.1.graphValue_mem_lCarrier hselect').2
    have hiEq : i' = i :=
      hselector.1.graphValue_unique hxUnion
        hi'Index hiIndex hselect' hselect
    subst i'
    have hfiber'Family :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexed').2
    have hfiberEq : fiber' = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hfiber'Family hfiberFamily hindexed' hindexed
    subst fiber'
    have hinjection'GraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionAt').2
    have hinjectionEq : injection' = injection :=
      hfamilies.2.1.graphValue_unique hiIndex
        hinjection'GraphFamily hinjectionGraphFamily
        hinjectionAt' hinjectionAt
    subst injection'
    have hvalue'Kappa :=
      (hinjects.1.graphValue_mem_lCarrier hxvalue').2
    have hvalueEq : value' = value :=
      hinjects.toIsFunctionGraph.graphValue_unique hxSelectedFiber
        hvalue'Kappa hvalueKappa hxvalue' hxvalue
    subst value'
    apply Subtype.ext
    simpa only [output, Constructible.Model.orderedPairLCarrier_val] using
      (isKuratowskiPairOf_lCarrier_iff other i value).mp hotherPair
  · intro output houtputProduct x hxUnion hxoutput z hzUnion hzoutput
    rcases (hvalue x output).mp hxoutput with
      ⟨i, fiber, injection, value, hselectX, hindexedI,
        hinjectionI, hxvalue, houtputI⟩
    rcases (hvalue z output).mp hzoutput with
      ⟨j, fiber', injection', value', hselectZ, hindexedJ,
        hinjectionJ, hzvalue, houtputJ⟩
    have hpairI :=
      (isKuratowskiPairOf_lCarrier_iff output i value).mp houtputI
    have hpairJ :=
      (isKuratowskiPairOf_lCarrier_iff output j value').mp houtputJ
    have hcoordinates := ZFSet.pair_inj.mp (hpairI.symm.trans hpairJ)
    have hij : i = j := Subtype.ext hcoordinates.1
    have hvalues : value = value' := Subtype.ext hcoordinates.2
    subst j
    subst value'
    have hiIndex :=
      (hselector.1.1.graphValue_mem_lCarrier hselectX).2
    have hfiberFamily :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexedI).2
    have hfiber'Family :=
      (hfamilies.1.1.graphValue_mem_lCarrier hindexedJ).2
    have hfiberEq : fiber' = fiber :=
      hfamilies.1.graphValue_unique hiIndex
        hfiber'Family hfiberFamily hindexedJ hindexedI
    subst fiber'
    have hinjectionGraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionI).2
    have hinjection'GraphFamily :=
      (hfamilies.2.1.1.graphValue_mem_lCarrier hinjectionJ).2
    have hinjectionEq : injection' = injection :=
      hfamilies.2.1.graphValue_unique hiIndex
        hinjection'GraphFamily hinjectionGraphFamily
        hinjectionJ hinjectionI
    subst injection'
    have hinjects := hfamilies.2.2 i fiber injection
      hiIndex hindexedI hinjectionI
    have hxFiber := (hinjects.1.graphValue_mem_lCarrier hxvalue).1
    have hzFiber := (hinjects.1.graphValue_mem_lCarrier hzvalue).1
    have hvalueKappa :=
      (hinjects.1.graphValue_mem_lCarrier hxvalue).2
    exact hinjects.2.2 value hvalueKappa
      x hxFiber hxvalue z hzFiber hzvalue

end Constructible.ContinuumFormula
