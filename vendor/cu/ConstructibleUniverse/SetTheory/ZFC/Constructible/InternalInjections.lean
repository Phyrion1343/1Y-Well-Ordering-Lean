/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Hartogs

/-!
# Internally represented injections in the constructible universe

This file develops the elementary algebra of injection graphs whose graph is
itself an element of `L`.  In particular, inverse and composite graphs are
obtained by Separation from fixed first-order definitions.  No ambient
function is used as a witness for an internal injection.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-! ## Absoluteness of Kuratowski graph semantics -/

theorem isKuratowskiPairOf_lCarrier_iff
    (pair x y : Constructible.Model.LCarrier.{u}) :
    IsKuratowskiPairOf Constructible.Model.lCarrierMem pair x y ↔
      pair.1 = ZFSet.pair x.1 y.1 := by
  have hsemantic := satisfies_kuratowskiPairAt
    Constructible.Model.lCarrierMem
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) ![pair, x, y]
  have hraw :=
    Constructible.DefinableRelationGraph.satisfies_pairEq_lCarrier
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) ![pair, x, y]
  rw [show kuratowskiPairAt
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) =
        (Delta0Formula.kuratowskiPairEqAt
          (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)).toFO from rfl]
      at hsemantic
  exact hsemantic.symm.trans hraw

@[simp]
theorem graphValue_lCarrier_iff_graphRel
    (graph x y : Constructible.Model.LCarrier.{u}) :
    GraphValue Constructible.Model.lCarrierMem graph x y ↔
      Constructible.Model.GraphRel graph x y := by
  constructor
  · rintro ⟨pair, hpairGraph, hpair⟩
    rw [Constructible.Model.GraphRel]
    rw [← (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpair]
    exact hpairGraph
  · intro hgraph
    let pair := Constructible.Model.orderedPairLCarrier x y
    refine ⟨pair, hgraph, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl

theorem IsGraphBetween.graphValue_mem_lCarrier
    {graph domain codomain x y : Constructible.Model.LCarrier.{u}}
    (h : IsGraphBetween Constructible.Model.lCarrierMem
      graph domain codomain)
    (hvalue : GraphValue Constructible.Model.lCarrierMem graph x y) :
    x.1 ∈ domain.1 ∧ y.1 ∈ codomain.1 := by
  rcases hvalue with ⟨pair, hpairGraph, hpairXY⟩
  rcases h pair hpairGraph with
    ⟨x', hx', y', hy', hpairXY'⟩
  have hraw : ZFSet.pair x.1 y.1 = ZFSet.pair x'.1 y'.1 :=
    ((isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY).symm.trans
      ((isKuratowskiPairOf_lCarrier_iff pair x' y').mp hpairXY')
  have hcoordinates := ZFSet.pair_inj.mp hraw
  have hx : x = x' := Subtype.ext hcoordinates.1
  have hy : y = y' := Subtype.ext hcoordinates.2
  simpa only [hx, hy] using And.intro hx' hy'

/-! ## Definable identity, converse, and composition graphs -/

/-- The binary union, packaged as an element of `L`. -/
def unionLCarrier
    (x y : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  ⟨x.1 ∪ y.1, Constructible.union_mem_L x.2 y.2⟩

@[simp]
theorem mem_unionLCarrier_iff
    (x y z : Constructible.Model.LCarrier.{u}) :
    z.1 ∈ (unionLCarrier x y).1 ↔ z.1 ∈ x.1 ∨ z.1 ∈ y.1 := by
  simp [unionLCarrier]

def identityGraphPredicate : FOFormula 2 :=
  .eq (0 : Fin 2) (1 : Fin 2)

private theorem identityGraph_assignment
    (x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y = ![x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_identityGraphPredicate
    (x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      identityGraphPredicate
      (snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y) ↔
        x = y := by
  rw [identityGraph_assignment]
  rfl

def converseGraphPredicate : FOFormula 3 :=
  graphValueAt (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)

private theorem converseGraph_assignment
    (graph x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![graph] x) y = ![graph, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_converseGraphPredicate
    (graph x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      converseGraphPredicate (snoc (snoc ![graph] x) y) ↔
        GraphValue Constructible.Model.lCarrierMem graph y x := by
  rw [converseGraph_assignment]
  exact satisfies_graphValueAt
    Constructible.Model.lCarrierMem
      (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) ![graph, x, y]

def compositionGraphPredicate : FOFormula 4 :=
  .ex (.conj
    (graphValueAt
      (0 : Fin 4).castSucc (2 : Fin 4).castSucc (Fin.last 4))
    (graphValueAt
      (1 : Fin 4).castSucc (Fin.last 4) (3 : Fin 4).castSucc))

private theorem compositionGraph_assignment
    (first second x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![first, second] x) y = ![first, second, x, y] := by
  funext i
  fin_cases i <;> rfl

private theorem compositionGraph_witness_assignment
    (first second x y z : Constructible.Model.LCarrier.{u}) :
    snoc ![first, second, x, y] z = ![first, second, x, y, z] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_compositionGraphPredicate
    (first second x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      compositionGraphPredicate
      (snoc (snoc ![first, second] x) y) ↔
        ∃ middle : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem first x middle ∧
            GraphValue Constructible.Model.lCarrierMem second middle y := by
  rw [compositionGraph_assignment]
  simp only [compositionGraphPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt]
  apply exists_congr
  intro z
  rw [compositionGraph_witness_assignment]
  rfl

theorem exists_identityGraph_lCarrier
    (domain : Constructible.Model.LCarrier.{u}) :
    ∃ graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem graph domain domain ∧
        ∀ x y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y ↔
            x.1 ∈ domain.1 ∧ y = x := by
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      identityGraphPredicate
      (fun i : Fin 0 => Fin.elim0 i) domain with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        x.1 ∈ domain.1 ∧ y = x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨hx, _hy, hxy⟩
      exact ⟨hx, (satisfies_identityGraphPredicate x y).mp hxy |>.symm⟩
    · rintro ⟨hx, hxy⟩
      subst y
      exact ⟨hx, hx, (satisfies_identityGraphPredicate x x).mpr rfl⟩
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, hx, hy, hpairEq, hxy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq

theorem injects_refl_lCarrier
    (domain : Constructible.Model.LCarrier.{u}) :
    Injects Constructible.Model.lCarrierMem domain domain := by
  rcases exists_identityGraph_lCarrier domain with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hx
    refine ⟨x, hx, (hvalue x x).mpr ⟨hx, rfl⟩, ?_⟩
    intro z _hz hzValue
    exact (hvalue x z).mp hzValue |>.2
  · intro y _hy x hx hxy z hz hzy
    have hyx : y = x := (hvalue x y).mp hxy |>.2
    have hyz : y = z := (hvalue z y).mp hzy |>.2
    exact hyz.symm.trans hyx

theorem injects_of_subset_lCarrier
    {domain codomain : Constructible.Model.LCarrier.{u}}
    (hsubset : ∀ x : Constructible.Model.LCarrier.{u},
      x.1 ∈ domain.1 → x.1 ∈ codomain.1) :
    Injects Constructible.Model.lCarrierMem domain codomain := by
  rcases exists_identityGraph_lCarrier domain with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, ?_, ?_, ?_⟩
  · intro pair hpair
    rcases hbetween pair hpair with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hsubset y hy, hxy⟩
  · intro x hx
    refine ⟨x, hsubset x hx, (hvalue x x).mpr ⟨hx, rfl⟩, ?_⟩
    intro z _hz hzValue
    exact (hvalue x z).mp hzValue |>.2
  · intro y _hy x hx hxy z hz hzy
    have hyx : y = x := (hvalue x y).mp hxy |>.2
    have hyz : y = z := (hvalue z y).mp hzy |>.2
    exact hyz.symm.trans hyx

theorem exists_compositionGraph_lCarrier
    {first second domain middle codomain :
      Constructible.Model.LCarrier.{u}}
    (hfirst : IsGraphBetween Constructible.Model.lCarrierMem
      first domain middle)
    (hsecond : IsGraphBetween Constructible.Model.lCarrierMem
      second middle codomain) :
    ∃ graph : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem
        graph domain codomain ∧
      ∀ x y : Constructible.Model.LCarrier.{u},
        GraphValue Constructible.Model.lCarrierMem graph x y ↔
          ∃ z : Constructible.Model.LCarrier.{u},
            GraphValue Constructible.Model.lCarrierMem first x z ∧
              GraphValue Constructible.Model.lCarrierMem second z y := by
  let container := unionLCarrier domain codomain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      compositionGraphPredicate ![first, second] container with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem graph x y ↔
        ∃ z : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem first x z ∧
            GraphValue Constructible.Model.lCarrierMem second z y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hx, _hy, hformula⟩
      exact (satisfies_compositionGraphPredicate first second x y).mp
        hformula
    · rintro ⟨z, hxz, hzy⟩
      have hx := (hfirst.graphValue_mem_lCarrier hxz).1
      have hy := (hsecond.graphValue_mem_lCarrier hzy).2
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff domain codomain x).mpr (Or.inl hx)
      · exact (mem_unionLCarrier_iff domain codomain y).mpr (Or.inr hy)
      · exact (satisfies_compositionGraphPredicate first second x y).mpr
          ⟨z, hxz, hzy⟩
  refine ⟨graph, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  rcases (satisfies_compositionGraphPredicate first second x y).mp
      hformula with ⟨z, hxz, hzy⟩
  have hx := (hfirst.graphValue_mem_lCarrier hxz).1
  have hy := (hsecond.graphValue_mem_lCarrier hzy).2
  exact ⟨x, hx, y, hy,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

theorem Injects.trans_lCarrier
    {domain middle codomain : Constructible.Model.LCarrier.{u}}
    (hfirst : Injects Constructible.Model.lCarrierMem domain middle)
    (hsecond : Injects Constructible.Model.lCarrierMem middle codomain) :
    Injects Constructible.Model.lCarrierMem domain codomain := by
  rcases hfirst with ⟨first, hfirst⟩
  rcases hsecond with ⟨second, hsecond⟩
  rcases exists_compositionGraph_lCarrier hfirst.1 hsecond.1 with
    ⟨graph, hbetween, hvalue⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro x hx
    rcases hfirst.2.1 x hx with ⟨y, hy, hxy, hyUnique⟩
    rcases hsecond.2.1 y hy with ⟨z, hz, hyz, hzUnique⟩
    refine ⟨z, hz, (hvalue x z).mpr ⟨y, hxy, hyz⟩, ?_⟩
    intro z' hz' hxz'
    rcases (hvalue x z').mp hxz' with ⟨y', hxy', hy'z'⟩
    have hy' := (hfirst.1.graphValue_mem_lCarrier hxy').2
    have hyEq : y' = y := hyUnique y' hy' hxy'
    subst y'
    exact hzUnique z' hz' hy'z'
  · intro z hz x hx hxz x' hx' hx'z
    rcases (hvalue x z).mp hxz with ⟨y, hxy, hyz⟩
    rcases (hvalue x' z).mp hx'z with ⟨y', hx'y', hy'z⟩
    have hy := (hfirst.1.graphValue_mem_lCarrier hxy).2
    have hy' := (hfirst.1.graphValue_mem_lCarrier hx'y').2
    have hyEq : y' = y :=
      hsecond.2.2 z hz y hy hyz y' hy' hy'z
    subst y'
    exact hfirst.2.2 y hy x hx hxy x' hx' hx'y'

theorem exists_converseGraph_lCarrier
    {graph domain codomain : Constructible.Model.LCarrier.{u}}
    (hgraph : IsGraphBetween Constructible.Model.lCarrierMem
      graph domain codomain) :
    ∃ converse : Constructible.Model.LCarrier.{u},
      IsGraphBetween Constructible.Model.lCarrierMem
        converse codomain domain ∧
      ∀ x y : Constructible.Model.LCarrier.{u},
        GraphValue Constructible.Model.lCarrierMem converse x y ↔
          GraphValue Constructible.Model.lCarrierMem graph y x := by
  let container := unionLCarrier codomain domain
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      converseGraphPredicate ![graph] container with
    ⟨converse, hsupport, hrelation⟩
  have hvalue : ∀ x y : Constructible.Model.LCarrier.{u},
      GraphValue Constructible.Model.lCarrierMem converse x y ↔
        GraphValue Constructible.Model.lCarrierMem graph y x := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hx, _hy, hformula⟩
      exact (satisfies_converseGraphPredicate graph x y).mp hformula
    · intro hyx
      have hmem := hgraph.graphValue_mem_lCarrier hyx
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_unionLCarrier_iff codomain domain x).mpr
          (Or.inl hmem.2)
      · exact (mem_unionLCarrier_iff codomain domain y).mpr
          (Or.inr hmem.1)
      · exact (satisfies_converseGraphPredicate graph x y).mpr hyx
  refine ⟨converse, ?_, hvalue⟩
  intro pair hpair
  rcases hsupport pair hpair with
    ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
  have hyx := (satisfies_converseGraphPredicate graph x y).mp hformula
  have hmem := hgraph.graphValue_mem_lCarrier hyx
  exact ⟨x, hmem.2, y, hmem.1,
    (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩

theorem Equinumerous.symm_lCarrier
    {domain codomain : Constructible.Model.LCarrier.{u}}
    (h : Equinumerous Constructible.Model.lCarrierMem domain codomain) :
    Equinumerous Constructible.Model.lCarrierMem codomain domain := by
  rcases h with ⟨graph, hgraph⟩
  rcases exists_converseGraph_lCarrier hgraph.1 with
    ⟨converse, hbetween, hvalue⟩
  refine ⟨converse, hbetween, ?_, ?_⟩
  · intro x hx
    rcases hgraph.2.2 x hx with ⟨y, hy, hyx, hyUnique⟩
    refine ⟨y, hy, (hvalue x y).mpr hyx, ?_⟩
    intro z hz hxz
    exact hyUnique z hz ((hvalue x z).mp hxz)
  · intro y hy
    rcases hgraph.2.1 y hy with ⟨x, hx, hyx, hxUnique⟩
    refine ⟨x, hx, (hvalue x y).mpr hyx, ?_⟩
    intro z hz hzy
    exact hxUnique z hz ((hvalue z y).mp hzy)

/-! ## Hartogs numbers are internal cardinals -/

theorem internalHartogsLCarrier_isCardinal
    (base : Constructible.Model.LCarrier.{u}) :
    IsCardinal Constructible.Model.lCarrierMem
      (internalHartogsLCarrier base) := by
  apply (internalHartogsLCarrier_isHartogsNumber base).isCardinal_of
  · intro x y hxy
    exact hxy.symm_lCarrier.injects
  · intro x y z hxy hyz
    exact hxy.trans_lCarrier hyz

end Constructible.ContinuumFormula
