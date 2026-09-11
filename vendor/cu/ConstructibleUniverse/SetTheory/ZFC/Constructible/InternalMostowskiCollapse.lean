/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiCollapse

/-!
# Internalizing a set-sized Mostowski collapse

`MostowskiCollapse.collapse` is an external well-founded recursion on actual
`ZFSet`s.  Consequently its range and graph are actual `ZFSet`s, but that fact
alone does not show that either set belongs to `L`.

This file isolates the exact bridge needed for that internalization.  A
`CollapseFormulaSpec` records a fixed first-order formula which is sound for
the external collapse and has an output in `L` for every member of the
domain.  Replacement then constructs the range in `L`, and Separation
constructs the Kuratowski-pair graph in `L`.

The remaining obligation in a full condensation proof is therefore explicit:
one must prove the `complete` field of `CollapseFormulaSpec`, normally from
the well-founded-recursion theorem of ZF.  No form of Condensation is assumed
in this file.
-/

@[expose] public section

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The Kuratowski-pair graph of the external Mostowski collapse. -/
noncomputable def graph (domain : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    ZFSet.pair x.1 (collapse domain x.1)

@[simp]
theorem mem_graph_iff {domain q : ZFSet.{u}} :
    q ∈ graph domain ↔
      ∃ x : ZFSet.{u}, x ∈ domain ∧
        ZFSet.pair x (collapse domain x) = q := by
  rw [graph, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, hvalue⟩
    exact ⟨x, hx, hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨⟨x, hx⟩, hvalue⟩

@[simp]
theorem pair_mem_graph_iff {domain x y : ZFSet.{u}} :
    ZFSet.pair x y ∈ graph domain ↔
      x ∈ domain ∧ y = collapse domain x := by
  rw [mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hpair⟩
    rcases ZFSet.pair_inj.mp hpair with ⟨hxz, hy⟩
    subst z
    exact ⟨hz, hy.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The collapse range of an already transitive domain is the domain itself. -/
theorem range_eq_self_of_isTransitive {domain : ZFSet.{u}}
    (htransitive : domain.IsTransitive) :
    range domain = domain := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_range_iff.mp hz with ⟨x, hx, hcollapse⟩
    have hfixed := collapse_eq_self_of_mem htransitive x hx
    have hxz : x = z := hfixed.symm.trans hcollapse
    simpa only [hxz] using hx
  · intro hz
    exact mem_range_iff.mpr
      ⟨z, hz, collapse_eq_self_of_mem htransitive z hz⟩

end

end MostowskiCollapse

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The first-order internalization interface -/

/--
A first-order definition of the collapse on `domain`.

The formula layout is `[domain, input, output]`.  `sound` rules out both
off-domain inputs and incorrect outputs.  `complete` is the substantive
well-founded-recursion obligation: it says that the formula has a witness in
`L` at every input in `domain`.
-/
structure CollapseFormulaSpec (domain : LCarrier.{u}) where
  formula : FOFormula 3
  sound : ∀ x y : LCarrier.{u},
    FOFormula.Satisfies LMem formula (snoc (snoc ![domain] x) y) →
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1
  complete : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
    ∃ y : LCarrier.{u},
      FOFormula.Satisfies LMem formula (snoc (snoc ![domain] x) y)

/-! A fully explicit sanity-check instance: collapse of a transitive set. -/

/-- On a transitive domain the collapse formula says `x ∈ domain ∧ y = x`. -/
def transitiveCollapseFormula : FOFormula 3 :=
  .conj (.mem (1 : Fin 3) (0 : Fin 3))
    (.eq (2 : Fin 3) (1 : Fin 3))

@[simp]
theorem satisfies_transitiveCollapseFormula
    (domain x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem transitiveCollapseFormula
        (snoc (snoc ![domain] x) y) ↔
      x.1 ∈ domain.1 ∧ y = x := by
  have hassignment : snoc (snoc ![domain] x) y = ![domain, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  rfl

/-- The explicit identity formula represents collapse on a transitive set. -/
def collapseFormulaSpec_of_isTransitive
    (domain : LCarrier.{u}) (htransitive : domain.1.IsTransitive) :
    CollapseFormulaSpec domain where
  formula := transitiveCollapseFormula
  sound := by
    intro x y hformula
    have hsemantic :=
      (satisfies_transitiveCollapseFormula domain x y).mp hformula
    refine ⟨hsemantic.1, ?_⟩
    have hyx : y.1 = x.1 := congrArg Subtype.val hsemantic.2
    exact hyx.trans
      (MostowskiCollapse.collapse_eq_self_of_mem
        htransitive x.1 hsemantic.1).symm
  complete := by
    intro x hx
    exact ⟨x,
      (satisfies_transitiveCollapseFormula domain x x).mpr ⟨hx, rfl⟩⟩

/-- Soundness makes the output of a collapse formula unique. -/
theorem CollapseFormulaSpec.existsUnique_output
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    ∃! y : LCarrier.{u},
      FOFormula.Satisfies LMem spec.formula
        (snoc (snoc ![domain] x) y) := by
  rcases spec.complete x hx with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  exact (spec.sound x z hz).2.trans (spec.sound x y hy).2.symm

/-- Every pointwise collapse value selected by the formula belongs to `L`. -/
theorem CollapseFormulaSpec.collapse_mem_L
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    MostowskiCollapse.collapse domain.1 x.1 ∈ L := by
  rcases spec.complete x hx with ⟨y, hformula⟩
  rw [← (spec.sound x y hformula).2]
  exact y.2

/-- Replacement internalizes the exact range of a collapse formula. -/
theorem exists_collapseRangeLCarrier
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain) :
    ∃ rangeCarrier : LCarrier.{u},
      rangeCarrier.1 = MostowskiCollapse.range domain.1 := by
  let params : Tuple LCarrier.{u} 1 := ![domain]
  have hfun : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
      ∃! y : LCarrier.{u},
        FOFormula.Satisfies LMem spec.formula
          (snoc (snoc params x) y) := by
    intro x hx
    simpa only [params] using spec.existsUnique_output x hx
  rcases exists_replacementLCarrier spec.formula params domain hfun with
    ⟨rangeCarrier, hrange⟩
  refine ⟨rangeCarrier, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    let zL : LCarrier.{u} :=
      ⟨z, mem_L_of_mem hz rangeCarrier.2⟩
    rcases (hrange zL).mp hz with ⟨x, hx, hformula⟩
    have hzCollapse :
        z = MostowskiCollapse.collapse domain.1 x.1 :=
      (spec.sound x zL (by
        simpa only [params] using hformula)).2
    exact MostowskiCollapse.mem_range_iff.mpr
      ⟨x.1, hx, hzCollapse.symm⟩
  · intro hz
    rcases MostowskiCollapse.mem_range_iff.mp hz with
      ⟨x, hx, hcollapse⟩
    let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx domain.2⟩
    rcases spec.complete xL hx with ⟨y, hformula⟩
    have hyCollapse :
        y.1 = MostowskiCollapse.collapse domain.1 x :=
      (spec.sound xL y hformula).2
    have hyz : y.1 = z := hyCollapse.trans hcollapse
    have hyRange : y.1 ∈ rangeCarrier.1 :=
      (hrange y).mpr ⟨xL, hx, by
        simpa only [params] using hformula⟩
    simpa only [hyz] using hyRange

/-! ## Packaged internal range and graph -/

/-- A collapse whose range and Kuratowski graph are both actual members of `L`. -/
structure InternalizedCollapse (domain : LCarrier.{u}) where
  rangeCarrier : LCarrier.{u}
  graphCarrier : LCarrier.{u}
  range_val : rangeCarrier.1 = MostowskiCollapse.range domain.1
  graph_val : graphCarrier.1 = MostowskiCollapse.graph domain.1

/-- Package already established constructibility of the external range and graph. -/
def InternalizedCollapse.of_mem
    (domain : LCarrier.{u})
    (hrange : MostowskiCollapse.range domain.1 ∈ L)
    (hgraph : MostowskiCollapse.graph domain.1 ∈ L) :
    InternalizedCollapse domain where
  rangeCarrier := ⟨MostowskiCollapse.range domain.1, hrange⟩
  graphCarrier := ⟨MostowskiCollapse.graph domain.1, hgraph⟩
  range_val := rfl
  graph_val := rfl

/--
Replacement constructs the collapse range and Separation constructs its exact
Kuratowski-pair graph.  Both witnesses therefore belong to `L`.
-/
theorem exists_internalizedCollapse_of_formulaSpec
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain) :
    ∃ _witness : InternalizedCollapse domain, True := by
  rcases exists_collapseRangeLCarrier spec with
    ⟨rangeCarrier, hrange⟩
  let container :=
    Constructible.ContinuumFormula.unionLCarrier domain rangeCarrier
  let params : Tuple LCarrier.{u} 1 := ![domain]
  rcases exists_definableRelationGraph_with_support
      spec.formula params container with
    ⟨graphCarrier, hsupport, hrelation⟩
  have hgraph :
      graphCarrier.1 = MostowskiCollapse.graph domain.1 := by
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      let qL : LCarrier.{u} :=
        ⟨q, mem_L_of_mem hq graphCarrier.2⟩
      rcases hsupport qL hq with
        ⟨x, y, _hxContainer, _hyContainer, hpair, hformula⟩
      have hsound := spec.sound x y (by
        simpa only [params] using hformula)
      apply MostowskiCollapse.mem_graph_iff.mpr
      refine ⟨x.1, hsound.1, ?_⟩
      exact (congrArg (ZFSet.pair x.1) hsound.2.symm).trans hpair.symm
    · intro hq
      rcases MostowskiCollapse.mem_graph_iff.mp hq with
        ⟨x, hx, hpair⟩
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx domain.2⟩
      rcases spec.complete xL hx with ⟨y, hformula⟩
      have hyCollapse :
          y.1 = MostowskiCollapse.collapse domain.1 x :=
        (spec.sound xL y hformula).2
      have hxContainer : xL.1 ∈ container.1 :=
        (Constructible.ContinuumFormula.mem_unionLCarrier_iff
          domain rangeCarrier xL).mpr (Or.inl hx)
      have hyRange : y.1 ∈ rangeCarrier.1 := by
        rw [hrange]
        exact MostowskiCollapse.mem_range_iff.mpr
          ⟨x, hx, hyCollapse.symm⟩
      have hyContainer : y.1 ∈ container.1 :=
        (Constructible.ContinuumFormula.mem_unionLCarrier_iff
          domain rangeCarrier y).mpr (Or.inr hyRange)
      have hgraphRel : GraphRel graphCarrier xL y :=
        (hrelation xL y).mpr
          ⟨hxContainer, hyContainer, by
            simpa only [params] using hformula⟩
      have hpair' : ZFSet.pair x y.1 = q :=
        (congrArg (ZFSet.pair x) hyCollapse).trans hpair
      change q ∈ graphCarrier.1
      rw [← hpair']
      exact hgraphRel
  exact ⟨{
    rangeCarrier := rangeCarrier
    graphCarrier := graphCarrier
    range_val := hrange
    graph_val := hgraph
  }, trivial⟩

/-- A represented collapse has a constructible external range. -/
theorem collapseRange_mem_L_of_formulaSpec
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain) :
    MostowskiCollapse.range domain.1 ∈ L := by
  rcases exists_collapseRangeLCarrier spec with ⟨rangeCarrier, hrange⟩
  rw [← hrange]
  exact rangeCarrier.2

/-- A represented collapse has a constructible external Kuratowski graph. -/
theorem collapseGraph_mem_L_of_formulaSpec
    {domain : LCarrier.{u}} (spec : CollapseFormulaSpec domain) :
    MostowskiCollapse.graph domain.1 ∈ L := by
  rcases exists_internalizedCollapse_of_formulaSpec spec with ⟨w, _⟩
  rw [← w.graph_val]
  exact w.graphCarrier.2

/-- The explicit identity formula fully internalizes collapse of a transitive set. -/
theorem exists_internalizedCollapse_of_isTransitive
    (domain : LCarrier.{u}) (htransitive : domain.1.IsTransitive) :
    ∃ _witness : InternalizedCollapse domain, True :=
  exists_internalizedCollapse_of_formulaSpec
    (collapseFormulaSpec_of_isTransitive domain htransitive)

/-! ## Consequences of an internalized collapse -/

theorem InternalizedCollapse.range_isTransitive
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain) :
    w.rangeCarrier.1.IsTransitive := by
  rw [w.range_val]
  exact MostowskiCollapse.range_isTransitive domain.1

@[simp]
theorem InternalizedCollapse.graphRel_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (x y : LCarrier.{u}) :
    GraphRel w.graphCarrier x y ↔
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  rw [GraphRel, w.graph_val, MostowskiCollapse.pair_mem_graph_iff]

@[simp]
theorem InternalizedCollapse.graphValue_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (x y : LCarrier.{u}) :
    Constructible.ContinuumFormula.GraphValue LMem
        w.graphCarrier x y ↔
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  rw [Constructible.ContinuumFormula.graphValue_lCarrier_iff_graphRel,
    w.graphRel_iff]

theorem InternalizedCollapse.isGraphBetween
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain) :
    Constructible.ContinuumFormula.IsGraphBetween LMem
      w.graphCarrier domain w.rangeCarrier := by
  intro pair hpair
  have hraw : pair.1 ∈ MostowskiCollapse.graph domain.1 := by
    change pair.1 ∈ w.graphCarrier.1 at hpair
    rw [w.graph_val] at hpair
    exact hpair
  rcases MostowskiCollapse.mem_graph_iff.mp hraw with
    ⟨x, hx, hpairEq⟩
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx domain.2⟩
  have hcollapseRange :
      MostowskiCollapse.collapse domain.1 x ∈ w.rangeCarrier.1 := by
    rw [w.range_val]
    exact MostowskiCollapse.mem_range_iff.mpr ⟨x, hx, rfl⟩
  let yL : LCarrier.{u} :=
    ⟨MostowskiCollapse.collapse domain.1 x,
      mem_L_of_mem hcollapseRange w.rangeCarrier.2⟩
  refine ⟨xL, hx, yL, hcollapseRange, ?_⟩
  apply (Constructible.ContinuumFormula.isKuratowskiPairOf_lCarrier_iff
    pair xL yL).mpr
  exact hpairEq.symm

/-- The internal collapse graph is a bijection onto the internal range. -/
theorem InternalizedCollapse.isBijection
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1) :
    Constructible.ContinuumFormula.IsBijection LMem
      w.graphCarrier domain w.rangeCarrier := by
  refine ⟨w.isGraphBetween, ?_, ?_⟩
  · intro x hx
    have hcollapseRange :
        MostowskiCollapse.collapse domain.1 x.1 ∈ w.rangeCarrier.1 := by
      rw [w.range_val]
      exact MostowskiCollapse.mem_range_iff.mpr ⟨x.1, hx, rfl⟩
    let y : LCarrier.{u} :=
      ⟨MostowskiCollapse.collapse domain.1 x.1,
        mem_L_of_mem hcollapseRange w.rangeCarrier.2⟩
    refine ⟨y, hcollapseRange, (w.graphValue_iff x y).mpr ⟨hx, rfl⟩, ?_⟩
    intro z _hz hvalue
    apply Subtype.ext
    exact (w.graphValue_iff x z).mp hvalue |>.2
  · intro y hy
    have hyRaw : y.1 ∈ MostowskiCollapse.range domain.1 := by
      change y.1 ∈ w.rangeCarrier.1 at hy
      rw [w.range_val] at hy
      exact hy
    rcases MostowskiCollapse.mem_range_iff.mp hyRaw with
      ⟨x, hx, hcollapse⟩
    let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx domain.2⟩
    refine ⟨xL, hx, (w.graphValue_iff xL y).mpr
      ⟨hx, hcollapse.symm⟩, ?_⟩
    intro z hz hvalue
    have hzCollapse := (w.graphValue_iff z y).mp hvalue |>.2
    have hcollapseEq :
        MostowskiCollapse.collapse domain.1 x =
          MostowskiCollapse.collapse domain.1 z.1 :=
      hcollapse.trans hzCollapse
    have hxz := MostowskiCollapse.collapse_eq_imp_eq_of_mem
      hextensional x hx z.1 hz hcollapseEq
    exact Subtype.ext hxz.symm

/-- The internal graph witnesses internal equinumerosity with the range. -/
theorem InternalizedCollapse.equinumerous
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1) :
    Constructible.ContinuumFormula.Equinumerous LMem
      domain w.rangeCarrier :=
  ⟨w.graphCarrier, w.isBijection hextensional⟩

/-! ## The membership isomorphism -/

def internalCarrierEquivRaw (a : LCarrier.{u}) :
    InternalCarrier a ≃ {x : ZFSet.{u} // x ∈ a.1} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, mem_L_of_mem x.2 a.2⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def InternalizedCollapse.rawRangeEquiv
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain) :
    {z : ZFSet.{u} // z ∈ w.rangeCarrier.1} ≃
      {z : ZFSet.{u} // z ∈ MostowskiCollapse.range domain.1} where
  toFun z := ⟨z.1, by simpa only [w.range_val] using z.2⟩
  invFun z := ⟨z.1, by simpa only [w.range_val] using z.2⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- The internal-carrier version of the Mostowski equivalence. -/
noncomputable def InternalizedCollapse.equivRange
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1) :
    InternalCarrier domain ≃ InternalCarrier w.rangeCarrier :=
  ((((internalCarrierEquivRaw domain).trans
      (MostowskiCollapse.equivRange hextensional)).trans
      w.rawRangeEquiv.symm).trans
      (internalCarrierEquivRaw w.rangeCarrier).symm)

@[simp]
theorem InternalizedCollapse.equivRange_val
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1)
    (x : InternalCarrier domain) :
    (w.equivRange hextensional x).1.1 =
      MostowskiCollapse.collapse domain.1 x.1.1 := by
  simp [InternalizedCollapse.equivRange, internalCarrierEquivRaw,
    InternalizedCollapse.rawRangeEquiv,
    MostowskiCollapse.equivRange_apply]

/-- The internalized Mostowski equivalence preserves and reflects membership. -/
@[simp]
theorem InternalizedCollapse.equivRange_mem_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1)
    (x y : InternalCarrier domain) :
    (w.equivRange hextensional x).1.1 ∈
        (w.equivRange hextensional y).1.1 ↔
      x.1.1 ∈ y.1.1 := by
  simp only [w.equivRange_val]
  exact MostowskiCollapse.collapse_mem_collapse_iff
    hextensional x.2 y.2

end

end Model

end Constructible
