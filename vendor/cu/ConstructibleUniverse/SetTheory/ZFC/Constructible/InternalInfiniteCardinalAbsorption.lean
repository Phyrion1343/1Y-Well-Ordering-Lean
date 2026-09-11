/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GeneralCollapseInternalization

/-!
# Finite absorption by an internally infinite constructible set

This file carries out the standard Hilbert-hotel argument with actual graphs
belonging to `L`.  If `omega` is a subset of a constructible set `kappa`, the
definable map which shifts the natural numbers and fixes every other element
is an internal injection `kappa -> kappa` whose range omits the empty set.
Consequently an internal injection into `kappa` can be extended over one
fresh point.

No ambient function or cardinal comparison is used as an internal witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The internal omega shift -/

/-- The semantic Hilbert-hotel shift: move members of `omega` to their von
Neumann successors and fix all other sets. -/
def OmegaShift (x y : LCarrier.{u}) : Prop :=
  (x.1 ∈ omegaLCarrier.1 ∧ y = successorLCarrier x) ∨
    (x.1 ∉ omegaLCarrier.1 ∧ y = x)

/-- Layout `(omega,x,y)`. -/
def omegaShiftFormula : FOFormula 3 :=
  .disj
    (.conj
      (.mem (1 : Fin 3) (0 : Fin 3))
      (Constructible.Model.successorSetAt (2 : Fin 3) (1 : Fin 3)))
    (.conj
      (.neg (.mem (1 : Fin 3) (0 : Fin 3)))
      (.eq (2 : Fin 3) (1 : Fin 3)))

@[simp]
theorem satisfies_omegaShiftFormula
    (omega x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem omegaShiftFormula
        (snoc (snoc ![omega] x) y) ↔
      (x.1 ∈ omega.1 ∧ y = successorLCarrier x) ∨
        (x.1 ∉ omega.1 ∧ y = x) := by
  have hassignment : snoc (snoc ![omega] x) y = ![omega, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  simp [omegaShiftFormula]

/-- The successor of a member of the standard omega is again in omega. -/
theorem successorLCarrier_mem_omegaLCarrier
    (x : LCarrier.{u}) (hx : x.1 ∈ omegaLCarrier.1) :
    (successorLCarrier x).1 ∈ omegaLCarrier.1 :=
  Constructible.Model.omegaLCarrier_isInductiveSet.2 x hx

/-- The omega shift takes members of any `kappa` containing omega back into
`kappa`. -/
theorem OmegaShift.mem_of_omega_subset
    {kappa x y : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hx : x.1 ∈ kappa.1) (hshift : OmegaShift x y) :
    y.1 ∈ kappa.1 := by
  rcases hshift with hnat | hfixed
  · rw [hnat.2]
    exact homega _ (successorLCarrier_mem_omegaLCarrier x hnat.1)
  · simpa only [hfixed.2] using hx

/-- The omega shift is a genuine injection. -/
theorem OmegaShift.injective
    {x y z : LCarrier.{u}}
    (hxy : OmegaShift x y) (hzy : OmegaShift z y) :
    z = x := by
  rcases hxy with hxn | hxf <;> rcases hzy with hzn | hzf
  · have hsucc : successorLCarrier x = successorLCarrier z :=
      hxn.2.symm.trans hzn.2
    apply Subtype.ext
    apply insert_self_injective
    exact (congrArg Subtype.val hsucc).symm
  · have hyOmega : y.1 ∈ omegaLCarrier.1 := by
      rw [hxn.2]
      exact successorLCarrier_mem_omegaLCarrier x hxn.1
    rw [hzf.2] at hyOmega
    exact (hzf.1 hyOmega).elim
  · have hyOmega : y.1 ∈ omegaLCarrier.1 := by
      rw [hzn.2]
      exact successorLCarrier_mem_omegaLCarrier z hzn.1
    rw [hxf.2] at hyOmega
    exact (hxf.1 hyOmega).elim
  · exact hzf.2.symm.trans hxf.2

/-- The empty set is omitted by the omega shift. -/
theorem OmegaShift.ne_emptyLCarrier
    {x : LCarrier.{u}} : ¬ OmegaShift x emptyLCarrier := by
  intro hshift
  rcases hshift with hnat | hfixed
  · have hxMemSucc : x.1 ∈ (successorLCarrier x).1 := by
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      exact Or.inl rfl
    rw [← hnat.2] at hxMemSucc
    exact not_mem_emptyLCarrier x hxMemSucc
  · apply hfixed.1
    rw [← hfixed.2]
    exact empty_mem_omegaLCarrier

/-- Separation produces the internal omega-shift graph on `kappa`.  The
result records both its exact value semantics and the omitted empty value. -/
theorem exists_omegaShiftInjection_lCarrier
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    ∃ graph : LCarrier.{u},
      IsInjection LMem graph kappa kappa ∧
        (∀ x y : LCarrier.{u},
          GraphValue LMem graph x y ↔
            x.1 ∈ kappa.1 ∧ OmegaShift x y) ∧
          ∀ x : LCarrier.{u},
            ¬GraphValue LMem graph x emptyLCarrier := by
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      omegaShiftFormula ![omegaLCarrier] kappa with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : ∀ x y : LCarrier.{u},
      GraphValue LMem graph x y ↔
        x.1 ∈ kappa.1 ∧ OmegaShift x y := by
    intro x y
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨hx, _hy, hformula⟩
      exact ⟨hx,
        (satisfies_omegaShiftFormula omegaLCarrier x y).mp hformula⟩
    · rintro ⟨hx, hshift⟩
      exact ⟨hx, hshift.mem_of_omega_subset homega hx,
        (satisfies_omegaShiftFormula omegaLCarrier x y).mpr hshift⟩
  have hbetween : IsGraphBetween LMem graph kappa kappa := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, hx, hy, hpairEq, _hformula⟩
    exact ⟨x, hx, y, hy,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  have hinjection : IsInjection LMem graph kappa kappa := by
    refine ⟨hbetween, ?_, ?_⟩
    · intro x hx
      by_cases hnat : x.1 ∈ omegaLCarrier.1
      · let y := successorLCarrier x
        have hshift : OmegaShift x y := Or.inl ⟨hnat, rfl⟩
        refine ⟨y, hshift.mem_of_omega_subset homega hx,
          (hvalue x y).mpr ⟨hx, hshift⟩, ?_⟩
        intro z _hz hzValue
        rcases (hvalue x z).mp hzValue with ⟨_hx, hzShift⟩
        rcases hzShift with hsucc | hfixed
        · exact hsucc.2
        · exact (hfixed.1 hnat).elim
      · refine ⟨x, hx,
          (hvalue x x).mpr ⟨hx, Or.inr ⟨hnat, rfl⟩⟩, ?_⟩
        intro z _hz hzValue
        rcases (hvalue x z).mp hzValue with ⟨_hx, hzShift⟩
        rcases hzShift with hsucc | hfixed
        · exact (hnat hsucc.1).elim
        · exact hfixed.2
    · intro y _hy x hx hxy z hz hzy
      exact OmegaShift.injective (hvalue x y |>.mp hxy).2
        (hvalue z y |>.mp hzy).2
  refine ⟨graph, hinjection, hvalue, ?_⟩
  intro x hxEmpty
  exact OmegaShift.ne_emptyLCarrier (hvalue x emptyLCarrier |>.mp hxEmpty).2

/-! ## Composition and adjoining a fresh point -/

/-- The constructible set `domain union {point}`. -/
def adjoinLCarrier
    (domain point : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier (singletonLCarrier point) domain

@[simp]
theorem mem_adjoinLCarrier_iff
    (domain point z : LCarrier.{u}) :
    z.1 ∈ (adjoinLCarrier domain point).1 ↔
      z = point ∨ z.1 ∈ domain.1 := by
  simp only [adjoinLCarrier, mem_unionLCarrier_iff,
    mem_singletonLCarrier_iff]

@[simp]
theorem adjoin_self_eq_successorLCarrier
    (domain : LCarrier.{u}) :
    adjoinLCarrier domain domain = successorLCarrier domain := by
  apply lCarrier_extensionality
  intro z
  simp only [mem_adjoinLCarrier_iff, successorLCarrier_val,
    ZFSet.mem_insert_iff, Subtype.ext_iff]

/-- The composition graph constructed by Separation carries the composite
injection, together with its exact graph-value semantics. -/
theorem exists_compositionInjection_lCarrier
    {first second domain middle codomain : LCarrier.{u}}
    (hfirst : IsInjection LMem first domain middle)
    (hsecond : IsInjection LMem second middle codomain) :
    ∃ graph : LCarrier.{u},
      IsInjection LMem graph domain codomain ∧
        ∀ x y : LCarrier.{u},
          GraphValue LMem graph x y ↔
            ∃ z : LCarrier.{u},
              GraphValue LMem first x z ∧
                GraphValue LMem second z y := by
  rcases exists_compositionGraph_lCarrier hfirst.1 hsecond.1 with
    ⟨graph, hbetween, hvalue⟩
  have hinjection : IsInjection LMem graph domain codomain := by
    refine ⟨hbetween, ?_, ?_⟩
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
  exact ⟨graph, hinjection, hvalue⟩

/-- Inserting one new graph value extends an injection across a fresh point,
provided the new value was omitted by the old graph. -/
theorem IsInjection.insert_fresh_lCarrier
    {graph domain codomain point value : LCarrier.{u}}
    (hgraph : IsInjection LMem graph domain codomain)
    (hpoint : point.1 ∉ domain.1)
    (hvalue : value.1 ∈ codomain.1)
    (homit : ∀ x : LCarrier.{u},
      ¬GraphValue LMem graph x value) :
    IsInjection LMem
      (Constructible.Model.insertGraphValue graph point value)
      (adjoinLCarrier domain point) codomain := by
  have hbetween : IsGraphBetween LMem
      (Constructible.Model.insertGraphValue graph point value)
      (adjoinLCarrier domain point) codomain := by
    intro pair hpair
    rcases (Constructible.Model.mem_insertGraphValue_iff
      graph point value pair).mp hpair with hnew | hold
    · subst pair
      exact ⟨point,
        (mem_adjoinLCarrier_iff domain point point).mpr (Or.inl rfl),
        value, hvalue,
        (isKuratowskiPairOf_lCarrier_iff
          (orderedPairLCarrier point value) point value).mpr rfl⟩
    · rcases hgraph.1 pair hold with ⟨x, hx, y, hy, hpairXY⟩
      exact ⟨x,
        (mem_adjoinLCarrier_iff domain point x).mpr (Or.inr hx),
        y, hy, hpairXY⟩
  refine ⟨hbetween, ?_, ?_⟩
  · intro x hx
    rcases (mem_adjoinLCarrier_iff domain point x).mp hx with
      hnew | hold
    · subst x
      refine ⟨value, hvalue,
        (Constructible.Model.graphValue_insertGraphValue_iff
          graph point value point value).mpr
            (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro z _hz hzGraph
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value point z).mp hzGraph with hold | hnew
      · have hpointDomain :=
          (hgraph.1.graphValue_mem_lCarrier hold).1
        exact (hpoint hpointDomain).elim
      · exact hnew.2
    · rcases hgraph.2.1 x hold with ⟨y, hy, hxy, hyUnique⟩
      refine ⟨y, hy,
        (Constructible.Model.graphValue_insertGraphValue_iff
          graph point value x y).mpr (Or.inl hxy), ?_⟩
      intro z hz hxz
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value x z).mp hxz with holdValue | hnew
      · exact hyUnique z hz holdValue
      · have hpointDomain : point.1 ∈ domain.1 := by
          rw [← hnew.1]
          exact hold
        exact (hpoint hpointDomain).elim
  · intro y hy x _hx hxy z _hz hzy
    rcases (Constructible.Model.graphValue_insertGraphValue_iff
      graph point value x y).mp hxy with hxyOld | hxyNew <;>
      rcases (Constructible.Model.graphValue_insertGraphValue_iff
        graph point value z y).mp hzy with hzyOld | hzyNew
    · have hxDomain := (hgraph.1.graphValue_mem_lCarrier hxyOld).1
      have hzDomain := (hgraph.1.graphValue_mem_lCarrier hzyOld).1
      exact hgraph.2.2 y hy x hxDomain hxyOld z hzDomain hzyOld
    · have hxyValue : GraphValue LMem graph x value := by
        rw [← hzyNew.2]
        exact hxyOld
      exact (homit x hxyValue).elim
    · have hzyValue : GraphValue LMem graph z value := by
        rw [← hxyNew.2]
        exact hzyOld
      exact (homit z hzyValue).elim
    · exact hzyNew.1.trans hxyNew.1.symm

/-- If `kappa` contains omega, any internal injection `domain -> kappa`
extends to `domain union {point}` when `point` is fresh. -/
theorem injects_adjoin_fresh_of_omega_subset_lCarrier
    {domain kappa point : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hpoint : point.1 ∉ domain.1)
    (hinjects : Injects LMem domain kappa) :
    Injects LMem (adjoinLCarrier domain point) kappa := by
  rcases hinjects with ⟨first, hfirst⟩
  rcases exists_omegaShiftInjection_lCarrier kappa homega with
    ⟨shift, hshift, _hshiftValue, hshiftOmits⟩
  rcases exists_compositionInjection_lCarrier hfirst hshift with
    ⟨composite, hcomposite, hcompositeValue⟩
  have hcompositeOmits : ∀ x : LCarrier.{u},
      ¬GraphValue LMem composite x emptyLCarrier := by
    intro x hxEmpty
    rcases (hcompositeValue x emptyLCarrier).mp hxEmpty with
      ⟨middle, _hxMiddle, hmiddleEmpty⟩
    exact hshiftOmits middle hmiddleEmpty
  exact ⟨Constructible.Model.insertGraphValue
      composite point emptyLCarrier,
    hcomposite.insert_fresh_lCarrier hpoint
      (homega emptyLCarrier empty_mem_omegaLCarrier)
      hcompositeOmits⟩

/-- A set containing omega internally absorbs one von Neumann successor. -/
theorem injects_successor_of_omega_subset_lCarrier
    {domain kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : Injects LMem domain kappa) :
    Injects LMem (successorLCarrier domain) kappa := by
  have hfresh : domain.1 ∉ domain.1 := ZFSet.mem_irrefl domain.1
  simpa only [adjoin_self_eq_successorLCarrier] using
    injects_adjoin_fresh_of_omega_subset_lCarrier
      homega hfresh hinjects

/-- Ordinal specialization of one-point absorption. -/
theorem injects_successorOrdinal_of_omega_subset_lCarrier
    {alpha : Ordinal.{u}} {kappa : LCarrier.{u}}
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (hinjects : Injects LMem (ordinalLCarrier alpha) kappa) :
    Injects LMem (ordinalLCarrier (Order.succ alpha)) kappa := by
  simpa only [successorLCarrier_ordinalLCarrier] using
    injects_successor_of_omega_subset_lCarrier homega hinjects

end

end Constructible.ContinuumFormula
