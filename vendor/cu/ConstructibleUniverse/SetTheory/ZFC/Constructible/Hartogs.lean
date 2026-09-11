/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ContinuumHypothesis
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryGeneratorInternalOrder
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOrdinal
public import Mathlib.SetTheory.ZFC.Cardinal

/-!
# Internal injections and Hartogs numbers

This file formulates Hartogs' construction entirely inside a membership
structure.  Injections are represented by sets of Kuratowski pairs, so an
injection in `LCarrier` is required to have a graph which itself belongs to
`L`.  Ambient cardinal comparison is used only to show that the search for
an obstruction is nonempty; the least obstruction and its specification use
only internally represented injection graphs.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace Constructible.ContinuumFormula

/-! ## Semantic relations -/

/-- The graph has at most one preimage in `domain` at `y`. -/
def HasAtMostOnePreimage {A : Type u} (E : A → A → Prop)
    (graph domain y : A) : Prop :=
  ∀ x : A, E x domain → GraphValue E graph x y →
    ∀ z : A, E z domain → GraphValue E graph z y → z = x

/-- A set-coded injection from `domain` into `codomain`. -/
def IsInjection {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain ∧
    (∀ x : A, E x domain → HasUniqueImage E graph x codomain) ∧
      ∀ y : A, E y codomain →
        HasAtMostOnePreimage E graph domain y

/-- There is an internally represented injection from `domain` to
`codomain`. -/
def Injects {A : Type u} (E : A → A → Prop)
    (domain codomain : A) : Prop :=
  ∃ graph : A, IsInjection E graph domain codomain

/-- The elements of a set in a relation-parametric membership structure. -/
abbrev RelationCarrier {A : Type u} (E : A → A → Prop) (a : A) :=
  {x : A // E x a}

/-- `hartogs` is the least ordinal which does not internally inject into
`base`. -/
def IsHartogsNumber {A : Type u} (E : A → A → Prop)
    (base hartogs : A) : Prop :=
  IsVonNeumannOrdinal E hartogs ∧
    ¬Injects E hartogs base ∧
      ∀ alpha : A, E alpha hartogs → Injects E alpha base

/-- Every internally represented bijection is, in particular, an internally
represented injection. -/
theorem IsBijection.toIsInjection {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsBijection E graph domain codomain) :
    IsInjection E graph domain codomain := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro y hy
  rcases h.2.2 y hy with ⟨x, hx, hxy, hunique⟩
  intro x' hx' hx'y z hz hzy
  exact (hunique z hz hzy).trans (hunique x' hx' hx'y).symm

/-- Internal equinumerosity gives an internal injection. -/
theorem Equinumerous.injects {A : Type u} {E : A → A → Prop}
    {domain codomain : A} (h : Equinumerous E domain codomain) :
    Injects E domain codomain := by
  rcases h with ⟨graph, hgraph⟩
  exact ⟨graph, hgraph.toIsInjection⟩

/-- The function selected from a total internally represented injection. -/
noncomputable def IsInjection.toFun
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    RelationCarrier E domain → RelationCarrier E codomain :=
  fun x =>
    ⟨Classical.choose (h.2.1 x.1 x.2),
      (Classical.choose_spec (h.2.1 x.1 x.2)).1⟩

theorem IsInjection.toFun_graphValue
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain)
    (x : RelationCarrier E domain) :
    GraphValue E graph x.1 (h.toFun x).1 :=
  (Classical.choose_spec (h.2.1 x.1 x.2)).2.1

theorem IsInjection.toFun_injective
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    Function.Injective h.toFun := by
  intro x z hxz
  apply Subtype.ext
  have hvalue : (h.toFun x).1 = (h.toFun z).1 :=
    congrArg Subtype.val hxz
  have hzx : z.1 = x.1 :=
    h.2.2 (h.toFun x).1 (h.toFun x).2
      x.1 x.2 (h.toFun_graphValue x)
      z.1 z.2 (by
        rw [hvalue]
        exact h.toFun_graphValue z)
  exact hzx.symm

/-- An internally represented injection induces an actual embedding between
the corresponding semantic carriers.  This theorem is used only to establish
the external nonemptiness needed when taking the least internal obstruction. -/
noncomputable def IsInjection.toEmbedding
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    RelationCarrier E domain ↪ RelationCarrier E codomain :=
  ⟨h.toFun, h.toFun_injective⟩

theorem Injects.cardinalMk_le
    {A : Type u} {E : A → A → Prop} {domain codomain : A}
    (h : Injects E domain codomain) :
    #(RelationCarrier E domain) ≤ #(RelationCarrier E codomain) := by
  rcases h with ⟨graph, hgraph⟩
  exact Cardinal.mk_le_of_injective hgraph.toFun_injective

theorem IsHartogsNumber.not_equinumerous
    {A : Type u} {E : A → A → Prop} {base hartogs : A}
    (h : IsHartogsNumber E base hartogs) :
    ¬Equinumerous E hartogs base := by
  intro heq
  exact h.2.1 heq.injects

/--
The Hartogs obstruction is an internal cardinal as soon as internally coded
injections can be reversed along a bijection and composed.  Keeping these
hypotheses explicit prevents an ambient function from being mistaken for a
graph which belongs to the membership structure.
-/
theorem IsHartogsNumber.isCardinal_of
    {A : Type u} {E : A → A → Prop} {base hartogs : A}
    (h : IsHartogsNumber E base hartogs)
    (reverse : ∀ {x y : A}, Equinumerous E x y → Injects E y x)
    (comp : ∀ {x y z : A},
      Injects E x y → Injects E y z → Injects E x z) :
    IsCardinal E hartogs := by
  refine ⟨h.1, ?_⟩
  intro alpha halpha heq
  exact h.2.1 (comp (reverse heq) (h.2.2 alpha halpha))

/-! ## The internal Hartogs number of a constructible set -/

private noncomputable def externalHartogsBound
    (base : Constructible.Model.LCarrier.{u}) : Ordinal.{u} :=
  (Order.succ (ZFSet.card base.1)).ord

/-- The von Neumann ordinal predicate is absolute between the transitive
class `L` and the ambient well-founded `ZFSet` universe. -/
theorem isVonNeumannOrdinal_lCarrier_iff
    (x : Constructible.Model.LCarrier.{u}) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem x ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  constructor
  · rintro ⟨hxTransitive, hmembers⟩
    constructor
    · intro y hy z hz
      let yL : Constructible.Model.LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hy x.2⟩
      let zL : Constructible.Model.LCarrier.{u} :=
        ⟨z, Constructible.mem_L_of_mem hz yL.2⟩
      exact hxTransitive yL hy zL hz
    · intro y hy z hz w hw
      let yL : Constructible.Model.LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hy x.2⟩
      let zL : Constructible.Model.LCarrier.{u} :=
        ⟨z, Constructible.mem_L_of_mem hz yL.2⟩
      let wL : Constructible.Model.LCarrier.{u} :=
        ⟨w, Constructible.mem_L_of_mem hw zL.2⟩
      exact hmembers yL hy zL hz wL hw
  · rintro ⟨hxTransitive, hmembers⟩
    constructor
    · intro y hy z hz
      exact hxTransitive.mem_trans hz hy
    · intro y hy z hz w hw
      exact (hmembers y.1 hy).mem_trans hw hz

/-- Every internally recognized ordinal is its canonical constructible
ordinal code. -/
theorem exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
    (x : Constructible.Model.LCarrier.{u})
    (hx : IsVonNeumannOrdinal Constructible.Model.lCarrierMem x) :
    ∃ alpha : Ordinal.{u},
      x = Constructible.Model.ordinalLCarrier alpha := by
  refine ⟨x.1.rank, ?_⟩
  apply Subtype.ext
  exact (isVonNeumannOrdinal_lCarrier_iff x).mp hx |>.toZFSet_rank_eq.symm

private theorem ordinalLCarrier_isVonNeumannOrdinal (alpha : Ordinal.{u}) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem
      (Constructible.Model.ordinalLCarrier alpha) :=
  (isVonNeumannOrdinal_lCarrier_iff _).mpr
    (ZFSet.isOrdinal_toZFSet alpha)

private theorem not_injects_externalHartogsBound
    (base : Constructible.Model.LCarrier.{u}) :
    ¬Injects Constructible.Model.lCarrierMem
      (Constructible.Model.ordinalLCarrier (externalHartogsBound base))
      base := by
  intro hinjects
  have hinternal := hinjects.cardinalMk_le
  change
    #(Constructible.Model.InternalCarrier
        (Constructible.Model.ordinalLCarrier (externalHartogsBound base))) ≤
      #(Constructible.Model.InternalCarrier base) at hinternal
  have hraw :
      #(ZFCarrier
          (Constructible.Model.ordinalLCarrier
            (externalHartogsBound base)).1) ≤
        #(ZFCarrier base.1) := by
    calc
      #(ZFCarrier
          (Constructible.Model.ordinalLCarrier
            (externalHartogsBound base)).1) =
          #(Constructible.Model.InternalCarrier
            (Constructible.Model.ordinalLCarrier
              (externalHartogsBound base))) :=
        Cardinal.mk_congr
          (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv
            (Constructible.Model.ordinalLCarrier
              (externalHartogsBound base)))
      _ ≤ #(Constructible.Model.InternalCarrier base) := hinternal
      _ = #(ZFCarrier base.1) :=
        Cardinal.mk_congr
          (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv base).symm
  have hlift :
      Cardinal.lift
          ((externalHartogsBound base).toZFSet.card) ≤
        Cardinal.lift (base.1.card) := by
    simpa only [Constructible.Model.ordinalLCarrier_val,
      ZFSet.cardinalMk_coe_sort] using hraw
  have hcard :
      (externalHartogsBound base).card ≤ base.1.card := by
    rw [Ordinal.card_toZFSet] at hlift
    exact Cardinal.lift_le.mp hlift
  rw [externalHartogsBound, Cardinal.card_ord] at hcard
  exact (Order.lt_succ base.1.card).2 hcard

/-- The ordinals which do not internally inject into `base`. -/
def internalHartogsObstructions
    (base : Constructible.Model.LCarrier.{u}) : Set Ordinal.{u} :=
  {alpha | ¬Injects Constructible.Model.lCarrierMem
    (Constructible.Model.ordinalLCarrier alpha) base}

theorem internalHartogsObstructions_nonempty
    (base : Constructible.Model.LCarrier.{u}) :
    (internalHartogsObstructions base).Nonempty := by
  exact ⟨externalHartogsBound base,
    not_injects_externalHartogsBound base⟩

/-- The least ordinal which has no injection into `base` represented in
`L`. -/
noncomputable def internalHartogsOrdinal
    (base : Constructible.Model.LCarrier.{u}) : Ordinal.{u} :=
  sInf (internalHartogsObstructions base)

/-- The internal Hartogs ordinal, packaged as a constructible set. -/
noncomputable def internalHartogsLCarrier
    (base : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  Constructible.Model.ordinalLCarrier (internalHartogsOrdinal base)

theorem internalHartogsOrdinal_is_obstruction
    (base : Constructible.Model.LCarrier.{u}) :
    internalHartogsOrdinal base ∈ internalHartogsObstructions base := by
  exact csInf_mem (internalHartogsObstructions_nonempty base)

/-- The least obstruction has exactly the internal Hartogs property. -/
theorem internalHartogsLCarrier_isHartogsNumber
    (base : Constructible.Model.LCarrier.{u}) :
    IsHartogsNumber Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) := by
  refine ⟨ordinalLCarrier_isVonNeumannOrdinal _, ?_, ?_⟩
  · exact internalHartogsOrdinal_is_obstruction base
  · intro alpha halpha
    obtain ⟨beta, hbeta, hvalue⟩ :=
      Ordinal.mem_toZFSet_iff.mp halpha
    have halphaEq :
        alpha = Constructible.Model.ordinalLCarrier beta := by
      apply Subtype.ext
      exact hvalue.symm
    rw [halphaEq]
    by_contra hnotInjects
    have hle : internalHartogsOrdinal base ≤ beta :=
      csInf_le' hnotInjects
    exact (not_le_of_gt hbeta) hle

/-- Every constructible set has a Hartogs number computed with internally
represented injections. -/
theorem exists_internalHartogsNumber
    (base : Constructible.Model.LCarrier.{u}) :
    ∃ hartogs : Constructible.Model.LCarrier.{u},
      IsHartogsNumber Constructible.Model.lCarrierMem base hartogs :=
  ⟨internalHartogsLCarrier base,
    internalHartogsLCarrier_isHartogsNumber base⟩

/-! ## Object-language formulas -/

/-- The graph has at most one preimage in `domain` at `y`. -/
def atMostOnePreimageAt {n : Nat}
    (graph domain y : Fin n) : FOFormula n :=
  FOFormula.boundedAll domain
    (FOFormula.imp
      (graphValueAt graph.castSucc (Fin.last n) y.castSucc)
      (FOFormula.boundedAll domain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            (Fin.last (n + 1)) y.castSucc.castSucc)
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_atMostOnePreimageAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (graph domain y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (atMostOnePreimageAt graph domain y) s ↔
      HasAtMostOnePreimage E (s graph) (s domain) (s y) := by
  simp only [atMostOnePreimageAt,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_imp,
    FOFormula.Satisfies, satisfies_graphValueAt,
    snoc_last, snoc_castSucc,
    HasAtMostOnePreimage]

/-- `graph` codes an injection from `domain` into `codomain`. -/
def injectionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  .conj (graphBetweenAt graph domain codomain)
    (.conj
      (FOFormula.boundedAll domain
        (uniqueImageAt graph.castSucc
          (Fin.last n) codomain.castSucc))
      (FOFormula.boundedAll codomain
        (atMostOnePreimageAt graph.castSucc
          domain.castSucc (Fin.last n))))

@[simp]
theorem satisfies_injectionAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (injectionAt graph domain codomain) s ↔
      IsInjection E (s graph) (s domain) (s codomain) := by
  simp only [injectionAt, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    satisfies_uniqueImageAt, satisfies_atMostOnePreimageAt,
    snoc_last, snoc_castSucc, IsInjection]

/-- There is a set coding an injection from `domain` to `codomain`. -/
def injectsAt {n : Nat} (domain codomain : Fin n) : FOFormula n :=
  .ex (injectionAt (Fin.last n) domain.castSucc codomain.castSucc)

@[simp]
theorem satisfies_injectsAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (injectsAt domain codomain) s ↔
      Injects E (s domain) (s codomain) := by
  simp only [injectsAt, FOFormula.Satisfies,
    satisfies_injectionAt, snoc_last, snoc_castSucc, Injects]

/-- `hartogs` is the least ordinal not injecting into `base`. -/
def hartogsAt {n : Nat} (base hartogs : Fin n) : FOFormula n :=
  .conj (isOrdinalAt hartogs)
    (.conj
      (.neg (injectsAt hartogs base))
      (FOFormula.boundedAll hartogs
        (injectsAt (Fin.last n) base.castSucc)))

@[simp]
theorem satisfies_hartogsAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (base hartogs : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (hartogsAt base hartogs) s ↔
      IsHartogsNumber E (s base) (s hartogs) := by
  simp only [hartogsAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt, satisfies_injectsAt,
    FOFormula.satisfies_boundedAll, snoc_last, snoc_castSucc,
    IsHartogsNumber]

end Constructible.ContinuumFormula
