/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalSchroederBernstein
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryGeneratorInternalOrder
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem

/-!
# Internal cardinal representatives

This file constructs the order-type interface needed to turn the internally
represented well-order of a constructible set into an internally represented
bijection with an ordinal.  Every graph appearing in the semantic statements
is an element of `L`; an ambient Lean equivalence is not used as an internal
bijection witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Semantic order-type predicates -/

/-- `predecessors` consists exactly of the members of `domain` below `point`
in the relation represented by `relation`. -/
def IsPredecessorSetOf {A : Type u} (E : A -> A -> Prop)
    (predecessors relation domain point : A) : Prop :=
  forall z : A, E z predecessors <->
    E z domain /\ GraphValue E relation z point

/-- A set-coded bijection which also preserves and reflects the represented
order. -/
def IsOrderIsomorphism {A : Type u} (E : A -> A -> Prop)
    (graph relation domain ordinal : A) : Prop :=
  IsBijection E graph domain ordinal /\
    forall z w imageZ imageW : A,
      E z domain -> E w domain ->
        GraphValue E graph z imageZ ->
          GraphValue E graph w imageW ->
            (GraphValue E relation z w <-> E imageZ imageW)

/-- `ordinal` is the order type of the strict initial segment below `point`.
Both the predecessor set and the order-isomorphism graph are internal sets. -/
def IsInitialSegmentOrderType {A : Type u} (E : A -> A -> Prop)
    (relation domain point ordinal : A) : Prop :=
  IsVonNeumannOrdinal E ordinal /\
    exists predecessors : A,
      IsPredecessorSetOf E predecessors relation domain point /\
        exists graph : A,
          IsOrderIsomorphism E graph relation predecessors ordinal

/-! ## Object-language formulas -/

/-- `predecessors` is the represented strict initial segment below `point`. -/
def predecessorSetAt {n : Nat}
    (predecessors relation domain point : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) predecessors.castSucc)
      (.conj
        (.mem (Fin.last n) domain.castSucc)
        (graphValueAt relation.castSucc (Fin.last n) point.castSucc)))

@[simp]
theorem satisfies_predecessorSetAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (predecessors relation domain point : Fin n)
    (s : Tuple A n) :
    FOFormula.Satisfies E
        (predecessorSetAt predecessors relation domain point) s <->
      IsPredecessorSetOf E (s predecessors) (s relation)
        (s domain) (s point) := by
  simp only [predecessorSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc,
    IsPredecessorSetOf]

/-- A represented bijection preserves and reflects the source relation. -/
def orderPreservingAt {n : Nat}
    (graph relation domain : Fin n) : FOFormula n :=
  FOFormula.boundedAll domain
    (FOFormula.boundedAll domain.castSucc
      (FOFormula.all (FOFormula.all
        (FOFormula.imp
          (.conj
            (graphValueAt
              graph.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 2)).castSucc)
            (graphValueAt
              graph.castSucc.castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc
              (Fin.last (n + 3))))
          (FOFormula.biimp
            (graphValueAt
              relation.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc)
            (.mem (Fin.last (n + 2)).castSucc
              (Fin.last (n + 3))))))))

@[simp]
theorem satisfies_orderPreservingAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (graph relation domain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (orderPreservingAt graph relation domain) s <->
      forall z w imageZ imageW : A,
        E z (s domain) -> E w (s domain) ->
          GraphValue E (s graph) z imageZ ->
            GraphValue E (s graph) w imageW ->
              (GraphValue E (s relation) z w <-> E imageZ imageW) := by
  simp only [orderPreservingAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc]
  constructor
  · intro h z w imageZ imageW hz hw hzImage hwImage
    exact h z hz w hw imageZ imageW ⟨hzImage, hwImage⟩
  · intro h z hz w hw imageZ imageW hImages
    exact h z w imageZ imageW hz hw hImages.1 hImages.2

/-- `graph` is an internal order isomorphism from `domain` to `ordinal`. -/
def orderIsomorphismAt {n : Nat}
    (graph relation domain ordinal : Fin n) : FOFormula n :=
  .conj (bijectionAt graph domain ordinal)
    (orderPreservingAt graph relation domain)

@[simp]
theorem satisfies_orderIsomorphismAt {A : Type u}
    (E : A -> A -> Prop) {n : Nat}
    (graph relation domain ordinal : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (orderIsomorphismAt graph relation domain ordinal) s <->
      IsOrderIsomorphism E (s graph) (s relation)
        (s domain) (s ordinal) := by
  simp only [orderIsomorphismAt, FOFormula.Satisfies,
    satisfies_bijectionAt, satisfies_orderPreservingAt,
    IsOrderIsomorphism]

/-- Layout `[relation, domain, point, ordinal]`: the last coordinate is the
order type of the strict initial segment below `point`. -/
def initialSegmentOrderTypeAt : FOFormula 4 :=
  .conj (isOrdinalAt (3 : Fin 4))
    (.ex
      (.conj
        (predecessorSetAt (Fin.last 4)
          (0 : Fin 4).castSucc (1 : Fin 4).castSucc
          (2 : Fin 4).castSucc)
        (.ex
          (orderIsomorphismAt (Fin.last 5)
            (0 : Fin 4).castSucc.castSucc
            (Fin.last 4).castSucc
            (3 : Fin 4).castSucc.castSucc))))

private theorem initialSegmentOrderType_assignment
    (relation domain point ordinal predecessors graph : A) :
    snoc (snoc ![relation, domain, point, ordinal] predecessors) graph =
      ![relation, domain, point, ordinal, predecessors, graph] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_initialSegmentOrderTypeAt {A : Type u}
    (E : A -> A -> Prop) (relation domain point ordinal : A) :
    FOFormula.Satisfies E initialSegmentOrderTypeAt
        ![relation, domain, point, ordinal] <->
      IsInitialSegmentOrderType E relation domain point ordinal := by
  simp only [initialSegmentOrderTypeAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt]
  apply and_congr_right
  intro _hOrdinal
  apply exists_congr
  intro predecessors
  apply and_congr
  · exact satisfies_predecessorSetAt E
      (Fin.last 4) (0 : Fin 4).castSucc
        (1 : Fin 4).castSucc (2 : Fin 4).castSucc
      (snoc ![relation, domain, point, ordinal] predecessors)
  · apply exists_congr
    intro graph
    rw [initialSegmentOrderType_assignment]
    exact satisfies_orderIsomorphismAt E
      (Fin.last 5) (0 : Fin 4).castSucc.castSucc
      (Fin.last 4).castSucc (3 : Fin 4).castSucc.castSucc
      ![relation, domain, point, ordinal, predecessors, graph]

/-- Select `[relation, domain, point, ordinal]` from
`[relation, domain, bound, point, ordinal]`. -/
def beforeOrderTypeRename : Fin 4 -> Fin 5 :=
  ![0, 1, 3, 4]

private theorem comp_beforeOrderTypeRename {A : Type u}
    (relation domain bound point ordinal : A) :
    (fun i => ![relation, domain, bound, point, ordinal]
      (beforeOrderTypeRename i)) =
      ![relation, domain, point, ordinal] := by
  funext i
  fin_cases i <;> rfl

/-- Layout `[relation, domain, bound, point, ordinal]`: `point` is below
`bound` and `ordinal` is the represented order type at `point`. -/
def beforeOrderTypeRelation : FOFormula 5 :=
  .conj (.mem (3 : Fin 5) (1 : Fin 5))
    (.conj (graphValueAt (0 : Fin 5) (3 : Fin 5) (2 : Fin 5))
      (FOFormula.rename beforeOrderTypeRename initialSegmentOrderTypeAt))

@[simp]
theorem satisfies_beforeOrderTypeRelation
    (relation domain bound point ordinal : LCarrier.{u}) :
    FOFormula.Satisfies LMem beforeOrderTypeRelation
        ![relation, domain, bound, point, ordinal] <->
      point.1 ∈ domain.1 /\ GraphRel relation point bound /\
        IsInitialSegmentOrderType LMem relation domain point ordinal := by
  simp only [beforeOrderTypeRelation, FOFormula.Satisfies,
    satisfies_graphValueAt, FOFormula.satisfies_rename,
    comp_beforeOrderTypeRename, satisfies_initialSegmentOrderTypeAt]
  rw [graphValue_lCarrier_iff_graphRel]
  change
    (point.1 ∈ domain.1 /\ GraphRel relation point bound /\
      IsInitialSegmentOrderType LMem relation domain point ordinal) <-> _
  rfl

/-- Layout `[relation, domain, point, ordinal]`: restrict the order-type
relation to members of `domain`. -/
def memberOrderTypeRelation : FOFormula 4 :=
  .conj (.mem (2 : Fin 4) (1 : Fin 4)) initialSegmentOrderTypeAt

@[simp]
theorem satisfies_memberOrderTypeRelation
    (relation domain point ordinal : LCarrier.{u}) :
    FOFormula.Satisfies LMem memberOrderTypeRelation
        ![relation, domain, point, ordinal] <->
      point.1 ∈ domain.1 /\
        IsInitialSegmentOrderType LMem relation domain point ordinal := by
  simp only [memberOrderTypeRelation, FOFormula.Satisfies,
    satisfies_initialSegmentOrderTypeAt]
  change
    (point.1 ∈ domain.1 /\
      IsInitialSegmentOrderType LMem relation domain point ordinal) <-> _
  rfl

/-! ## Small carriers and represented bijections -/

/-- The actual equivalence induced by an internally represented bijection.
This is used only to reason about the represented graph; the internal witness
remains the graph supplied by `h`. -/
noncomputable def IsBijection.toEquiv
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain : A}
    (h : IsBijection E graph domain codomain) :
    RelationCarrier E domain ≃ RelationCarrier E codomain := by
  let f := h.toIsInjection.toFun
  apply Equiv.ofBijective f
  constructor
  · exact h.toIsInjection.toFun_injective
  · intro y
    rcases h.2.2 y.1 y.2 with ⟨x, hx, hxy, _huniquePreimage⟩
    let xDomain : RelationCarrier E domain := ⟨x, hx⟩
    rcases h.2.1 x hx with
      ⟨value, hvalueCodomain, hxvalue, huniqueValue⟩
    have hchosenValue : (f xDomain).1 = value :=
      huniqueValue (f xDomain) (f xDomain).2
        (h.toIsInjection.toFun_graphValue xDomain)
    have hyValue : y.1 = value :=
      huniqueValue y.1 y.2 hxy
    refine ⟨xDomain, Subtype.ext ?_⟩
    exact hchosenValue.trans hyValue.symm

/-- Transport a represented bijection to the small `ZFCarrier`s of its
domain and codomain. -/
noncomputable def IsBijection.toZFCarrierEquiv
    {graph domain codomain : LCarrier.{u}}
    (h : IsBijection LMem graph domain codomain) :
    ZFCarrier domain.1 ≃ ZFCarrier codomain.1 :=
  ((Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv domain).trans
    h.toEquiv).trans
    (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv codomain).symm

/-- The relation on the small carrier represented by an internal graph. -/
def rawGraphRel (relation domain : LCarrier.{u}) :
    ZFCarrier domain.1 -> ZFCarrier domain.1 -> Prop :=
  Constructible.Godel.RudimentaryTerm.generatorPairRel relation.1

/-- Package a member of a constructible set as an element of `LCarrier`. -/
def rawMemberLCarrier (domain : LCarrier.{u})
    (x : ZFCarrier domain.1) : LCarrier.{u} :=
  ⟨x.1, Constructible.mem_L_of_mem x.2 domain.2⟩

@[simp]
theorem rawMemberLCarrier_val (domain : LCarrier.{u})
    (x : ZFCarrier domain.1) :
    (rawMemberLCarrier domain x).1 = x.1 :=
  rfl

@[simp]
theorem rawGraphRel_iff_graphRel
    (relation domain : LCarrier.{u})
    (x y : ZFCarrier domain.1) :
    rawGraphRel relation domain x y <->
      GraphRel relation (rawMemberLCarrier domain x)
        (rawMemberLCarrier domain y) := by
  rfl

/-- An internally represented well-order is a well-order on the genuinely
small carrier of the underlying `ZFSet`. -/
theorem rawGraphRel_isWellOrder
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    IsWellOrder (ZFCarrier domain.1) (rawGraphRel relation domain) := by
  exact
    Constructible.Godel.RudimentaryTerm.generatorPairRel_isWellOrder_of_internal
      domain relation hwell

/-- A universe-small presentation of the members of a `ZFSet`. -/
abbrev SmallZFCarrier (x : ZFSet.{u}) :=
  Shrink.{u} (ZFCarrier x)

/-- Pull the represented relation back to the small presentation. -/
def smallGraphRel (relation domain : LCarrier.{u}) :
    SmallZFCarrier domain.1 -> SmallZFCarrier domain.1 -> Prop :=
  InvImage (rawGraphRel relation domain)
    (equivShrink (ZFCarrier domain.1)).symm

theorem smallGraphRel_isWellOrder
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) := by
  letI : IsWellOrder (ZFCarrier domain.1)
      (rawGraphRel relation domain) :=
    rawGraphRel_isWellOrder relation domain hwell
  exact
    { wf := InvImage.wf (equivShrink (ZFCarrier domain.1)).symm
        (IsWellFounded.wf : WellFounded (rawGraphRel relation domain))
      trichotomous :=
        (InvImage.trichotomous
          (r := rawGraphRel relation domain)
          (equivShrink (ZFCarrier domain.1)).symm.injective).trichotomous }

/-! ## The canonical small carrier of a von Neumann ordinal -/

/-- Send an element of the canonical type of `alpha` to its von Neumann set
code in the ordinary (large) element subtype. -/
noncomputable def ordinalToRawZFCarrier (alpha : Ordinal.{u}) :
    alpha.ToType -> ZFCarrier alpha.toZFSet :=
  fun i => ⟨(i : Ordinal.{u}).toZFSet,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr i.toOrd.2⟩

theorem ordinalToRawZFCarrier_injective (alpha : Ordinal.{u}) :
    Function.Injective (ordinalToRawZFCarrier alpha) := by
  intro i j hij
  have hord : (i : Ordinal.{u}) = (j : Ordinal.{u}) := by
    apply Ordinal.toZFSet_injective
    exact congrArg Subtype.val hij
  apply (Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm.injective
  apply Subtype.ext
  exact hord

theorem ordinalToRawZFCarrier_surjective (alpha : Ordinal.{u}) :
    Function.Surjective (ordinalToRawZFCarrier alpha) := by
  intro z
  rcases Ordinal.mem_toZFSet_iff.mp z.2 with ⟨beta, hbeta, hvalue⟩
  let i : alpha.ToType := Ordinal.ToType.mk ⟨beta, hbeta⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  change (i : Ordinal.{u}).toZFSet = z.1
  have hi : (i : Ordinal.{u}) = beta := by
    exact congrArg Subtype.val
      ((Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm_apply_apply
        ⟨beta, hbeta⟩)
  rw [hi]
  exact hvalue

/-- The same canonical map, now landing in the small carrier. -/
noncomputable def ordinalToSmallZFCarrier (alpha : Ordinal.{u}) :
    alpha.ToType -> SmallZFCarrier alpha.toZFSet :=
  fun i => equivShrink (ZFCarrier alpha.toZFSet)
    (ordinalToRawZFCarrier alpha i)

theorem ordinalToSmallZFCarrier_injective (alpha : Ordinal.{u}) :
    Function.Injective (ordinalToSmallZFCarrier alpha) :=
  (equivShrink (ZFCarrier alpha.toZFSet)).injective.comp
    (ordinalToRawZFCarrier_injective alpha)

theorem ordinalToSmallZFCarrier_surjective (alpha : Ordinal.{u}) :
    Function.Surjective (ordinalToSmallZFCarrier alpha) := by
  intro z
  let zRaw := (equivShrink (ZFCarrier alpha.toZFSet)).symm z
  rcases ordinalToRawZFCarrier_surjective alpha zRaw with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  change equivShrink (ZFCarrier alpha.toZFSet)
      (ordinalToRawZFCarrier alpha i) = z
  rw [hi]
  exact (equivShrink (ZFCarrier alpha.toZFSet)).apply_symm_apply z

/-- Membership pulled back to the small presentation of an ordinal. -/
def smallOrdinalMem (alpha : Ordinal.{u}) :
    SmallZFCarrier alpha.toZFSet ->
      SmallZFCarrier alpha.toZFSet -> Prop :=
  InvImage (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
    (equivShrink (ZFCarrier alpha.toZFSet)).symm

instance smallOrdinalMem_isWellOrder (alpha : Ordinal.{u}) :
    IsWellOrder (SmallZFCarrier alpha.toZFSet)
      (smallOrdinalMem alpha) := by
  letI hraw : IsWellOrder (ZFCarrier alpha.toZFSet)
      (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1) :=
    (ZFSet.isOrdinal_toZFSet alpha).isWellOrder
  change IsWellOrder _
    (InvImage (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
      (equivShrink (ZFCarrier alpha.toZFSet)).symm)
  exact
    { wf := InvImage.wf
        (r := fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
        (equivShrink (ZFCarrier alpha.toZFSet)).symm
        (IsWellFounded.wf : WellFounded
          (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)),
      trichotomous :=
        (InvImage.trichotomous
          (r := fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
          (equivShrink (ZFCarrier alpha.toZFSet)).symm.injective).trichotomous }

noncomputable def ordinalToSmallZFCarrierEquiv (alpha : Ordinal.{u}) :
    alpha.ToType ≃ SmallZFCarrier alpha.toZFSet :=
  Equiv.ofBijective (ordinalToSmallZFCarrier alpha)
    ⟨ordinalToSmallZFCarrier_injective alpha,
      ordinalToSmallZFCarrier_surjective alpha⟩

@[simp]
theorem ordinalToSmallZFCarrierEquiv_apply
    (alpha : Ordinal.{u}) (i : alpha.ToType) :
    ordinalToSmallZFCarrierEquiv alpha i =
      ordinalToSmallZFCarrier alpha i := by
  rfl

/-- The small members of `alpha.toZFSet`, ordered by membership, have order
type exactly `alpha`. -/
noncomputable def ordinalToSmallZFCarrierRelIso (alpha : Ordinal.{u}) :
    ((fun i j : alpha.ToType => i < j) ≃r
      smallOrdinalMem alpha) where
  toEquiv := ordinalToSmallZFCarrierEquiv alpha
  map_rel_iff' {i j} := by
    rw [ordinalToSmallZFCarrierEquiv_apply,
      ordinalToSmallZFCarrierEquiv_apply]
    simp only [smallOrdinalMem, ordinalToSmallZFCarrier, InvImage,
      Equiv.symm_apply_apply, ordinalToRawZFCarrier]
    rw [Ordinal.toZFSet_mem_toZFSet_iff]
    change i.toOrd < j.toOrd <-> i < j
    exact (Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm.lt_iff_lt

theorem type_smallZFCarrier_ordinal (alpha : Ordinal.{u}) :
    Ordinal.type (smallOrdinalMem alpha) =
      alpha := by
  letI : IsWellOrder alpha.ToType (fun i j => i < j) := inferInstance
  calc
    Ordinal.type (smallOrdinalMem alpha) =
        Ordinal.type (fun i j : alpha.ToType => i < j) :=
      (ordinalToSmallZFCarrierRelIso alpha).symm.ordinalType_congr
    _ = alpha := Ordinal.type_toType alpha

/-! ## From internal ordinal representatives to internal cardinals -/

/-- Internal equinumerosity is transitive in `LCarrier`.  The proof composes
internal injections in both directions and invokes the already internalized
Cantor--Schroeder--Bernstein construction. -/
theorem Equinumerous.trans_lCarrier
    {a b c : LCarrier.{u}}
    (hab : Equinumerous LMem a b)
    (hbc : Equinumerous LMem b c) :
    Equinumerous LMem a c := by
  apply injects_antisymm_lCarrier
  · exact hab.injects.trans_lCarrier hbc.injects
  · exact hbc.symm_lCarrier.injects.trans_lCarrier
      hab.symm_lCarrier.injects

/-- The ordinals internally equinumerous with `a`. -/
def internalOrdinalRepresentatives (a : LCarrier.{u}) : Set Ordinal.{u} :=
  {alpha | Equinumerous LMem a (ordinalLCarrier alpha)}

/-- An internal ordinal representative makes the candidate class nonempty. -/
theorem internalOrdinalRepresentatives_nonempty
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    (internalOrdinalRepresentatives a).Nonempty := by
  rcases h with ⟨alpha, halpha⟩
  exact ⟨alpha, halpha⟩

/-- The least ordinal internally equinumerous with `a`. -/
noncomputable def internalCardinalRepresentativeOrdinal
    (a : LCarrier.{u}) : Ordinal.{u} :=
  sInf (internalOrdinalRepresentatives a)

/-- Whenever an internal ordinal representative exists, the least candidate
is itself still witnessed by an internal bijection. -/
theorem internalCardinalRepresentativeOrdinal_mem
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    internalCardinalRepresentativeOrdinal a ∈
      internalOrdinalRepresentatives a := by
  exact csInf_mem (internalOrdinalRepresentatives_nonempty a h)

/-- The least internally represented ordinal equinumerous with `a` is an
internal cardinal.  Minimality is tested only against internally represented
bijections, exactly as required by `IsCardinal LMem`. -/
theorem internalCardinalRepresentative_isCardinal
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    IsCardinal LMem
      (ordinalLCarrier (internalCardinalRepresentativeOrdinal a)) := by
  let beta := internalCardinalRepresentativeOrdinal a
  have hbetaCandidate : beta ∈ internalOrdinalRepresentatives a :=
    internalCardinalRepresentativeOrdinal_mem a h
  have haBeta : Equinumerous LMem a (ordinalLCarrier beta) :=
    hbetaCandidate
  constructor
  · exact (isVonNeumannOrdinal_lCarrier_iff
      (ordinalLCarrier beta)).mpr (ZFSet.isOrdinal_toZFSet beta)
  · intro gamma hgamma hgammaBeta
    have hgammaRaw : gamma.1 ∈ beta.toZFSet := by
      change gamma.1 ∈ (ordinalLCarrier beta).1 at hgamma
      simpa only [ordinalLCarrier_val] using hgamma
    rcases Ordinal.mem_toZFSet_iff.mp hgammaRaw with
      ⟨delta, hdeltaBeta, hdeltaValue⟩
    have hgammaEq : gamma = ordinalLCarrier delta := by
      apply Subtype.ext
      exact hdeltaValue.symm
    have haDelta : Equinumerous LMem a (ordinalLCarrier delta) := by
      rw [← hgammaEq]
      exact haBeta.trans_lCarrier hgammaBeta.symm_lCarrier
    have hbetaDelta : beta <= delta :=
      csInf_le' (show delta ∈ internalOrdinalRepresentatives a from haDelta)
    exact (not_le_of_gt hdeltaBeta) hbetaDelta

/-- Every internal ordinal representative therefore yields a genuine
internal cardinal representative. -/
theorem exists_internalCardinalRepresentative_of_ordinalRepresentative
    (a : LCarrier.{u})
    (h : exists alpha : Ordinal.{u},
      Equinumerous LMem a (ordinalLCarrier alpha)) :
    exists cardinal : LCarrier.{u},
      IsCardinal LMem cardinal /\ Equinumerous LMem a cardinal := by
  exact ⟨ordinalLCarrier (internalCardinalRepresentativeOrdinal a),
    internalCardinalRepresentative_isCardinal a h,
    internalCardinalRepresentativeOrdinal_mem a h⟩

end Constructible.ContinuumFormula
