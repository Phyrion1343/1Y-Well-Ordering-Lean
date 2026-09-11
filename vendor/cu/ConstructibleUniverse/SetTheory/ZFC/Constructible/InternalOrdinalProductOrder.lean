/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeWitnessConstruction

/-!
# The maximum-lexicographic order on an internal ordinal square

For a von Neumann ordinal `kappa`, this file constructs the standard order on
`kappa x kappa`: first compare the maximum of the two coordinates, and then
compare the coordinates lexicographically.  The relation is obtained by
Separation from a fixed first-order formula, so its graph is an actual member
of the constructible universe.

This is the well-order used in the usual proof that every infinite cardinal
absorbs its square.  No ambient cardinal comparison is used as an internal
function witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Formula and exact semantics -/

/-- `maximum` is the larger of `left` and `right` in a strict linear order. -/
def IsMaximumOf {A : Type u} (E : A -> A -> Prop)
    (left right maximum : A) : Prop :=
  ((E left right \/ left = right) /\ maximum = right) \/
    (E right left /\ maximum = left)

/-- Formula version of `IsMaximumOf`. -/
def maximumAt {n : Nat} (left right maximum : Fin n) : FOFormula n :=
  .disj
    (.conj
      (.disj (.mem left right) (.eq left right))
      (.eq maximum right))
    (.conj (.mem right left) (.eq maximum left))

@[simp]
theorem satisfies_maximumAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (left right maximum : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (maximumAt left right maximum) s <->
      IsMaximumOf E (s left) (s right) (s maximum) := by
  simp [maximumAt, IsMaximumOf]

/-- Each input to a membership maximum belongs to the successor of that
maximum. -/
theorem IsMaximumOf.mem_successor_lCarrier
    {left right maximum : LCarrier.{u}}
    (hmaximum : IsMaximumOf LMem left right maximum) :
    left.1 ∈ (successorLCarrier maximum).1 /\
      right.1 ∈ (successorLCarrier maximum).1 := by
  rw [successorLCarrier_val,
    ZFSet.mem_insert_iff, ZFSet.mem_insert_iff]
  rcases hmaximum with ⟨hleftRight, hmaximum⟩ |
    ⟨hrightLeft, hmaximum⟩
  · rw [hmaximum]
    constructor
    · rcases hleftRight with hmem | heq
      · exact Or.inr hmem
      · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inl rfl
  · rw [hmaximum]
    exact ⟨Or.inl rfl, Or.inr hrightLeft⟩

/-- Membership maxima are unique. -/
theorem IsMaximumOf.unique_lCarrier
    {left right first second : LCarrier.{u}}
    (hfirst : IsMaximumOf LMem left right first)
    (hsecond : IsMaximumOf LMem left right second) :
    first = second := by
  rcases hfirst with ⟨hleftRight, hfirst⟩ |
    ⟨hrightLeft, hfirst⟩ <;>
    rcases hsecond with ⟨hleftRight', hsecond⟩ |
      ⟨hrightLeft', hsecond⟩
  · exact hfirst.trans hsecond.symm
  · exfalso
    rcases hleftRight with hmem | heq
    · exact ZFSet.mem_asymm hmem hrightLeft'
    · rw [← heq] at hrightLeft'
      exact ZFSet.mem_irrefl left.1 hrightLeft'
  · exfalso
    rcases hleftRight' with hmem | heq
    · exact ZFSet.mem_asymm hmem hrightLeft
    · rw [← heq] at hrightLeft
      exact ZFSet.mem_irrefl left.1 hrightLeft
  · exact hfirst.trans hsecond.symm

/-- Two members of a von Neumann ordinal have a membership maximum. -/
theorem exists_maximum_lCarrier_of_mem_ordinal
    {kappa left right : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hleft : left.1 ∈ kappa.1) (hright : right.1 ∈ kappa.1) :
    exists maximum : LCarrier.{u},
      IsMaximumOf LMem left right maximum := by
  have hkappaRaw : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
  have hleftOrdinal := hkappaRaw.mem hleft
  have hrightOrdinal := hkappaRaw.mem hright
  rcases ZFSet.IsOrdinal.mem_trichotomous hleftOrdinal hrightOrdinal with
    hlt | heq | hgt
  · exact ⟨right, Or.inl ⟨Or.inl hlt, rfl⟩⟩
  · exact ⟨right, Or.inl ⟨Or.inr (Subtype.ext heq), rfl⟩⟩
  · exact ⟨left, Or.inr ⟨hgt, rfl⟩⟩

/-- Compare two coordinate pairs by maximum first and lexicographically on a
tie. -/
def MaximumLexComponents {A : Type u} (E : A -> A -> Prop)
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum : A) :
    Prop :=
  IsMaximumOf E leftFirst leftSecond leftMaximum /\
    IsMaximumOf E rightFirst rightSecond rightMaximum /\
      (E leftMaximum rightMaximum \/
        (leftMaximum = rightMaximum /\
          (E leftFirst rightFirst \/
            (leftFirst = rightFirst /\ E leftSecond rightSecond))))

/-- The maximum-lexicographic comparison embedded at arbitrary coordinates. -/
def maximumLexComponentsAt {n : Nat}
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum :
      Fin n) : FOFormula n :=
  .conj
    (maximumAt leftFirst leftSecond leftMaximum)
    (.conj
      (maximumAt rightFirst rightSecond rightMaximum)
      (.disj
        (.mem leftMaximum rightMaximum)
        (.conj
          (.eq leftMaximum rightMaximum)
          (.disj
            (.mem leftFirst rightFirst)
            (.conj
              (.eq leftFirst rightFirst)
              (.mem leftSecond rightSecond))))))

@[simp]
theorem satisfies_maximumLexComponentsAt {A : Type u}
    (E : A -> A -> Prop) {n : Nat}
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum :
      Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (maximumLexComponentsAt leftFirst leftSecond rightFirst rightSecond
          leftMaximum rightMaximum) s <->
      MaximumLexComponents E
        (s leftFirst) (s leftSecond) (s rightFirst) (s rightSecond)
        (s leftMaximum) (s rightMaximum) := by
  simp [maximumLexComponentsAt, MaximumLexComponents]

/-- The semantic relation on two Kuratowski pair codes. -/
def OrdinalPairMaximumLexRel {A : Type u} (E : A -> A -> Prop)
    (left right : A) : Prop :=
  exists leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum : A,
    IsKuratowskiPairOf E left leftFirst leftSecond /\
      IsKuratowskiPairOf E right rightFirst rightSecond /\
        MaximumLexComponents E leftFirst leftSecond rightFirst rightSecond
          leftMaximum rightMaximum

/-- Layout `(leftPair,rightPair)`.  The six witnesses are the four coordinates
and their two maxima. -/
def ordinalPairMaximumLexFormula : FOFormula 2 :=
  .ex (.ex (.ex (.ex (.ex (.ex
    (.conj
      (kuratowskiPairAt (0 : Fin 8) (2 : Fin 8) (3 : Fin 8))
      (.conj
        (kuratowskiPairAt (1 : Fin 8) (4 : Fin 8) (5 : Fin 8))
        (maximumLexComponentsAt
          (2 : Fin 8) (3 : Fin 8) (4 : Fin 8) (5 : Fin 8)
          (6 : Fin 8) (7 : Fin 8)))))))))

private theorem ordinalPairMaximumLex_assignment
    (left right leftFirst leftSecond rightFirst rightSecond
      leftMaximum rightMaximum : LCarrier.{u}) :
    snoc (snoc (snoc (snoc (snoc (snoc ![left, right]
      leftFirst) leftSecond) rightFirst) rightSecond) leftMaximum) rightMaximum =
      ![left, right, leftFirst, leftSecond, rightFirst, rightSecond,
        leftMaximum, rightMaximum] := by
  simp [Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_ordinalPairMaximumLexFormula
    (left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem ordinalPairMaximumLexFormula ![left, right] <->
      OrdinalPairMaximumLexRel LMem left right := by
  simp only [ordinalPairMaximumLexFormula, FOFormula.Satisfies]
  apply exists_congr
  intro leftFirst
  apply exists_congr
  intro leftSecond
  apply exists_congr
  intro rightFirst
  apply exists_congr
  intro rightSecond
  apply exists_congr
  intro leftMaximum
  apply exists_congr
  intro rightMaximum
  rw [ordinalPairMaximumLex_assignment]
  simp only [satisfies_kuratowskiPairAt,
    satisfies_maximumLexComponentsAt]
  rfl

/-! ## The represented relation -/

/-- The canonical Separation graph of the maximum-lexicographic relation on
`kappa x kappa`. -/
noncomputable def ordinalPairMaximumLexGraph (kappa : LCarrier.{u}) :
    LCarrier.{u} :=
  canonicalDefinableRelationGraph ordinalPairMaximumLexFormula
    (![] : Tuple LCarrier.{u} 0) (prodLCarrier kappa kappa)

@[simp]
theorem graphRel_ordinalPairMaximumLexGraph_iff
    (kappa left right : LCarrier.{u}) :
    GraphRel (ordinalPairMaximumLexGraph kappa) left right <->
      left.1 ∈ (prodLCarrier kappa kappa).1 /\
        right.1 ∈ (prodLCarrier kappa kappa).1 /\
          OrdinalPairMaximumLexRel LMem left right := by
  rw [ordinalPairMaximumLexGraph,
    graphRel_canonicalDefinableRelationGraph_iff]
  have htuple :
      snoc (snoc (![] : Tuple LCarrier.{u} 0) left) right =
        ![left, right] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, satisfies_ordinalPairMaximumLexFormula]

/-! ## The external presentation of the internal product -/

/-- Encode two internal members by their Kuratowski pair. -/
def encodeInternalProduct (kappa : LCarrier.{u})
    (point : InternalCarrier kappa × InternalCarrier kappa) :
    InternalCarrier (prodLCarrier kappa kappa) :=
  ⟨orderedPairLCarrier point.1.1 point.2.1, by
    change ZFSet.pair point.1.1.1 point.2.1.1 ∈
      ZFSet.prod kappa.1 kappa.1
    rw [ZFSet.pair_mem_prod]
    exact ⟨point.1.2, point.2.2⟩⟩

theorem encodeInternalProduct_injective (kappa : LCarrier.{u}) :
    Function.Injective (encodeInternalProduct kappa) := by
  intro left right heq
  have hraw := congrArg
    (fun point : InternalCarrier (prodLCarrier kappa kappa) => point.1.1)
    heq
  have hcoordinates :
      left.1.1.1 = right.1.1.1 /\ left.2.1.1 = right.2.1.1 := by
    apply ZFSet.pair_inj.mp
    simpa only [encodeInternalProduct, orderedPairLCarrier_val] using hraw
  apply Prod.ext
  · apply Subtype.ext
    exact Subtype.ext hcoordinates.1
  · apply Subtype.ext
    exact Subtype.ext hcoordinates.2

theorem encodeInternalProduct_surjective (kappa : LCarrier.{u}) :
    Function.Surjective (encodeInternalProduct kappa) := by
  intro point
  rcases ZFSet.mem_prod.mp point.2 with
    ⟨leftRaw, hleft, rightRaw, hright, hpoint⟩
  let left : LCarrier.{u} :=
    ⟨leftRaw, Constructible.mem_L_of_mem hleft kappa.2⟩
  let right : LCarrier.{u} :=
    ⟨rightRaw, Constructible.mem_L_of_mem hright kappa.2⟩
  let leftMember : InternalCarrier kappa := ⟨left, hleft⟩
  let rightMember : InternalCarrier kappa := ⟨right, hright⟩
  refine ⟨(leftMember, rightMember), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ZFSet.pair leftRaw rightRaw = point.1.1
  exact hpoint.symm

/-- The internal Kuratowski product has the expected external product
presentation. -/
noncomputable def internalProductEquiv (kappa : LCarrier.{u}) :
    (InternalCarrier kappa × InternalCarrier kappa) ≃
      InternalCarrier (prodLCarrier kappa kappa) :=
  Equiv.ofBijective (encodeInternalProduct kappa)
    ⟨encodeInternalProduct_injective kappa,
      encodeInternalProduct_surjective kappa⟩

/-! ## The represented relation is a well-order -/

/-- Membership on the internal members of a von Neumann ordinal is a
well-order. -/
theorem internalOrdinalMem_isWellOrder
    (kappa : LCarrier.{u})
    (hkappa : IsVonNeumannOrdinal LMem kappa) :
    IsWellOrder (InternalCarrier kappa)
      (fun left right => left.1.1 ∈ right.1.1) := by
  have hkappaRaw : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
  let embedding : InternalCarrier kappa ↪ ZFCarrier kappa.1 :=
    ⟨fun point => ⟨point.1.1, point.2⟩, by
      intro left right heq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun point : ZFCarrier kappa.1 => point.1) heq⟩
  letI : IsWellOrder (ZFCarrier kappa.1)
      (fun left right => left.1 ∈ right.1) :=
    hkappaRaw.isWellOrder
  change IsWellOrder _
    (InvImage (fun left right : ZFCarrier kappa.1 => left.1 ∈ right.1)
      embedding)
  exact (RelEmbedding.preimage embedding
    (fun left right : ZFCarrier kappa.1 => left.1 ∈ right.1)).isWellOrder

/-- The Separation graph above genuinely well-orders the internal square of
every von Neumann ordinal. -/
theorem ordinalPairMaximumLexGraph_internallyWellOrders
    (kappa : LCarrier.{u})
    (hkappa : IsVonNeumannOrdinal LMem kappa) :
    InternallyWellOrders (ordinalPairMaximumLexGraph kappa)
      (prodLCarrier kappa kappa) := by
  let baseRel : InternalCarrier kappa -> InternalCarrier kappa -> Prop :=
    fun left right => left.1.1 ∈ right.1.1
  let hbaseWell : IsWellOrder (InternalCarrier kappa) baseRel :=
    internalOrdinalMem_isWellOrder kappa hkappa
  letI : IsWellOrder (InternalCarrier kappa) baseRel := hbaseWell
  let baseOrder : LinearOrder (InternalCarrier kappa) :=
    IsWellOrder.linearOrder baseRel
  letI : LinearOrder (InternalCarrier kappa) := baseOrder
  letI : LE (InternalCarrier kappa) := baseOrder.toLE
  letI : LT (InternalCarrier kappa) := baseOrder.toLT
  letI : Min (InternalCarrier kappa) := baseOrder.toMin
  letI : Max (InternalCarrier kappa) := baseOrder.toMax
  letI : Preorder (InternalCarrier kappa) := baseOrder.toPreorder
  letI : PartialOrder (InternalCarrier kappa) := baseOrder.toPartialOrder
  letI : WellFoundedLT (InternalCarrier kappa) :=
    ⟨by
      change WellFounded baseRel
      exact hbaseWell.wf⟩
  have lt_iff_mem (left right : InternalCarrier kappa) :
      left < right <-> LMem left.1 right.1 := by
    rfl
  let keyEmbedding :
      (InternalCarrier kappa × InternalCarrier kappa) ↪
        (InternalCarrier kappa ×ₗ
          (InternalCarrier kappa ×ₗ InternalCarrier kappa)) :=
    ⟨fun point => toLex (max point.1 point.2, toLex point),
      fun left right heq => congrArg Prod.snd heq⟩
  have keyEmbedding_lt_iff
      (left right : InternalCarrier kappa × InternalCarrier kappa) :
      keyEmbedding left < keyEmbedding right <->
        (max left.1 left.2 < max right.1 right.2 \/
          (max left.1 left.2 = max right.1 right.2 /\
            (left.1 < right.1 \/
              (left.1 = right.1 /\ left.2 < right.2)))) := by
    change
      toLex (max left.1 left.2, toLex left) <
          toLex (max right.1 right.2, toLex right) <-> _
    rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  let productEquiv := internalProductEquiv kappa
  let fullEmbedding :
      InternalCarrier (prodLCarrier kappa kappa) ↪
        (InternalCarrier kappa ×ₗ
          (InternalCarrier kappa ×ₗ InternalCarrier kappa)) :=
    ⟨fun point => keyEmbedding (productEquiv.symm point),
      fun left right heq => productEquiv.symm.injective
        (keyEmbedding.injective heq)⟩
  have hwell : IsWellOrder
      (InternalCarrier (prodLCarrier kappa kappa))
      (fullEmbedding ⁻¹'o (fun left right => left < right)) :=
    (RelEmbedding.preimage fullEmbedding
      (fun left right => left < right)).isWellOrder
  have maximum_eq : forall
      (left right : InternalCarrier kappa) (maximum : LCarrier.{u}),
      IsMaximumOf LMem left.1 right.1 maximum ->
        maximum = (max left right).1 := by
    intro left right maximum hmaximum
    rcases hmaximum with ⟨hleftRight, hmaximum⟩ |
      ⟨hrightLeft, hmaximum⟩
    · rcases hleftRight with hlt | heq
      · have hlt' : left < right := hlt
        have hmax : max left right = right :=
          max_eq_right (le_of_lt hlt')
        exact hmaximum.trans (congrArg Subtype.val hmax).symm
      · have heq' : left = right := Subtype.ext heq
        subst right
        simpa using hmaximum
    · have hlt' : right < left := hrightLeft
      have hmax : max left right = left :=
        max_eq_left (le_of_lt hlt')
      exact hmaximum.trans (congrArg Subtype.val hmax).symm
  have maximum_spec : forall
      (left right : InternalCarrier kappa),
      IsMaximumOf LMem left.1 right.1 (max left right).1 := by
    intro left right
    rcases lt_trichotomy left right with hlt | heq | hgt
    · apply Or.inl
      constructor
      · exact Or.inl hlt
      · exact congrArg Subtype.val (max_eq_right (le_of_lt hlt))
    · apply Or.inl
      constructor
      · exact Or.inr (congrArg Subtype.val heq)
      · exact congrArg Subtype.val (max_eq_right (le_of_eq heq))
    · apply Or.inr
      constructor
      · exact hgt
      · exact congrArg Subtype.val (max_eq_left (le_of_lt hgt))
  have hsemantic : forall
      (left right : InternalCarrier kappa × InternalCarrier kappa),
      OrdinalPairMaximumLexRel LMem
          (encodeInternalProduct kappa left).1
          (encodeInternalProduct kappa right).1 <->
        keyEmbedding left < keyEmbedding right := by
    intro left right
    constructor
    · rintro ⟨leftFirst, leftSecond, rightFirst, rightSecond,
        leftMaximum, rightMaximum, hleftPair, hrightPair,
        hleftMaximum, hrightMaximum, hcomparison⟩
      have hleftRaw := (isKuratowskiPairOf_lCarrier_iff
        (encodeInternalProduct kappa left).1 leftFirst leftSecond).mp
          hleftPair
      have hrightRaw := (isKuratowskiPairOf_lCarrier_iff
        (encodeInternalProduct kappa right).1 rightFirst rightSecond).mp
          hrightPair
      have hleftCoordinates := ZFSet.pair_inj.mp
        (show ZFSet.pair left.1.1.1 left.2.1.1 =
            ZFSet.pair leftFirst.1 leftSecond.1 by
          simpa only [encodeInternalProduct, orderedPairLCarrier_val]
            using hleftRaw)
      have hrightCoordinates := ZFSet.pair_inj.mp
        (show ZFSet.pair right.1.1.1 right.2.1.1 =
            ZFSet.pair rightFirst.1 rightSecond.1 by
          simpa only [encodeInternalProduct, orderedPairLCarrier_val]
            using hrightRaw)
      have hleftFirst : leftFirst = left.1.1 :=
        Subtype.ext hleftCoordinates.1.symm
      have hleftSecond : leftSecond = left.2.1 :=
        Subtype.ext hleftCoordinates.2.symm
      have hrightFirst : rightFirst = right.1.1 :=
        Subtype.ext hrightCoordinates.1.symm
      have hrightSecond : rightSecond = right.2.1 :=
        Subtype.ext hrightCoordinates.2.symm
      subst leftFirst
      subst leftSecond
      subst rightFirst
      subst rightSecond
      have hleftMaximumEq := maximum_eq
        left.1 left.2 leftMaximum hleftMaximum
      have hrightMaximumEq := maximum_eq
        right.1 right.2 rightMaximum hrightMaximum
      subst leftMaximum
      subst rightMaximum
      apply (keyEmbedding_lt_iff left right).mpr
      simpa only [lt_iff_mem, Subtype.coe_injective.eq_iff] using hcomparison
    · intro hcomparison
      refine ⟨left.1.1, left.2.1, right.1.1, right.2.1,
        (max left.1 left.2).1, (max right.1 right.2).1, ?_, ?_,
        maximum_spec left.1 left.2, maximum_spec right.1 right.2, ?_⟩
      · apply (isKuratowskiPairOf_lCarrier_iff
          (encodeInternalProduct kappa left).1 left.1.1 left.2.1).mpr
        rfl
      · apply (isKuratowskiPairOf_lCarrier_iff
          (encodeInternalProduct kappa right).1 right.1.1 right.2.1).mpr
        rfl
      · have hcomparison' := (keyEmbedding_lt_iff left right).mp hcomparison
        simpa only [lt_iff_mem, Subtype.coe_injective.eq_iff] using hcomparison'
  change IsWellOrder (InternalCarrier (prodLCarrier kappa kappa))
    (graphRelOn (ordinalPairMaximumLexGraph kappa)
      (prodLCarrier kappa kappa))
  convert hwell using 1
  funext left right
  apply propext
  change GraphRel (ordinalPairMaximumLexGraph kappa) left.1 right.1 <-> _
  rw [graphRel_ordinalPairMaximumLexGraph_iff]
  simp only [left.2, right.2, true_and]
  let leftCoordinates := productEquiv.symm left
  let rightCoordinates := productEquiv.symm right
  have hleft : encodeInternalProduct kappa leftCoordinates = left := by
    change productEquiv leftCoordinates = left
    exact productEquiv.apply_symm_apply left
  have hright : encodeInternalProduct kappa rightCoordinates = right := by
    change productEquiv rightCoordinates = right
    exact productEquiv.apply_symm_apply right
  have hresult := hsemantic leftCoordinates rightCoordinates
  rw [hleft, hright] at hresult
  change OrdinalPairMaximumLexRel LMem left.1 right.1 <->
    keyEmbedding (productEquiv.symm left) <
      keyEmbedding (productEquiv.symm right)
  simpa only [leftCoordinates, rightCoordinates] using hresult

/-! ## Bounds for strict initial segments -/

/-- In a successor-closed ordinal, every predecessor in the maximum-lex order
lies in the square of a strictly smaller ordinal.  The bound is the successor
of the maximum coordinate of `point`, exactly as in the standard cardinal
multiplication proof. -/
theorem OrdinalPairMaximumLexRel.exists_successor_product_bound
    {kappa predecessor point : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hsuccessor : forall bound : LCarrier.{u}, bound.1 ∈ kappa.1 ->
      (successorLCarrier bound).1 ∈ kappa.1)
    (hpredecessor : predecessor.1 ∈ (prodLCarrier kappa kappa).1)
    (hpoint : point.1 ∈ (prodLCarrier kappa kappa).1)
    (hrel : OrdinalPairMaximumLexRel LMem predecessor point) :
    exists bound : LCarrier.{u},
      bound.1 ∈ kappa.1 /\
        predecessor.1 ∈ (prodLCarrier bound bound).1 := by
  rcases hrel with
    ⟨leftFirst, leftSecond, rightFirst, rightSecond,
      leftMaximum, rightMaximum, hleftPair, hrightPair,
      hleftMaximum, hrightMaximum, hcomparison⟩
  have hleftPairEq := (isKuratowskiPairOf_lCarrier_iff
    predecessor leftFirst leftSecond).mp hleftPair
  have hrightPairEq := (isKuratowskiPairOf_lCarrier_iff
    point rightFirst rightSecond).mp hrightPair
  have hleftCoordinates :
      leftFirst.1 ∈ kappa.1 /\ leftSecond.1 ∈ kappa.1 := by
    change predecessor.1 ∈ ZFSet.prod kappa.1 kappa.1 at hpredecessor
    rw [hleftPairEq, ZFSet.pair_mem_prod] at hpredecessor
    exact hpredecessor
  have hrightCoordinates :
      rightFirst.1 ∈ kappa.1 /\ rightSecond.1 ∈ kappa.1 := by
    change point.1 ∈ ZFSet.prod kappa.1 kappa.1 at hpoint
    rw [hrightPairEq, ZFSet.pair_mem_prod] at hpoint
    exact hpoint
  have hrightMaximumMem : rightMaximum.1 ∈ kappa.1 := by
    rcases hrightMaximum with ⟨_rightLe, hmaximum⟩ |
      ⟨_leftLt, hmaximum⟩
    · rw [hmaximum]
      exact hrightCoordinates.2
    · rw [hmaximum]
      exact hrightCoordinates.1
  have hmaximumLe :
      leftMaximum.1 ∈ rightMaximum.1 \/ leftMaximum = rightMaximum := by
    rcases hcomparison with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr heq.1
  have hrightMaximumOrdinal : rightMaximum.1.IsOrdinal := by
    have hkappaRaw : kappa.1.IsOrdinal :=
      (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
    exact hkappaRaw.mem hrightMaximumMem
  have promote : forall coordinate : LCarrier.{u},
      coordinate.1 ∈ (successorLCarrier leftMaximum).1 ->
        coordinate.1 ∈ (successorLCarrier rightMaximum).1 := by
    intro coordinate hcoordinate
    rcases hmaximumLe with hlt | heq
    · rw [successorLCarrier_val, ZFSet.mem_insert_iff] at hcoordinate
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      rcases hcoordinate with hcoordinateEq | hcoordinateMem
      · apply Or.inr
        rw [hcoordinateEq]
        exact hlt
      · exact Or.inr
          (hrightMaximumOrdinal.mem_trans hcoordinateMem hlt)
    · rw [heq] at hcoordinate
      exact hcoordinate
  have hleftInSuccessor := hleftMaximum.mem_successor_lCarrier
  let bound := successorLCarrier rightMaximum
  refine ⟨bound, hsuccessor rightMaximum hrightMaximumMem, ?_⟩
  change predecessor.1 ∈ ZFSet.prod bound.1 bound.1
  rw [hleftPairEq, ZFSet.pair_mem_prod]
  exact ⟨promote leftFirst hleftInSuccessor.1,
    promote leftSecond hleftInSuccessor.2⟩

/-- Uniform version of the preceding bound: for a fixed point, one smaller
ordinal square contains its entire strict initial segment. -/
theorem exists_uniform_bound_for_ordinalPairMaximumLexGraph
    {kappa point : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hsuccessor : forall bound : LCarrier.{u}, bound.1 ∈ kappa.1 ->
      (successorLCarrier bound).1 ∈ kappa.1)
    (hpoint : point.1 ∈ (prodLCarrier kappa kappa).1) :
    exists bound : LCarrier.{u},
      bound.1 ∈ kappa.1 /\
        forall predecessor : LCarrier.{u},
          predecessor.1 ∈ (prodLCarrier kappa kappa).1 ->
            GraphRel (ordinalPairMaximumLexGraph kappa) predecessor point ->
              predecessor.1 ∈ (prodLCarrier bound bound).1 := by
  have hpointRaw := hpoint
  change point.1 ∈ ZFSet.prod kappa.1 kappa.1 at hpointRaw
  rcases ZFSet.mem_prod.mp hpointRaw with
    ⟨rightFirstRaw, hrightFirst, rightSecondRaw, hrightSecond,
      hpointPair⟩
  let rightFirst : LCarrier.{u} :=
    ⟨rightFirstRaw, Constructible.mem_L_of_mem hrightFirst kappa.2⟩
  let rightSecond : LCarrier.{u} :=
    ⟨rightSecondRaw, Constructible.mem_L_of_mem hrightSecond kappa.2⟩
  rcases exists_maximum_lCarrier_of_mem_ordinal hkappa
      (left := rightFirst) (right := rightSecond)
      hrightFirst hrightSecond with
    ⟨rightMaximum, hrightMaximum⟩
  have hrightMaximumMem : rightMaximum.1 ∈ kappa.1 := by
    rcases hrightMaximum with ⟨_rightLe, hmaximum⟩ |
      ⟨_leftLt, hmaximum⟩
    · rw [hmaximum]
      exact hrightSecond
    · rw [hmaximum]
      exact hrightFirst
  have hrightMaximumOrdinal : rightMaximum.1.IsOrdinal := by
    have hkappaRaw : kappa.1.IsOrdinal :=
      (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
    exact hkappaRaw.mem hrightMaximumMem
  let bound := successorLCarrier rightMaximum
  refine ⟨bound, hsuccessor rightMaximum hrightMaximumMem, ?_⟩
  intro predecessor hpredecessor hpredecessorPoint
  have hrel := (graphRel_ordinalPairMaximumLexGraph_iff
    kappa predecessor point).mp hpredecessorPoint |>.2.2
  rcases hrel with
    ⟨leftFirst, leftSecond, rightFirst', rightSecond',
      leftMaximum, rightMaximum', hleftPair, hrightPair,
      hleftMaximum, hrightMaximum', hcomparison⟩
  have hleftPairEq := (isKuratowskiPairOf_lCarrier_iff
    predecessor leftFirst leftSecond).mp hleftPair
  have hrightPairEq := (isKuratowskiPairOf_lCarrier_iff
    point rightFirst' rightSecond').mp hrightPair
  have hrightCoordinates := ZFSet.pair_inj.mp
    (show ZFSet.pair rightFirst.1 rightSecond.1 =
        ZFSet.pair rightFirst'.1 rightSecond'.1 by
      exact hpointPair.symm.trans hrightPairEq)
  have hrightFirstEq : rightFirst' = rightFirst :=
    Subtype.ext hrightCoordinates.1.symm
  have hrightSecondEq : rightSecond' = rightSecond :=
    Subtype.ext hrightCoordinates.2.symm
  subst rightFirst'
  subst rightSecond'
  have hrightMaximumEq : rightMaximum' = rightMaximum :=
    hrightMaximum'.unique_lCarrier hrightMaximum
  rw [hrightMaximumEq] at hcomparison
  have hmaximumLe :
      leftMaximum.1 ∈ rightMaximum.1 \/ leftMaximum = rightMaximum := by
    rcases hcomparison with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr heq.1
  have promote : forall coordinate : LCarrier.{u},
      coordinate.1 ∈ (successorLCarrier leftMaximum).1 ->
        coordinate.1 ∈ bound.1 := by
    intro coordinate hcoordinate
    rcases hmaximumLe with hlt | heq
    · rw [successorLCarrier_val, ZFSet.mem_insert_iff] at hcoordinate
      change coordinate.1 ∈ (successorLCarrier rightMaximum).1
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      rcases hcoordinate with hcoordinateEq | hcoordinateMem
      · apply Or.inr
        rw [hcoordinateEq]
        exact hlt
      · exact Or.inr
          (hrightMaximumOrdinal.mem_trans hcoordinateMem hlt)
    · rw [heq] at hcoordinate
      exact hcoordinate
  have hleftInSuccessor := hleftMaximum.mem_successor_lCarrier
  change predecessor.1 ∈ ZFSet.prod bound.1 bound.1
  rw [hleftPairEq, ZFSet.pair_mem_prod]
  exact ⟨promote leftFirst hleftInSuccessor.1,
    promote leftSecond hleftInSuccessor.2⟩

/-- The canonical order type of every strict initial segment internally
injects into a smaller ordinal square. -/
theorem canonicalMemberOrderType_injects_smaller_ordinalSquare
    {kappa point : LCarrier.{u}}
    (hkappa : IsVonNeumannOrdinal LMem kappa)
    (hsuccessor : forall bound : LCarrier.{u}, bound.1 ∈ kappa.1 ->
      (successorLCarrier bound).1 ∈ kappa.1)
    (hpoint : point.1 ∈ (prodLCarrier kappa kappa).1) :
    exists bound : LCarrier.{u},
      bound.1 ∈ kappa.1 /\
        Injects LMem
          (canonicalMemberOrderTypeLCarrier
            (ordinalPairMaximumLexGraph kappa)
            (prodLCarrier kappa kappa)
            (ordinalPairMaximumLexGraph_internallyWellOrders kappa hkappa)
            point hpoint)
          (prodLCarrier bound bound) := by
  let relation := ordinalPairMaximumLexGraph kappa
  let domain := prodLCarrier kappa kappa
  let hwell : InternallyWellOrders relation domain :=
    ordinalPairMaximumLexGraph_internallyWellOrders kappa hkappa
  rcases exists_uniform_bound_for_ordinalPairMaximumLexGraph
      hkappa hsuccessor hpoint with
    ⟨bound, hbound, hboundProperty⟩
  have hinitial := canonicalMemberOrderType_isInitial
    relation domain hwell point hpoint
  rcases hinitial with
    ⟨_hordinal, predecessors, hpredecessors, graph, horderIsomorphism⟩
  have hpredecessorsSubset : forall z : LCarrier.{u},
      z.1 ∈ predecessors.1 -> z.1 ∈ (prodLCarrier bound bound).1 := by
    intro z hz
    have hzSemantic := (hpredecessors z).mp hz
    exact hboundProperty z hzSemantic.1
      ((graphValue_lCarrier_iff_graphRel relation z point).mp
        hzSemantic.2)
  have hpredecessorsInject :
      Injects LMem predecessors (prodLCarrier bound bound) :=
    injects_of_subset_lCarrier hpredecessorsSubset
  have horderTypeEquinumerous :
      Equinumerous LMem predecessors
        (canonicalMemberOrderTypeLCarrier relation domain hwell point hpoint) :=
    ⟨graph, horderIsomorphism.1⟩
  refine ⟨bound, hbound, ?_⟩
  change Injects LMem
    (canonicalMemberOrderTypeLCarrier relation domain hwell point hpoint)
    (prodLCarrier bound bound)
  exact horderTypeEquinumerous.symm_lCarrier.injects.trans_lCarrier
    hpredecessorsInject

end

end Constructible.ContinuumFormula
