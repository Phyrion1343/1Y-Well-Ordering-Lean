/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistory
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# The canonical relation-free constructible-stage history

This file fixes the actual set which later local-absoluteness arguments must
put inside a prescribed constructible level.  For an ordinal `alpha`,
`canonicalBareHistory alpha` is exactly

`{ <beta, L_beta> | beta <= alpha }`.

The definition uses ambient ZF Replacement only to obtain a genuine `ZFSet`.
No constructibility bound is claimed here.  In particular, membership in the
proper class `L` would not by itself imply the local bound required by
Condensation; that bound is a separate theorem.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The canonical Kuratowski pair at one constructible stage. -/
def canonicalBareHistoryPair (ordinal : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.pair ordinal.toZFSet (LStageZF ordinal)

/-- The graph of all canonical stage pairs at indices strictly below
`bound`. -/
def canonicalBareHistoryBelow (bound : Ordinal.{u}) : ZFSet.{u} :=
  replacementRangeZF bound fun ordinal _hordinal =>
    canonicalBareHistoryPair ordinal

/-- The graph of all canonical stage pairs through `bound`, including its
top pair. -/
def canonicalBareHistory (bound : Ordinal.{u}) : ZFSet.{u} :=
  canonicalBareHistoryBelow (Order.succ bound)

@[simp]
theorem mem_canonicalBareHistoryBelow_iff
    {bound : Ordinal.{u}} {entry : ZFSet.{u}} :
    entry ∈ canonicalBareHistoryBelow bound ↔
      ∃ ordinal < bound, canonicalBareHistoryPair ordinal = entry := by
  rw [canonicalBareHistoryBelow, mem_replacementRangeZF_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hentry⟩
    exact ⟨ordinal, hordinal, hentry⟩
  · rintro ⟨ordinal, hordinal, hentry⟩
    exact ⟨ordinal, hordinal, hentry⟩

@[simp]
theorem mem_canonicalBareHistory_iff
    {bound : Ordinal.{u}} {entry : ZFSet.{u}} :
    entry ∈ canonicalBareHistory bound ↔
      ∃ ordinal ≤ bound, canonicalBareHistoryPair ordinal = entry := by
  rw [canonicalBareHistory, mem_canonicalBareHistoryBelow_iff]
  apply exists_congr
  intro ordinal
  rw [Order.lt_succ_iff]

/-- The through-`bound` history is the below-`bound` graph with precisely the
top pair adjoined. -/
theorem canonicalBareHistory_eq_insert_top (bound : Ordinal.{u}) :
    canonicalBareHistory bound =
      insert (canonicalBareHistoryPair bound)
        (canonicalBareHistoryBelow bound) := by
  apply ZFSet.ext
  intro entry
  rw [mem_canonicalBareHistory_iff, ZFSet.mem_insert_iff,
    mem_canonicalBareHistoryBelow_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hentry⟩
    rcases hordinal.eq_or_lt with rfl | hordinal
    · exact Or.inl hentry.symm
    · exact Or.inr ⟨ordinal, hordinal, hentry⟩
  · rintro (hentry | ⟨ordinal, hordinal, hentry⟩)
    · exact ⟨bound, le_refl bound, hentry.symm⟩
    · exact ⟨ordinal, hordinal.le, hentry⟩

/-- Passing to a successor only adjoins its new top pair. -/
theorem canonicalBareHistory_succ (ordinal : Ordinal.{u}) :
    canonicalBareHistory (Order.succ ordinal) =
      insert (canonicalBareHistoryPair (Order.succ ordinal))
        (canonicalBareHistory ordinal) := by
  rw [canonicalBareHistory_eq_insert_top]
  rfl

/-- Exact coordinate form of lookup in the canonical history. -/
theorem pair_mem_canonicalBareHistory_iff
    {bound : Ordinal.{u}} {index stage : ZFSet.{u}} :
    ZFSet.pair index stage ∈ canonicalBareHistory bound ↔
      ∃ ordinal ≤ bound,
        index = ordinal.toZFSet ∧ stage = LStageZF ordinal := by
  rw [mem_canonicalBareHistory_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hpairs⟩
    have hcoordinates := ZFSet.pair_inj.mp hpairs
    exact ⟨ordinal, hordinal, hcoordinates.1.symm,
      hcoordinates.2.symm⟩
  · rintro ⟨ordinal, hordinal, rfl, rfl⟩
    exact ⟨ordinal, hordinal, rfl⟩

/-- At a fixed index the canonical history has a unique stage coordinate. -/
theorem canonicalBareHistory_functional
    {bound : Ordinal.{u}} {index stage otherStage : ZFSet.{u}}
    (hstage : ZFSet.pair index stage ∈ canonicalBareHistory bound)
    (hother : ZFSet.pair index otherStage ∈ canonicalBareHistory bound) :
    otherStage = stage := by
  rcases pair_mem_canonicalBareHistory_iff.mp hstage with
    ⟨ordinal, _hordinal, hindex, hstageEq⟩
  rcases pair_mem_canonicalBareHistory_iff.mp hother with
    ⟨otherOrdinal, _hotherOrdinal, hotherIndex, hotherStageEq⟩
  have hordinals : ordinal = otherOrdinal := by
    apply Ordinal.toZFSet_injective
    exact hindex.symm.trans hotherIndex
  subst otherOrdinal
  exact hotherStageEq.trans hstageEq.symm

/-- The canonical top entry is present. -/
theorem canonicalBareHistory_top_mem (bound : Ordinal.{u}) :
    canonicalBareHistoryPair bound ∈ canonicalBareHistory bound := by
  exact mem_canonicalBareHistory_iff.mpr ⟨bound, le_refl bound, rfl⟩

/-! ## Proper-class constructibility (not a local bound) -/

/-- The canonical graph agrees extensionally with the Replacement graph
already constructed in the full class `L`, hence is itself constructible.
This theorem deliberately gives only membership in `L`. -/
theorem canonicalBareHistory_mem_L (bound : Ordinal.{u}) :
    canonicalBareHistory bound ∈ L := by
  rcases exists_bareStagePairFamily bound with ⟨history, hhistory⟩
  have heq : history.1 = canonicalBareHistory bound := by
    apply ZFSet.ext
    intro entry
    constructor
    · intro hentry
      have hentryL : entry ∈ L := mem_L_of_mem hentry history.2
      let entryL : LCarrier.{u} := ⟨entry, hentryL⟩
      rcases (hhistory entryL).mp hentry with
        ⟨index, hindex, stage, relation, hstate, hcode⟩
      rcases exists_eq_ordinalLCarrier_of_mem hindex with
        ⟨ordinal, hordinal, hindexEq⟩
      subst index
      rcases exists_stageStateAt_ordinal ordinal with
        ⟨canonicalRelation, hcanonical⟩
      have houtputs := stageStateAt_ordinal_outputs_unique ordinal
        hstate hcanonical
      apply mem_canonicalBareHistory_iff.mpr
      refine ⟨ordinal, Order.lt_succ_iff.mp hordinal, ?_⟩
      apply Eq.symm
      calc
        entry = ZFSet.pair (ordinalLCarrier ordinal).1 stage.1 := hcode
        _ = canonicalBareHistoryPair ordinal := by
          rw [houtputs.1]
          rfl
    · intro hentry
      rcases mem_canonicalBareHistory_iff.mp hentry with
        ⟨ordinal, hordinal, hcode⟩
      have hpairL : canonicalBareHistoryPair ordinal ∈ L := by
        exact orderedPair_mem_L
          (ordinal_toZFSet_mem_L ordinal)
          (LStageZF_mem_L ordinal)
      let entryL : LCarrier.{u} :=
        ⟨canonicalBareHistoryPair ordinal, hpairL⟩
      have hentryFamily : entryL.1 ∈ history.1 :=
        (hhistory entryL).mpr (by
          refine ⟨ordinalLCarrier ordinal, ?_, ?_⟩
          · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
              (Order.succ bound) ordinal).mpr
              (Order.lt_succ_iff.mpr hordinal)
          · rcases exists_stageStateAt_ordinal ordinal with
              ⟨relation, hstate⟩
            exact ⟨stageLCarrier ordinal, relation, hstate, rfl⟩)
      change canonicalBareHistoryPair ordinal ∈ history.1 at hentryFamily
      rw [hcode] at hentryFamily
      exact hentryFamily
  rw [← heq]
  exact history.2

/-- The canonical history packaged as an element of the full constructible
universe.  Its subtype proof must not be used as a substitute for a local
`LStageZF` membership proof. -/
def canonicalBareHistoryLCarrier (bound : Ordinal.{u}) : LCarrier.{u} :=
  ⟨canonicalBareHistory bound, canonicalBareHistory_mem_L bound⟩

@[simp]
theorem canonicalBareHistoryLCarrier_val (bound : Ordinal.{u}) :
    (canonicalBareHistoryLCarrier bound).1 = canonicalBareHistory bound :=
  rfl

/-! ## A formula for one canonical bare pair -/

/-- After binding an index and a stage to the free layout `(fixed13,pair)`,
select the existing `(fixed13,index,stage)` bare-stage layout. -/
def canonicalBarePairStageRename : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15]

/-- Free layout `(fixed13,pair)`.  The formula says that `pair` is the
Kuratowski pair of an ordinal index and a stage recognized by the existing
relation-free stage predicate. -/
def canonicalBarePairFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename canonicalBarePairStageRename bareStageAtFormula)
        (Delta0Formula.kuratowskiPairEqAt
          (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)).toFO)))

/-- Raw free assignment `(fixed13,pair)`. -/
def canonicalBarePairRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u}) :
    Tuple ZFSet.{u} 14 :=
  snoc fixed pair

/-- Raw assignment after adjoining the hidden index and stage. -/
def canonicalBarePairWitnessRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (canonicalBarePairRawAssignment fixed pair) index) stage

private theorem comp_canonicalBarePairStageRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) :
    (fun i => canonicalBarePairWitnessRawAssignment fixed pair index stage
      (canonicalBarePairStageRename i)) =
      bareStageAtRawAssignment fixed index stage := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalBarePairWitnessRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i, canonicalBarePairWitnessRawAssignment fixed pair index stage i ∈ U := by
  intro i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · simpa only [canonicalBarePairWitnessRawAssignment,
      snoc_last] using hstage
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · simpa only [canonicalBarePairWitnessRawAssignment,
        snoc_castSucc, snoc_last] using hindex
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc,
          snoc_last] using hpair
      · simpa only [canonicalBarePairWitnessRawAssignment,
          canonicalBarePairRawAssignment, snoc_castSucc] using hfixed i12

private theorem satisfiesIn_isOrdinal_iff_canonicalBare
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFSet.{u}) (hx : x ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![x] ↔
      x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hx⟩
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU xU
  have hraw : (fun i => (![xU] i).1) = ![x] := by
    funext i
    fin_cases i
    rfl
  rw [hraw] at hbridge
  exact hbridge.symm.trans hsemantic

private theorem satisfiesIn_ordinalAt_iff_canonicalBare
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (ordinalAt i) s ↔
      (s i).IsOrdinal := by
  rw [ordinalAt, satisfiesIn_rename]
  have hone : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    fin_cases j
    rfl
  rw [hone, satisfiesIn_isOrdinal_iff_canonicalBare hU (s i) (hs i)]

/-- Exact raw semantics of `canonicalBarePairFormula`.  The stage conjunct
is intentionally left as `BareStageAtIn`; identifying it with `LStageZF`
requires a separate correctness hypothesis. -/
theorem satisfiesIn_canonicalBarePairFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) canonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) ↔
      ∃ index : ZFSet.{u}, index ∈ U ∧ index.IsOrdinal ∧
        ∃ stage : ZFSet.{u}, stage ∈ U ∧
          BareStageAtIn (U : Set ZFSet.{u}) fixed index stage ∧
          pair = ZFSet.pair index stage := by
  simp only [canonicalBarePairFormula, SatisfiesIn]
  apply exists_congr
  intro index
  apply and_congr_right
  intro hindex
  change index ∈ U at hindex
  constructor
  · rintro ⟨stage, hstage, hordinal, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : ∀ i, witness i ∈ U :=
      canonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    have hordinal' : index.IsOrdinal :=
      (satisfiesIn_ordinalAt_iff_canonicalBare hU
        (14 : Fin 16) witness hwitness).mp hordinal
    have hstageAt' : BareStageAtIn (U : Set ZFSet.{u})
        fixed index stage := by
      have hrenamed :
          SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
            (bareStageAtRawAssignment fixed index stage) := by
        rw [satisfiesIn_rename] at hstageAt
        change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
          (fun i => witness (canonicalBarePairStageRename i)) at hstageAt
        rw [comp_canonicalBarePairStageRename_raw] at hstageAt
        exact hstageAt
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mp hrenamed
    have hpairEq' := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
      witness hwitness).mp hpairEq
    refine ⟨hordinal', stage, hstage, hstageAt', ?_⟩
    have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
    have hindexCoordinate : witness (14 : Fin 16) = index := rfl
    have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
    simpa only [hpairCoordinate, hindexCoordinate,
      hstageCoordinate] using hpairEq'
  · rintro ⟨hordinal, stage, hstage, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : ∀ i, witness i ∈ U :=
      canonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    refine ⟨stage, hstage, ?_, ?_, ?_⟩
    · exact (satisfiesIn_ordinalAt_iff_canonicalBare hU
        (14 : Fin 16) witness hwitness).mpr hordinal
    · rw [satisfiesIn_rename]
      change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (fun i => witness (canonicalBarePairStageRename i))
      rw [comp_canonicalBarePairStageRename_raw]
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mpr hstageAt
    · apply (satisfiesIn_kuratowskiPairEqAt_iff hU
        (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
        witness hwitness).mpr
      have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
      have hindexCoordinate : witness (14 : Fin 16) = index := rfl
      have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
      simpa only [hpairCoordinate, hindexCoordinate,
        hstageCoordinate] using hpairEq

/-- Raw values of the thirteen canonical evaluator parameters. -/
def canonicalBareFixedParameters : Tuple ZFSet.{u} 13 :=
  fun i => (stageHistoryFixedParameters.{u} i).1

/-- The exact, assumption-transparent correctness contract used below.  It
speaks about `BareStageAtIn`, not syntactic satisfaction; the preceding raw
semantic theorem is the bridge between the two. -/
def CanonicalBareStagesCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  ∀ ordinal : Ordinal.{u}, ∀ stage : ZFSet.{u},
    ordinal.toZFSet ∈ U → stage ∈ U →
      (BareStageAtIn (U : Set ZFSet.{u}) fixed
          ordinal.toZFSet stage ↔
        stage = LStageZF ordinal)

/-- Coordinates of a Kuratowski pair belong to every transitive set which
contains the pair itself. -/
theorem orderedPair_components_mem_of_transitive
    {U x y : ZFSet.{u}} (hU : U.IsTransitive)
    (hpair : ZFSet.pair x y ∈ U) : x ∈ U ∧ y ∈ U := by
  have hxSingleton : ({x} : ZFSet.{u}) ∈ U :=
    hU.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ U :=
    hU.mem_trans (by simp [ZFSet.pair]) hpair
  exact ⟨hU.mem_trans (by simp) hxSingleton,
    hU.mem_trans (by simp) hxyPair⟩

/-- Under the displayed correctness contract, the canonical-pair formula
has exactly the expected external outputs whose ordinal codes lie in `U`. -/
theorem satisfiesIn_canonicalBarePairFormula_iff_of_correct
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U) (hpair : pair ∈ U)
    (hcorrect : CanonicalBareStagesCorrectIn U fixed) :
    SatisfiesIn (U : Set ZFSet.{u}) canonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) ↔
      ∃ ordinal : Ordinal.{u}, ordinal.toZFSet ∈ U ∧
        pair = canonicalBareHistoryPair ordinal := by
  rw [satisfiesIn_canonicalBarePairFormula_iff hU fixed pair
    hfixed hpair]
  constructor
  · rintro ⟨index, hindex, hordinal, stage, hstage,
      hstageAt, hpairEq⟩
    let ordinal : Ordinal.{u} := index.rank
    have hindexEq : index = ordinal.toZFSet :=
      hordinal.toZFSet_rank_eq.symm
    rw [hindexEq] at hindex hstageAt hpairEq
    have hstageEq : stage = LStageZF ordinal :=
      (hcorrect ordinal stage hindex hstage).mp hstageAt
    subst stage
    exact ⟨ordinal, hindex, by
      simpa only [canonicalBareHistoryPair] using hpairEq⟩
  · rintro ⟨ordinal, hindex, hpairEq⟩
    have hcanonicalPair : canonicalBareHistoryPair ordinal ∈ U := by
      simpa only [hpairEq] using hpair
    have hcomponents := orderedPair_components_mem_of_transitive hU
      (by simpa only [canonicalBareHistoryPair] using hcanonicalPair)
    refine ⟨ordinal.toZFSet, hindex, ZFSet.isOrdinal_toZFSet ordinal,
      LStageZF ordinal, hcomponents.2, ?_, ?_⟩
    · exact (hcorrect ordinal (LStageZF ordinal)
        hindex hcomponents.2).mpr rfl
    · simpa only [canonicalBareHistoryPair] using hpairEq

/-! ## Pointwise stage bounds -/

/-- A single canonical graph entry belongs to every nonzero limit level
strictly above its index. -/
theorem canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
    {ordinal theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hordinal : ordinal < theta) :
    canonicalBareHistoryPair ordinal ∈ LStageZF theta := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
    (ordinal_toZFSet_mem_LStageZF_of_lt hordinal)
    (LStageZF_mem_LStageZF_of_lt_isSuccLimit htheta hordinal)

/-- Every entry of a bounded canonical history lies in a containing limit
level.  This is deliberately a subset statement; it does not claim that the
whole graph is itself an element of that level. -/
theorem canonicalBareHistoryBelow_subset_LStageZF
    {bound theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hbound : bound ≤ theta) :
    canonicalBareHistoryBelow bound ⊆ LStageZF theta := by
  intro entry hentry
  rcases mem_canonicalBareHistoryBelow_iff.mp hentry with
    ⟨ordinal, hordinal, rfl⟩
  exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
    htheta (hordinal.trans_le hbound)

/-- In particular, the history through `bound` is pointwise contained in
every limit level strictly above `bound`. -/
theorem canonicalBareHistory_subset_LStageZF
    {bound theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (hbound : bound < theta) :
    canonicalBareHistory bound ⊆ LStageZF theta := by
  intro entry hentry
  rcases mem_canonicalBareHistory_iff.mp hentry with
    ⟨ordinal, hordinal, rfl⟩
  exact canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
    htheta (hordinal.trans_lt hbound)

/-! ## Ordinal bookkeeping for the intended local bound -/

/-- Below a limit, adjoining the finite-code headroom `omega` still stays
below (or reaches) that limit. -/
theorem add_omega_le_of_lt_isSuccLimit
    {ordinal limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (hordinal : ordinal < limit) :
    ordinal + Ordinal.omega0 ≤ limit := by
  apply (Ordinal.add_le_iff_of_isSuccLimit
    Ordinal.isSuccLimit_omega0).mpr
  intro finite hfinite
  rcases Ordinal.lt_omega0.mp hfinite with ⟨n, rfl⟩
  exact (hlimit.add_natCast_lt hordinal n).le

/-- A successor does not change the `alpha + omega` bookkeeping level. -/
theorem succ_add_omega (ordinal : Ordinal.{u}) :
    Order.succ ordinal + Ordinal.omega0 =
      ordinal + Ordinal.omega0 := by
  rw [Order.succ_eq_add_one, add_assoc, Ordinal.one_add_omega0]

/-- The intended history-bound level is itself a nonzero limit. -/
theorem isSuccLimit_add_omega (ordinal : Ordinal.{u}) :
    Order.IsSuccLimit (ordinal + Ordinal.omega0) :=
  Ordinal.isSuccLimit_add ordinal Ordinal.isSuccLimit_omega0

/-! ## Conditional local Separation at a limit -/

private theorem ordinal_lt_of_toZFSet_mem_stage
    {ordinal limit : Ordinal.{u}}
    (hordinal : ordinal.toZFSet ∈ LStageZF limit) : ordinal < limit := by
  have hrank := (ordinal_stage_invariants limit).1
    (ZFSet.isOrdinal_toZFSet ordinal) hordinal
  have heq : (ordinal.toZFSet : ZFSet.{u}).rank = ordinal := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet ordinal).toZFSet_rank_eq
  simpa only [heq] using hrank

/-- At a limit level, the conditional canonical-pair semantics is exactly
membership in the graph of all strictly earlier stage pairs. -/
theorem satisfiesIn_canonicalBarePairFormula_stage_iff_of_correct
    {limit : Ordinal.{u}} (_hlimit : Order.IsSuccLimit limit)
    (hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters)
    (pair : ZFSet.{u}) (hpair : pair ∈ LStageZF limit) :
    SatisfiesIn (LStageZF limit : Set ZFSet.{u})
        canonicalBarePairFormula
        (canonicalBarePairRawAssignment
          canonicalBareFixedParameters pair) ↔
      pair ∈ canonicalBareHistoryBelow limit := by
  rw [satisfiesIn_canonicalBarePairFormula_iff_of_correct
    (LStageZF_isTransitive limit) canonicalBareFixedParameters pair
    hfixed hpair hcorrect,
    mem_canonicalBareHistoryBelow_iff]
  constructor
  · rintro ⟨ordinal, hordinal, hpairEq⟩
    exact ⟨ordinal, ordinal_lt_of_toZFSet_mem_stage hordinal,
      hpairEq.symm⟩
  · rintro ⟨ordinal, hordinal, hpairEq⟩
    exact ⟨ordinal,
      ordinal_toZFSet_mem_LStageZF_of_lt hordinal, hpairEq.symm⟩

/-- Conditional Separation theorem for the earlier-pair graph.  Every
assumption is visible: the carrier is a genuine limit level, the fixed
parameters lie in it, and its raw bare-stage predicate is correct. -/
theorem canonicalBareHistoryBelow_mem_DefZF_of_correct
    {limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters) :
    canonicalBareHistoryBelow limit ∈ DefZF (LStageZF limit) := by
  rw [mem_DefZF_iff_exists_satisfies]
  let params : Tuple (ZFCarrier (LStageZF limit)) 13 :=
    fun i => ⟨canonicalBareFixedParameters i, hfixed i⟩
  refine ⟨canonicalBareHistoryBelow_subset_LStageZF hlimit
      (le_refl limit), 13, params, canonicalBarePairFormula, ?_⟩
  intro pair
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (LStageZF limit : Set ZFSet.{u}) canonicalBarePairFormula
    (snoc params pair)
  have hraw :
      (fun i => (snoc params pair i).1) =
        canonicalBarePairRawAssignment
          canonicalBareFixedParameters pair.1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp only [snoc_castSucc, canonicalBarePairRawAssignment,
        params]
  have hsemantic :=
    satisfiesIn_canonicalBarePairFormula_stage_iff_of_correct
      hlimit hfixed hcorrect pair.1 pair.2
  calc
    pair.1 ∈ canonicalBareHistoryBelow limit ↔
        SatisfiesIn (LStageZF limit : Set ZFSet.{u})
          canonicalBarePairFormula
          (canonicalBarePairRawAssignment
            canonicalBareFixedParameters pair.1) := hsemantic.symm
    _ ↔ FOFormula.Satisfies (zfCarrierMem (LStageZF limit))
          canonicalBarePairFormula (snoc params pair) := by
      rw [← hraw]
      exact hbridge.symm

/-- Insertion preserves every nonzero limit level. -/
theorem insert_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {element old : ZFSet.{u}}
    (helement : element ∈ LStageZF theta)
    (hold : old ∈ LStageZF theta) :
    insert element old ∈ LStageZF theta := by
  rw [ZFSet.insert_eq]
  exact union_mem_LStageZF_of_isSuccLimit htheta
    (singleton_mem_LStageZF_of_isSuccLimit htheta helement) hold

/-- The honest successor step for the intended invariant
`H_alpha ∈ L_(alpha + omega)`. -/
theorem canonicalBareHistory_succ_mem_LStageZF_add_omega
    (ordinal : Ordinal.{u})
    (hhistory : canonicalBareHistory ordinal ∈
      LStageZF (ordinal + Ordinal.omega0)) :
    canonicalBareHistory (Order.succ ordinal) ∈
      LStageZF (Order.succ ordinal + Ordinal.omega0) := by
  rw [succ_add_omega ordinal, canonicalBareHistory_succ]
  have hlimit := isSuccLimit_add_omega ordinal
  have hordinal : ordinal < ordinal + Ordinal.omega0 :=
    lt_add_of_pos_right ordinal Ordinal.omega0_pos
  have hsuccessor : Order.succ ordinal <
      ordinal + Ordinal.omega0 := hlimit.succ_lt hordinal
  exact insert_mem_LStageZF_of_isSuccLimit hlimit
    (canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      hlimit hsuccessor)
    hhistory

/-- The honest limit step above `omega`: conditional local correctness gives
the earlier graph by Separation, and finite closure then adds the top pair.
The conclusion is the exact invariant, not merely pointwise containment. -/
theorem canonicalBareHistory_mem_LStageZF_add_omega_of_limit_of_correct
    {limit : Ordinal.{u}} (hlimit : Order.IsSuccLimit limit)
    (homega : Ordinal.omega0 < limit)
    (hcorrect : CanonicalBareStagesCorrectIn
      (LStageZF limit) canonicalBareFixedParameters) :
    canonicalBareHistory limit ∈
      LStageZF (limit + Ordinal.omega0) := by
  have hfixed : ∀ i : Fin 13,
      canonicalBareFixedParameters.{u} i ∈ LStageZF limit := by
    intro i
    exact stageHistoryFixedParameters_mem_LStageZF_of_omega_lt homega i
  have hbelowSucc : canonicalBareHistoryBelow limit ∈
      LStageZF (Order.succ limit) := by
    rw [LStageZF_succ]
    exact canonicalBareHistoryBelow_mem_DefZF_of_correct
      hlimit hfixed hcorrect
  have htargetLimit := isSuccLimit_add_omega limit
  have hlimitTarget : limit < limit + Ordinal.omega0 :=
    lt_add_of_pos_right limit Ordinal.omega0_pos
  have hsuccTarget : Order.succ limit < limit + Ordinal.omega0 :=
    htargetLimit.succ_lt hlimitTarget
  have hbelow : canonicalBareHistoryBelow limit ∈
      LStageZF (limit + Ordinal.omega0) :=
    LStageZF_mono hsuccTarget.le hbelowSucc
  have htop : canonicalBareHistoryPair limit ∈
      LStageZF (limit + Ordinal.omega0) :=
    canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      htargetLimit hlimitTarget
  rw [canonicalBareHistory_eq_insert_top]
  exact insert_mem_LStageZF_of_isSuccLimit htargetLimit htop hbelow

end

end Constructible.Model
