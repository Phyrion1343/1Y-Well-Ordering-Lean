/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryOmegaBounds
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistorySemantics

/-!
# The canonical history at the first infinite limit

The full evaluator prefix contains the set `omega`, so it cannot be used as
a parameter over `L_omega`.  We instead work over `L_(omega + 1)` and
restrict the displayed stage index to an element of `omega`.

Crucially, this file does not assert full evaluator correctness in that
successor level.  It isolates the exact weaker fact required here: evaluator
correctness when the predecessor is one of the finite stages `L_n`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-! ## The exact finite-input evaluator contract -/

/-- Correctness of the internal Goedel evaluator only on actual finite
constructible stages.  No assertion is made about arbitrary inputs in `U`. -/
def FiniteBareGodelDefOutputCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  forall n : Nat, forall stage : ZFSet.{u},
    LStageZF (n : Ordinal.{u}) ∈ U -> stage ∈ U ->
      (BareGodelDefOutputIn (U : Set ZFSet.{u}) fixed
          (LStageZF (n : Ordinal.{u})) stage <->
        stage = Godel.godelDef (LStageZF (n : Ordinal.{u})))

private theorem empty_ne_insert_self_finite (predecessor : ZFSet.{u}) :
    (∅ : ZFSet.{u}) ≠ insert predecessor predecessor := by
  intro h
  have hmem : predecessor ∈ (∅ : ZFSet.{u}) := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact ZFSet.notMem_empty predecessor hmem

/-! ## Soundness and completeness at finite indices -/

/-- Soundness of an internally recognized finite stage only needs the
finite-input evaluator contract. -/
theorem bareStageAtIn_natCast_sound_of_transitive
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat) :
    forall {stage : ZFSet.{u}},
      (n : Ordinal.{u}).toZFSet ∈ U -> stage ∈ U ->
      BareStageAtIn (U : Set ZFSet.{u}) fixed
          (n : Ordinal.{u}).toZFSet stage ->
        stage = LStageZF (n : Ordinal.{u}) := by
  induction n with
  | zero =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, _hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      rcases hlocal with hbase | hsuccessor | hlimit
      · calc
          stage = fixed (2 : Fin 13) := hbase.2
          _ = (∅ : ZFSet.{u}) := hempty
          _ = LStageZF (0 : Ordinal.{u}) := LStageZF_zero.symm
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _houtput⟩
        have himpossible :
            (∅ : ZFSet.{u}) =
              insert predecessorIndex predecessorIndex := by
          simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using
            hpredecessor
        exact (empty_ne_insert_self_finite predecessorIndex
          himpossible).elim
      · have hzero :
            ((0 : Nat) : Ordinal.{u}).toZFSet =
              fixed (2 : Fin 13) := by
          rw [Nat.cast_zero, Ordinal.toZFSet_zero, hempty]
        exact (hlimit.1.1 hzero).elim
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one]
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      rcases hlocal with hbase | hsuccessor | hlimit
      · have hcodes :
            (Order.succ (n : Ordinal.{u})).toZFSet =
              (0 : Ordinal.{u}).toZFSet := by
          calc
            (Order.succ (n : Ordinal.{u})).toZFSet =
                fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : Order.succ (n : Ordinal.{u}) = 0 :=
          Ordinal.toZFSet_injective hcodes
        exact (Order.succ_ne_bot (n : Ordinal.{u}) hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, hpredecessorIndexU,
            predecessorStage, hpredecessorStageU,
            hpredecessor, hpredecessorEntry, houtput⟩
        change predecessorIndex ∈ U at hpredecessorIndexU
        change predecessorStage ∈ U at hpredecessorStageU
        have hpredecessorIndex :
            predecessorIndex = (n : Ordinal.{u}).toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            (n : Ordinal.{u}) predecessorIndex).mp hpredecessor
        subst predecessorIndex
        have hpredecessorAt :
            BareStageAtIn (U : Set ZFSet.{u}) fixed
              (n : Ordinal.{u}).toZFSet predecessorStage :=
          bareStageAtIn_of_validHistory hhistoryU rfl
            (Order.le_succ (n : Ordinal.{u})) hvalid hpredecessorEntry
        have hpredecessorStageEq :
            predecessorStage = LStageZF (n : Ordinal.{u}) :=
          ih hpredecessorIndexU hpredecessorStageU hpredecessorAt
        subst predecessorStage
        have hstageEq :
            stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) :=
          (hcorrect n stage hpredecessorStageU hstageU).mp houtput
        calc
          stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) := hstageEq
          _ = DefZF (LStageZF (n : Ordinal.{u})) :=
            (Godel.DefZF_eq_godelDef
              (LStageZF_isTransitive (n : Ordinal.{u}))).symm
          _ = LStageZF (Order.succ (n : Ordinal.{u})) :=
            (LStageZF_succ (n : Ordinal.{u})).symm
      · have hpredecessorMem :
            (n : Ordinal.{u}).toZFSet ∈
              (Order.succ (n : Ordinal.{u})).toZFSet :=
          Ordinal.toZFSet_mem_toZFSet_iff.mpr
            (Order.lt_succ (n : Ordinal.{u}))
        have hpredecessorU : (n : Ordinal.{u}).toZFSet ∈ U :=
          hU.mem_trans hpredecessorMem hindexU
        have hpredecessor :
            (Order.succ (n : Ordinal.{u})).toZFSet =
              insert (n : Ordinal.{u}).toZFSet
                (n : Ordinal.{u}).toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            (n : Ordinal.{u}) (n : Ordinal.{u}).toZFSet).mpr rfl
        exact (hlimit.1.2
          ⟨(n : Ordinal.{u}).toZFSet, hpredecessorU,
            hpredecessor⟩).elim

/-- The canonical local rule at a finite index needs evaluator correctness
only for the immediately preceding finite stage. -/
theorem canonicalBareHistory_localStateIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    {bound : Ordinal.{u}} (n : Nat)
    (hindex : (n : Ordinal.{u}) ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) (n : Ordinal.{u}).toZFSet
      (LStageZF (n : Ordinal.{u})) := by
  cases n with
  | zero =>
      exact Or.inl ⟨by rw [Nat.cast_zero, Ordinal.toZFSet_zero, hempty],
        by rw [Nat.cast_zero, LStageZF_zero, hempty]⟩
  | succ n =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one] at hindex ⊢
      have hpredecessorLe : (n : Ordinal.{u}) ≤ bound :=
        (Order.le_succ (n : Ordinal.{u})).trans hindex
      have hpredecessorComponents :=
        canonicalBareHistory_components_mem hU hpredecessorLe hhistory
      have hstageComponents :=
        canonicalBareHistory_components_mem hU hindex hhistory
      refine Or.inr (Or.inl
        ⟨(n : Ordinal.{u}).toZFSet, hpredecessorComponents.1,
          LStageZF (n : Ordinal.{u}), hpredecessorComponents.2,
          ?_, ?_, ?_⟩)
      · exact (ordinalToZFSet_successor_predecessor_iff
          (n : Ordinal.{u}) (n : Ordinal.{u}).toZFSet).mpr rfl
      · exact canonicalBareHistory_entry hpredecessorLe
      · apply (hcorrect n (LStageZF (Order.succ (n : Ordinal.{u})))
          hpredecessorComponents.2 hstageComponents.2).mpr
        rw [LStageZF_succ,
          Godel.DefZF_eq_godelDef
            (LStageZF_isTransitive (n : Ordinal.{u}))]

private theorem exists_ordinal_code_le_natCast_of_code_le
    {bound : Nat} {index : ZFSet.{u}}
    (hindex : index ∈ (bound : Ordinal.{u}).toZFSet ∨
      index = (bound : Ordinal.{u}).toZFSet) :
    exists n : Nat, n ≤ bound ∧ index = (n : Ordinal.{u}).toZFSet := by
  have hexists : exists ordinal : Ordinal.{u},
      ordinal ≤ (bound : Ordinal.{u}) ∧ index = ordinal.toZFSet := by
    rcases hindex with hindex | rfl
    · rcases Ordinal.mem_toZFSet_iff.mp hindex with
        ⟨ordinal, hordinal, hcode⟩
      exact ⟨ordinal, hordinal.le, hcode.symm⟩
    · exact ⟨(bound : Ordinal.{u}), le_refl _, rfl⟩
  rcases hexists with ⟨ordinal, hordinal, hcode⟩
  rcases Ordinal.eq_natCast_of_le_natCast hordinal with ⟨n, hn⟩
  subst ordinal
  exact ⟨n, by exact_mod_cast hordinal, hcode⟩

/-- The actual finite canonical graph is internally valid under the exact
finite-input evaluator contract. -/
theorem canonicalBareHistory_validIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (bound : Nat)
    (hhistory : canonicalBareHistory (bound : Ordinal.{u}) ∈ U) :
    BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory (bound : Ordinal.{u}))
      (bound : Ordinal.{u}).toZFSet := by
  intro index _hindexU hindex
  rcases exists_ordinal_code_le_natCast_of_code_le hindex with
    ⟨n, hn, rfl⟩
  have hnOrdinal : (n : Ordinal.{u}) ≤ (bound : Ordinal.{u}) := by
    exact_mod_cast hn
  have hcomponents := canonicalBareHistory_components_mem hU
    hnOrdinal hhistory
  refine ⟨LStageZF (n : Ordinal.{u}), hcomponents.2,
    canonicalBareHistory_entry hnOrdinal, ?_, ?_⟩
  · intro otherStage _hotherStageU hotherEntry
    exact canonicalBareHistory_functional
      (canonicalBareHistory_entry hnOrdinal) hotherEntry
  · exact canonicalBareHistory_localStateIn_natCast hU fixed hempty
      hcorrect n hnOrdinal hhistory

/-- Predicate-level completeness at a finite index. -/
theorem canonicalBareHistory_stageAtIn_natCast
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat)
    (hhistory : canonicalBareHistory (n : Ordinal.{u}) ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed
      (n : Ordinal.{u}).toZFSet (LStageZF (n : Ordinal.{u})) := by
  exact ⟨canonicalBareHistory (n : Ordinal.{u}), hhistory,
    canonicalBareHistory_validIn_natCast hU fixed hempty hcorrect n
      hhistory,
    canonicalBareHistory_entry (le_refl (n : Ordinal.{u}))⟩

/-- Exact finite-index semantics, with no claim about nonfinite inputs. -/
theorem bareStageAtIn_natCast_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : FiniteBareGodelDefOutputCorrectIn U fixed)
    (n : Nat) (stage : ZFSet.{u})
    (hindex : (n : Ordinal.{u}).toZFSet ∈ U)
    (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory (n : Ordinal.{u}) ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed
        (n : Ordinal.{u}).toZFSet stage <->
      stage = LStageZF (n : Ordinal.{u}) := by
  constructor
  · exact bareStageAtIn_natCast_sound_of_transitive hU fixed hempty
      hcorrect n hindex hstage
  · rintro rfl
    exact canonicalBareHistory_stageAtIn_natCast hU fixed hempty
      hcorrect n hhistory

/-! ## A pair formula restricted to finite indices -/

/-- Free layout `(fixed13,pair)`.  The two hidden witnesses are an index and
a stage; unlike `canonicalBarePairFormula`, this formula explicitly requires
the index to belong to the final fixed parameter, which will be the actual
von Neumann `omega`. -/
def finiteCanonicalBarePairFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (.mem (14 : Fin 16) (12 : Fin 16))
      (.conj
        (FOFormula.rename canonicalBarePairStageRename bareStageAtFormula)
        (Delta0Formula.kuratowskiPairEqAt
          (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)).toFO)))

private theorem comp_finiteCanonicalBarePairStageRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u}) :
    (fun i => canonicalBarePairWitnessRawAssignment fixed pair index stage
      (canonicalBarePairStageRename i)) =
      bareStageAtRawAssignment fixed index stage := by
  funext i
  fin_cases i <;> rfl

private theorem finiteCanonicalBarePairWitnessRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (pair index stage : ZFSet.{u})
    (hfixed : forall i, fixed i ∈ U) (hpair : pair ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    forall i,
      canonicalBarePairWitnessRawAssignment fixed pair index stage i ∈ U := by
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

/-- Exact raw semantics of the finite-index pair formula.  The occurrence of
`index ∈ fixed[12]` is visible in the conclusion; no assumption about that
parameter being `omega` is built into this syntactic theorem. -/
theorem satisfiesIn_finiteCanonicalBarePairFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (pair : ZFSet.{u})
    (hfixed : forall i, fixed i ∈ U) (hpair : pair ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) finiteCanonicalBarePairFormula
        (canonicalBarePairRawAssignment fixed pair) <->
      exists index : ZFSet.{u}, index ∈ U ∧
        index ∈ fixed (12 : Fin 13) ∧
        exists stage : ZFSet.{u}, stage ∈ U ∧
          BareStageAtIn (U : Set ZFSet.{u}) fixed index stage ∧
          pair = ZFSet.pair index stage := by
  simp only [finiteCanonicalBarePairFormula, SatisfiesIn]
  apply exists_congr
  intro index
  apply and_congr_right
  intro hindex
  change index ∈ U at hindex
  constructor
  · rintro ⟨stage, hstage, hindexOmega, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : forall i, witness i ∈ U :=
      finiteCanonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    have hstageAt' : BareStageAtIn (U : Set ZFSet.{u})
        fixed index stage := by
      have hrenamed :
          SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
            (bareStageAtRawAssignment fixed index stage) := by
        rw [satisfiesIn_rename] at hstageAt
        change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
          (fun i => witness (canonicalBarePairStageRename i)) at hstageAt
        rw [comp_finiteCanonicalBarePairStageRename_raw] at hstageAt
        exact hstageAt
      exact (satisfiesIn_bareStageAtFormula_iff hU fixed index stage
        hfixed hindex hstage).mp hrenamed
    have hpairEq' := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)
      witness hwitness).mp hpairEq
    refine ⟨hindexOmega, stage, hstage, hstageAt', ?_⟩
    have hpairCoordinate : witness (13 : Fin 16) = pair := rfl
    have hindexCoordinate : witness (14 : Fin 16) = index := rfl
    have hstageCoordinate : witness (15 : Fin 16) = stage := rfl
    simpa only [hpairCoordinate, hindexCoordinate,
      hstageCoordinate] using hpairEq'
  · rintro ⟨hindexOmega, stage, hstage, hstageAt, hpairEq⟩
    change stage ∈ U at hstage
    let witness := canonicalBarePairWitnessRawAssignment
      fixed pair index stage
    have hwitness : forall i, witness i ∈ U :=
      finiteCanonicalBarePairWitnessRawAssignment_mem fixed pair index stage
        hfixed hpair hindex hstage
    refine ⟨stage, hstage, hindexOmega, ?_, ?_⟩
    · rw [satisfiesIn_rename]
      change SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (fun i => witness (canonicalBarePairStageRename i))
      rw [comp_finiteCanonicalBarePairStageRename_raw]
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

/-! ## Separation of the graph below `omega` -/

@[simp]
theorem stageHistoryFixedParametersRaw_last :
    stageHistoryFixedParametersRaw.{u} (12 : Fin 13) =
      Ordinal.omega0.toZFSet := by
  change (stageHistoryFixedParameters (Fin.last 12)).1 =
    Ordinal.omega0.toZFSet
  rw [stageHistoryFixedParameters_last]

/-- All evaluator parameters, including `omega`, belong to its successor
level. -/
theorem stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ :
    forall i : Fin 13,
      stageHistoryFixedParametersRaw.{u} i ∈
        LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) := by
  intro i
  simpa only [stageHistoryFixedParametersRaw] using
    (stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
      (Order.lt_succ (Ordinal.omega0 : Ordinal.{u})) i)

/-- A finite canonical history remains available one level above
`L_omega`. -/
theorem canonicalBareHistory_natCast_mem_LStageZF_omega_succ (n : Nat) :
    canonicalBareHistory (n : Ordinal.{u}) ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  LStageZF_mono (Order.le_succ (Ordinal.omega0 : Ordinal.{u}))
    (canonicalBareHistory_natCast_mem_LStageZF_omega n)

/-- Under exactly the finite-input evaluator contract, the restricted pair
formula cuts out the graph of the stages strictly below `omega`. -/
theorem satisfiesIn_finiteCanonicalBarePairFormula_omega_succ_iff
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw)
    (pair : ZFSet.{u})
    (hpair : pair ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u}))) :
    SatisfiesIn
        (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :
          Set ZFSet.{u})
        finiteCanonicalBarePairFormula
        (canonicalBarePairRawAssignment
          stageHistoryFixedParametersRaw pair) <->
      pair ∈ canonicalBareHistoryBelow Ordinal.omega0 := by
  rw [satisfiesIn_finiteCanonicalBarePairFormula_iff
    (LStageZF_isTransitive
      (Order.succ (Ordinal.omega0 : Ordinal.{u})))
    stageHistoryFixedParametersRaw pair
    stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ hpair]
  constructor
  · rintro ⟨index, hindexU, hindexOmega, stage, hstageU,
      hstageAt, hpairEq⟩
    rw [stageHistoryFixedParametersRaw_last] at hindexOmega
    rcases Ordinal.mem_toZFSet_iff.mp hindexOmega with
      ⟨ordinal, hordinal, hindexCode⟩
    rcases Ordinal.lt_omega0.mp hordinal with ⟨n, hn⟩
    subst ordinal
    have hindexEq : index = (n : Ordinal.{u}).toZFSet :=
      hindexCode.symm
    subst index
    have hstageEq : stage = LStageZF (n : Ordinal.{u}) :=
      (bareStageAtIn_natCast_iff_of_canonicalHistory_mem
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        stageHistoryFixedParametersRaw
        stageHistoryFixedParametersRaw_empty hcorrect n stage
        hindexU hstageU
        (canonicalBareHistory_natCast_mem_LStageZF_omega_succ n)).mp
          hstageAt
    subst stage
    apply mem_canonicalBareHistoryBelow_iff.mpr
    refine ⟨(n : Ordinal.{u}), Ordinal.natCast_lt_omega0 n, ?_⟩
    simpa only [canonicalBareHistoryPair] using hpairEq.symm
  · intro hpairBelow
    rcases mem_canonicalBareHistoryBelow_iff.mp hpairBelow with
      ⟨ordinal, hordinal, hpairEq⟩
    rcases Ordinal.lt_omega0.mp hordinal with ⟨n, hn⟩
    subst ordinal
    have hcanonicalPair : canonicalBareHistoryPair (n : Ordinal.{u}) ∈
        LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) := by
      simpa only [hpairEq] using hpair
    have hcomponents := orderedPair_components_mem_of_transitive
      (LStageZF_isTransitive
        (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      (by simpa only [canonicalBareHistoryPair] using hcanonicalPair)
    refine ⟨(n : Ordinal.{u}).toZFSet, hcomponents.1, ?_,
      LStageZF (n : Ordinal.{u}), hcomponents.2, ?_, ?_⟩
    · rw [stageHistoryFixedParametersRaw_last]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (Ordinal.natCast_lt_omega0 n)
    · exact canonicalBareHistory_stageAtIn_natCast
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        stageHistoryFixedParametersRaw
        stageHistoryFixedParametersRaw_empty hcorrect n
        (canonicalBareHistory_natCast_mem_LStageZF_omega_succ n)
    · simpa only [canonicalBareHistoryPair] using hpairEq.symm

/-- Genuine internal Separation over `L_(omega+1)` constructs the whole
graph of finite stages. -/
theorem canonicalBareHistoryBelow_omega_mem_DefZF_omega_succ
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistoryBelow Ordinal.omega0 ∈
      DefZF (LStageZF (Order.succ
        (Ordinal.omega0 : Ordinal.{u}))) := by
  rw [mem_DefZF_iff_exists_satisfies]
  let params : Tuple
      (ZFCarrier (LStageZF
        (Order.succ (Ordinal.omega0 : Ordinal.{u})))) 13 :=
    fun i => ⟨stageHistoryFixedParametersRaw i,
      stageHistoryFixedParametersRaw_mem_LStageZF_omega_succ i⟩
  refine ⟨?_, 13, params, finiteCanonicalBarePairFormula, ?_⟩
  · intro pair hpair
    exact LStageZF_mono (Order.le_succ
      (Ordinal.omega0 : Ordinal.{u}))
      (canonicalBareHistoryBelow_subset_LStageZF
        Ordinal.isSuccLimit_omega0 (le_refl Ordinal.omega0) hpair)
  · intro pair
    have hbridge := satisfies_subtype_iff_satisfiesIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :
        Set ZFSet.{u}) finiteCanonicalBarePairFormula
      (snoc params pair)
    have hraw :
        (fun i => (snoc params pair i).1) =
          canonicalBarePairRawAssignment
            stageHistoryFixedParametersRaw pair.1 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simp only [snoc_castSucc, canonicalBarePairRawAssignment,
          params]
    have hsemantic :=
      satisfiesIn_finiteCanonicalBarePairFormula_omega_succ_iff
        hcorrect pair.1 pair.2
    calc
      pair.1 ∈ canonicalBareHistoryBelow Ordinal.omega0 <->
          SatisfiesIn
            (LStageZF (Order.succ
              (Ordinal.omega0 : Ordinal.{u})) : Set ZFSet.{u})
            finiteCanonicalBarePairFormula
            (canonicalBarePairRawAssignment
              stageHistoryFixedParametersRaw pair.1) := hsemantic.symm
      _ <-> FOFormula.Satisfies
          (zfCarrierMem (LStageZF (Order.succ
            (Ordinal.omega0 : Ordinal.{u}))))
          finiteCanonicalBarePairFormula (snoc params pair) := by
        rw [← hraw]
        exact hbridge.symm

/-- The finite-stage graph is therefore present by `L_(omega+2)`. -/
theorem canonicalBareHistoryBelow_omega_mem_LStageZF_omega_succ_succ
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistoryBelow Ordinal.omega0 ∈
      LStageZF (Order.succ
        (Order.succ (Ordinal.omega0 : Ordinal.{u}))) := by
  rw [LStageZF_succ]
  exact canonicalBareHistoryBelow_omega_mem_DefZF_omega_succ hcorrect

/-- The honest `H_omega` bound, conditional only on finite-input evaluator
correctness in `L_(omega+1)`.  This is the exceptional base case for the
later uniform invariant `H_alpha ∈ L_(alpha + omega)`. -/
theorem canonicalBareHistory_omega_mem_LStageZF_add_omega_of_finite_correct
    (hcorrect : FiniteBareGodelDefOutputCorrectIn
      (LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})))
      stageHistoryFixedParametersRaw) :
    canonicalBareHistory (Ordinal.omega0 : Ordinal.{u}) ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) := by
  have htargetLimit := isSuccLimit_add_omega
    (Ordinal.omega0 : Ordinal.{u})
  have homegaTarget : (Ordinal.omega0 : Ordinal.{u}) <
      (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    lt_add_of_pos_right Ordinal.omega0 Ordinal.omega0_pos
  have hsuccTarget : Order.succ (Ordinal.omega0 : Ordinal.{u}) <
      (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    htargetLimit.succ_lt homegaTarget
  have hsuccSuccTarget :
      Order.succ (Order.succ (Ordinal.omega0 : Ordinal.{u})) <
        (Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0 :=
    htargetLimit.succ_lt hsuccTarget
  have hbelow : canonicalBareHistoryBelow Ordinal.omega0 ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) :=
    LStageZF_mono hsuccSuccTarget.le
      (canonicalBareHistoryBelow_omega_mem_LStageZF_omega_succ_succ
        hcorrect)
  have htop : canonicalBareHistoryPair Ordinal.omega0 ∈
      LStageZF ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0) :=
    canonicalBareHistoryPair_mem_LStageZF_of_lt_isSuccLimit
      htargetLimit homegaTarget
  rw [canonicalBareHistory_eq_insert_top]
  exact insert_mem_LStageZF_of_isSuccLimit htargetLimit htop hbelow

end

end Constructible.Model
