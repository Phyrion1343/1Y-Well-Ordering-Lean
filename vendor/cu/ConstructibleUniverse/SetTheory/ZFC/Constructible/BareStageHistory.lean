/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryDefOutputFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryParameters
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryOrdinal
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessorInternalOrder
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryRecursion

/-!
# Relation-free histories for the constructible hierarchy

This file is a proof tool; it does not define a different constructible
hierarchy.  In ordinary set-theoretic language, a bare history through an
ordinal `a` is a set-coded partial function `h` whose value at every
`i <= a` is a set `S_i`, with

* `S_0 = empty`;
* `S_(i+1) = Def(S_i)`;
* `S_l = union (i < l) S_i` when `l` is a nonzero limit ordinal.

The Lean representation uses Kuratowski pairs: `BareHistoryEntry h i s`
means exactly that `<i,s>` belongs to the internal `ZFSet` underlying `h`.
Unlike `ValidStageHistory`, no canonical well-order relation is stored in an
entry or mentioned by the local recursion rule.

The formula interfaces below use the exact quantifiers displayed by the
semantic predicates.  They still reuse `godelDefOutputFormula` at successor
steps, so their first thirteen coordinates are the existing evaluator
parameters `(varTag, appTag, empty, op0, ..., op8, omega)`.  Consequently this
file, by itself, does not assert that those parameters belong to `L_omega`,
nor does it claim absoluteness in every limit level.  The special `L_omega`
case must be handled separately before this tool can support the unrestricted
Condensation Lemma.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Pair-coded history entries -/

/-- In an arbitrary context, the selected history contains the Kuratowski
pair made from the selected index and stage. -/
def bareHistoryEntryAt {n : Nat}
    (history index stage : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) history.castSucc)
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) index.castSucc stage.castSucc).toFO)

/-- Free-variable layout `(history, index, stage)`. -/
def bareHistoryEntryFormula : FOFormula 3 :=
  bareHistoryEntryAt (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)

/-- A direct assignment for the three exposed entry coordinates. -/
def bareHistoryEntryAssignment
    (history index stage : LCarrier.{u}) : Tuple LCarrier.{u} 3 :=
  ![history, index, stage]

/-- The ordinary mathematical meaning of a bare history entry. -/
def BareHistoryEntry
    (history index stage : LCarrier.{u}) : Prop :=
  ZFSet.pair index.1 stage.1 ∈ history.1

@[simp]
theorem satisfies_bareHistoryEntryAt_components {n : Nat}
    (history index stage : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (bareHistoryEntryAt history index stage) s ↔
      ∃ entry : LCarrier.{u},
        entry.1 ∈ (s history).1 ∧
        entry.1 = ZFSet.pair (s index).1 (s stage).1 := by
  simp only [bareHistoryEntryAt, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _hentry
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_bareHistoryEntryAt_iff {n : Nat}
    (history index stage : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (bareHistoryEntryAt history index stage) s ↔
      ZFSet.pair (s index).1 (s stage).1 ∈ (s history).1 := by
  rw [satisfies_bareHistoryEntryAt_components]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    simpa only [heq] using hentry
  · intro hentry
    exact
      ⟨orderedPairLCarrier (s index) (s stage),
        by simpa only [orderedPairLCarrier_val] using hentry,
        orderedPairLCarrier_val (s index) (s stage)⟩

@[simp]
theorem satisfies_bareHistoryEntryFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryEntryFormula
        (bareHistoryEntryAssignment history index stage) ↔
      BareHistoryEntry history index stage := by
  rw [bareHistoryEntryFormula,
    satisfies_bareHistoryEntryAt_iff]
  rfl

/-! ## The exact zero, successor, and limit clauses -/

/-- Layout `(fixed13, history, index, stage)`. -/
def bareHistoryStateLAssignment
    (history index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (snoc stageHistoryFixedParameters history) index) stage

/-- Select `(history,index,stage)` from the shared local-state layout. -/
def bareHistoryStateRename : Fin 3 → Fin 16 :=
  ![13, 14, 15]

theorem comp_bareHistoryStateRename
    (history index stage : LCarrier.{u}) :
    (fun i => bareHistoryStateLAssignment history index stage
      (bareHistoryStateRename i)) =
      bareHistoryEntryAssignment history index stage := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem bareHistoryStateLAssignment_history
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (13 : Fin 16) =
      history := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_index
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (14 : Fin 16) =
      index := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_stage
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (15 : Fin 16) =
      stage := by
  rfl

@[simp] theorem bareHistoryStateLAssignment_empty
    (history index stage : LCarrier.{u}) :
    bareHistoryStateLAssignment history index stage (2 : Fin 16) =
      emptyLCarrier := by
  change stageHistoryFixedParameters (2 : Fin 13) = emptyLCarrier
  exact stageHistoryFixedParameters_empty

/-- The local rule at index zero.  Coordinate `2` of the fixed prefix is the
canonical empty set. -/
def bareHistoryBaseStateFormula : FOFormula 16 :=
  .conj
    (.eq (14 : Fin 16) (2 : Fin 16))
    (.eq (15 : Fin 16) (2 : Fin 16))

@[simp]
theorem satisfies_bareHistoryBaseStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryBaseStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      index = emptyLCarrier ∧ stage = emptyLCarrier := by
  simp only [bareHistoryBaseStateFormula, FOFormula.Satisfies,
    bareHistoryStateLAssignment_index,
    bareHistoryStateLAssignment_stage,
    bareHistoryStateLAssignment_empty]

/-- After the two successor witnesses the layout is
`(fixed13, history, index, stage, predecessorIndex, predecessorStage)`.
This permutation selects the existing output-formula layout
`(predecessorStage, fixed13, stage)`. -/
def bareHistorySuccessorDefRename : Fin 15 → Fin 18 :=
  Fin.lastCases
    (15 : Fin 18)
    (fun i14 => Fin.cases
      (17 : Fin 18)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Assignment after adjoining the predecessor index and predecessor stage. -/
def bareHistorySuccessorWitnessAssignment
    (history index stage predecessorIndex predecessorStage : LCarrier.{u}) :
    Tuple LCarrier.{u} 18 :=
  snoc (snoc (bareHistoryStateLAssignment history index stage)
    predecessorIndex) predecessorStage

private theorem bareHistorySuccessorDefRename_fixed (k : Fin 12) :
    bareHistorySuccessorDefRename k.castSucc.succ.castSucc =
      Fin.castLE (by decide) k.castSucc := by
  unfold bareHistorySuccessorDefRename
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

theorem comp_bareHistorySuccessorDefRename
    (history index stage predecessorIndex predecessorStage : LCarrier.{u}) :
    (fun i => bareHistorySuccessorWitnessAssignment history index stage
      predecessorIndex predecessorStage
      (bareHistorySuccessorDefRename i)) =
      Godel.RudimentaryTerm.godelDefOutputLAssignment
        predecessorStage stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · change predecessorStage = predecessorStage
      rfl
    · refine Fin.lastCases ?_ (fun k => ?_) i13
      · change stageHistoryFixedParameters (Fin.last 12) =
          (⟨Ordinal.omega0.toZFSet, omega_mem_L⟩ : LCarrier.{u})
        exact stageHistoryFixedParameters_last
      · rw [bareHistorySuccessorDefRename_fixed]
        rw [show Fin.castLE (by decide) k.castSucc =
            k.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        rw [show k.castSucc.succ.castSucc =
            k.succ.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareHistorySuccessorWitnessAssignment,
          bareHistoryStateLAssignment,
          Godel.RudimentaryTerm.godelDefOutputLAssignment,
          snoc_castSucc]
        exact stageHistoryFixedParameters_init predecessorStage k

/-- The local successor clause: the previous entry exists and the new stage
is exactly `godelDef` of its stage coordinate. -/
def bareHistorySuccessorStateFormula : FOFormula 16 :=
  .ex (.ex
    (.conj
      (Delta0Formula.successorFOAt (14 : Fin 18) (16 : Fin 18))
      (.conj
        (bareHistoryEntryAt
          (13 : Fin 18) (16 : Fin 18) (17 : Fin 18))
        (FOFormula.rename bareHistorySuccessorDefRename
          Godel.RudimentaryTerm.godelDefOutputFormula))))

@[simp]
theorem satisfies_bareHistorySuccessorStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistorySuccessorStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      ∃ predecessorIndex predecessorStage : LCarrier.{u},
        index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
        BareHistoryEntry history predecessorIndex predecessorStage ∧
        stage.1 = Godel.godelDef predecessorStage.1 := by
  simp only [bareHistorySuccessorStateFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_bareHistoryEntryAt_iff, BareHistoryEntry,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro predecessorIndex
  apply exists_congr
  intro predecessorStage
  rw [show
    snoc (snoc (bareHistoryStateLAssignment history index stage)
      predecessorIndex) predecessorStage =
        bareHistorySuccessorWitnessAssignment history index stage
          predecessorIndex predecessorStage by rfl]
  rw [comp_bareHistorySuccessorDefRename,
    Godel.RudimentaryTerm.satisfies_godelDefOutputFormula_iff]
  rfl

/-- Free-variable layout `(history,index,stage)`.  At a limit index, `stage`
is the union of all earlier stage values. -/
def bareHistoryLimitStateFormula : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (3 : Fin 4) (2 : Fin 4))
      (FOFormula.boundedEx (1 : Fin 4)
        (.ex
          (.conj
            (bareHistoryEntryAt
              (0 : Fin 6) (4 : Fin 6) (5 : Fin 6))
            (.mem (3 : Fin 6) (5 : Fin 6))))))

/-- Exact external meaning of the limit-union clause. -/
def BareHistoryLimitState
    (history index stage : LCarrier.{u}) : Prop :=
  ∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
      ∃ earlierStage : LCarrier.{u},
        BareHistoryEntry history earlierIndex earlierStage ∧
        z.1 ∈ earlierStage.1

@[simp]
theorem satisfies_bareHistoryLimitStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryLimitStateFormula
        (bareHistoryEntryAssignment history index stage) ↔
      BareHistoryLimitState history index stage := by
  simp only [bareHistoryLimitStateFormula, BareHistoryLimitState,
    bareHistoryEntryAssignment, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, satisfies_bareHistoryEntryAt_iff,
    BareHistoryEntry]
  rfl

/-- The current index is the empty set. -/
def bareHistoryIndexIsZeroFormula : FOFormula 16 :=
  .eq (14 : Fin 16) (2 : Fin 16)

/-- The current index is a von Neumann successor. -/
def bareHistoryIndexHasPredecessorFormula : FOFormula 16 :=
  .ex (Delta0Formula.successorFOAt (14 : Fin 17) (16 : Fin 17))

@[simp]
theorem satisfies_bareHistoryIndexIsZeroFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryIndexIsZeroFormula
        (bareHistoryStateLAssignment history index stage) ↔
      index = emptyLCarrier := by
  simp only [bareHistoryIndexIsZeroFormula, FOFormula.Satisfies,
    bareHistoryStateLAssignment_index,
    bareHistoryStateLAssignment_empty]

@[simp]
theorem satisfies_bareHistoryIndexHasPredecessorFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryIndexHasPredecessorFormula
        (bareHistoryStateLAssignment history index stage) ↔
      ∃ predecessor : LCarrier.{u},
        index.1 = insert predecessor.1 predecessor.1 := by
  simp only [bareHistoryIndexHasPredecessorFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  apply exists_congr
  intro predecessor
  change (index.1 = insert predecessor.1 predecessor.1) ↔ _
  rfl

/-- The ordinary three-way recursion rule, with no order-relation output. -/
def BareHistoryLocalState
    (history index stage : LCarrier.{u}) : Prop :=
  (index = emptyLCarrier ∧ stage = emptyLCarrier) ∨
  (∃ predecessorIndex predecessorStage : LCarrier.{u},
    index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
    BareHistoryEntry history predecessorIndex predecessorStage ∧
    stage.1 = Godel.godelDef predecessorStage.1) ∨
  (index ≠ emptyLCarrier ∧
    ¬ ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1) ∧
    BareHistoryLimitState history index stage

/-- Formula for the ordinary three-way recursion rule. -/
def bareHistoryLocalStateFormula : FOFormula 16 :=
  .disj
    bareHistoryBaseStateFormula
    (.disj
      bareHistorySuccessorStateFormula
      (.conj
        (.conj
          (.neg bareHistoryIndexIsZeroFormula)
          (.neg bareHistoryIndexHasPredecessorFormula))
        (FOFormula.rename bareHistoryStateRename
          bareHistoryLimitStateFormula)))

@[simp]
theorem satisfies_bareHistoryLocalStateFormula
    (history index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareHistoryLocalStateFormula
        (bareHistoryStateLAssignment history index stage) ↔
      BareHistoryLocalState history index stage := by
  simp only [bareHistoryLocalStateFormula, BareHistoryLocalState,
    FOFormula.satisfies_disj, FOFormula.Satisfies,
    satisfies_bareHistoryBaseStateFormula,
    satisfies_bareHistorySuccessorStateFormula,
    satisfies_bareHistoryIndexIsZeroFormula,
    satisfies_bareHistoryIndexHasPredecessorFormula,
    FOFormula.satisfies_rename, comp_bareHistoryStateRename,
    satisfies_bareHistoryLimitStateFormula]

/-! ## Bounded total functional histories -/

/-- Layout `(fixed13,history,bound)`. -/
def bareValidStageHistoryLAssignment
    (history bound : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters history) bound

/-- Select `(fixed13,history,index,stage)` after the index and stage witnesses
have been appended to `(fixed13,history,bound)`. -/
def bareValidHistoryLocalRename : Fin 16 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i15 => Fin.lastCases
      (15 : Fin 17)
      (fun i14 => Fin.lastCases
        (13 : Fin 17)
        (fun i13 => Fin.castLE (by decide) i13)
        i14)
      i15)

private theorem bareValidHistoryLocalRename_fixed (i : Fin 13) :
    bareValidHistoryLocalRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp [bareValidHistoryLocalRename]

/-- At one selected index there is one unique stage, and it obeys the local
recursion rule.  Before choosing the stage, the layout is
`(fixed13,history,bound,index)`. -/
def bareValidStageHistoryIndexBody : FOFormula 16 :=
  .ex
    (.conj
      (bareHistoryEntryAt
        (13 : Fin 17) (15 : Fin 17) (16 : Fin 17))
      (.conj
        (FOFormula.all
          (FOFormula.imp
            (bareHistoryEntryAt
              (13 : Fin 18) (15 : Fin 18) (17 : Fin 18))
            (.eq (17 : Fin 18) (16 : Fin 18))))
        (FOFormula.rename bareValidHistoryLocalRename
          bareHistoryLocalStateFormula)))

/-- A history is total, stage-functional, and locally correct through the
supplied bound.  Extra members not encoding entries are harmless. -/
def bareValidStageHistoryFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.imp
      (FOFormula.disj
        (.mem (15 : Fin 16) (14 : Fin 16))
        (.eq (15 : Fin 16) (14 : Fin 16)))
      bareValidStageHistoryIndexBody)

/-- Exact external predicate expressed by `bareValidStageHistoryFormula`. -/
def BareValidStageHistory (history bound : LCarrier.{u}) : Prop :=
  ∀ index : LCarrier.{u},
    (index.1 ∈ bound.1 ∨ index = bound) →
      ∃ stage : LCarrier.{u},
        BareHistoryEntry history index stage ∧
        (∀ otherStage : LCarrier.{u},
          BareHistoryEntry history index otherStage →
            otherStage = stage) ∧
        BareHistoryLocalState history index stage

private theorem comp_bareValidHistoryLocalRename
    (history bound index stage : LCarrier.{u}) :
    (fun i =>
      snoc (snoc (bareValidStageHistoryLAssignment history bound) index)
        stage (bareValidHistoryLocalRename i)) =
      bareHistoryStateLAssignment history index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · change index = index
      rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · change history = history
        rfl
      · rw [bareValidHistoryLocalRename_fixed]
        rw [show Fin.castLE (by decide) i13 =
            i13.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareValidStageHistoryLAssignment,
          bareHistoryStateLAssignment, snoc_castSucc]

@[simp]
theorem satisfies_bareValidStageHistoryIndexBody
    (history bound index : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareValidStageHistoryIndexBody
        (snoc (bareValidStageHistoryLAssignment history bound) index) ↔
      ∃ stage : LCarrier.{u},
        BareHistoryEntry history index stage ∧
        (∀ otherStage : LCarrier.{u},
          BareHistoryEntry history index otherStage →
            otherStage = stage) ∧
        BareHistoryLocalState history index stage := by
  simp only [bareValidStageHistoryIndexBody, FOFormula.Satisfies,
    satisfies_bareHistoryEntryAt_iff, BareHistoryEntry,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro stage
  rw [comp_bareValidHistoryLocalRename,
    satisfies_bareHistoryLocalStateFormula]
  rfl

@[simp]
theorem satisfies_bareValidStageHistoryFormula
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareValidStageHistoryFormula
        (bareValidStageHistoryLAssignment history bound) ↔
      BareValidStageHistory history bound := by
  simp only [bareValidStageHistoryFormula, BareValidStageHistory,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_disj, FOFormula.Satisfies]
  apply forall_congr'
  intro index
  change
    ((index.1 ∈ bound.1 ∨ index = bound) →
      FOFormula.Satisfies LMem bareValidStageHistoryIndexBody
        (snoc (bareValidStageHistoryLAssignment history bound) index)) ↔ _
  rw [satisfies_bareValidStageHistoryIndexBody]

/-! ## A history-independent stage-output formula -/

/-- Layout `(fixed13,index,stage)`. -/
def bareStageAtLAssignment
    (index stage : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) stage

/-- Select `(fixed13,history,bound=index)` after binding a hidden history. -/
def bareStageAtValidHistoryRename : Fin 15 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 13]

/-- There is a valid bare history through `index` with the stated stage at
its top entry. -/
def BareStageAt (index stage : LCarrier.{u}) : Prop :=
  ∃ history : LCarrier.{u},
    BareValidStageHistory history index ∧
    BareHistoryEntry history index stage

/-- Formula exposing only an index and its constructible-stage output. -/
def bareStageAtFormula : FOFormula 15 :=
  .ex
    (.conj
      (FOFormula.rename bareStageAtValidHistoryRename
        bareValidStageHistoryFormula)
      (bareHistoryEntryAt
        (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)))

private theorem comp_bareStageAtValidHistoryRename
    (index stage history : LCarrier.{u}) :
    (fun i => snoc (bareStageAtLAssignment index stage) history
      (bareStageAtValidHistoryRename i)) =
      bareValidStageHistoryLAssignment history index := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_bareStageAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareStageAtFormula
        (bareStageAtLAssignment index stage) ↔
      BareStageAt index stage := by
  simp only [bareStageAtFormula, BareStageAt, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro history
  rw [comp_bareStageAtValidHistoryRename,
    satisfies_bareValidStageHistoryFormula,
    satisfies_bareHistoryEntryAt_iff]
  rfl

/-! ## Full-`L` existence via a relation-forgetting projection -/

/-- Auxiliary Replacement output.  Its layout is `(fixed13,index,pair)`;
the two hidden witnesses are the stage and the old relation coordinate.  The
relation is used only to invoke the already verified existence theorem and
is forgotten from the output pair. -/
def bareStagePairAtFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (FOFormula.rename stageEntryStateRename stageStateAtFormula)
      (Delta0Formula.kuratowskiPairEqAt
        (14 : Fin 17) (13 : Fin 17) (15 : Fin 17)).toFO))

/-- Exact external semantics of the projection formula. -/
def BareStagePairAt (index pair : LCarrier.{u}) : Prop :=
  ∃ stage relation : LCarrier.{u},
    StageStateAt index stage relation ∧
    pair.1 = ZFSet.pair index.1 stage.1

@[simp]
theorem satisfies_bareStagePairAtFormula
    (index pair : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareStagePairAtFormula
        (stageEntryAtLAssignment index pair) ↔
      BareStagePairAt index pair := by
  simp only [bareStagePairAtFormula, BareStagePairAt,
    FOFormula.Satisfies]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [FOFormula.satisfies_rename,
    comp_stageEntryStateRename,
    satisfies_stageStateAtFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  rfl

/-- Replacement in `L` constructs the pair graph of all stage outputs below
the successor of `bound`, hence through `bound` itself. -/
theorem exists_bareStagePairFamily (bound : Ordinal.{u}) :
    ∃ history : LCarrier.{u}, ∀ pair : LCarrier.{u},
      pair.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 ∧
          BareStagePairAt index pair := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 →
        ∃! pair : LCarrier.{u},
          FOFormula.Satisfies LMem bareStagePairAtFormula
            (snoc (snoc stageHistoryFixedParameters index) pair) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, _hordinal, rfl⟩
    rcases exists_stageStateAt_ordinal ordinal with
      ⟨relation, hstate⟩
    let pair := orderedPairLCarrier
      (ordinalLCarrier ordinal) (stageLCarrier ordinal)
    refine ⟨pair, ?_, ?_⟩
    · change FOFormula.Satisfies LMem bareStagePairAtFormula
        (stageEntryAtLAssignment (ordinalLCarrier ordinal) pair)
      apply (satisfies_bareStagePairAtFormula
        (ordinalLCarrier ordinal) pair).mpr
      exact ⟨stageLCarrier ordinal, relation, hstate,
        orderedPairLCarrier_val
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)⟩
    · intro other hother
      have hother' :=
        (satisfies_bareStagePairAtFormula
          (ordinalLCarrier ordinal) other).mp hother
      rcases hother' with
        ⟨otherStage, otherRelation, hotherState, hotherCode⟩
      have houtputs := stageStateAt_ordinal_outputs_unique ordinal
        hotherState hstate
      apply Subtype.ext
      calc
        other.1 = ZFSet.pair (ordinalLCarrier ordinal).1
            otherStage.1 := hotherCode
        _ = ZFSet.pair (ordinalLCarrier ordinal).1
            (stageLCarrier ordinal).1 := by rw [houtputs.1]
        _ = pair.1 := (orderedPairLCarrier_val
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)).symm
  rcases exists_replacementLCarrier bareStagePairAtFormula
      stageHistoryFixedParameters
      (ordinalLCarrier (Order.succ bound)) hfun with
    ⟨history, hhistory⟩
  refine ⟨history, ?_⟩
  intro pair
  rw [hhistory]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_bareStagePairAtFormula index pair

/-- Exact lookup in a projected pair family: at a canonical index below the
family bound, the only stored stage is the corresponding `LStageZF` level. -/
theorem bareHistoryEntry_iff_stageLCarrier_of_pairFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ pair : LCarrier.{u},
      pair.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 ∧
          BareStagePairAt index pair)
    {ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (stage : LCarrier.{u}) :
    BareHistoryEntry history (ordinalLCarrier ordinal) stage ↔
      stage = stageLCarrier ordinal := by
  let pair := orderedPairLCarrier (ordinalLCarrier ordinal) stage
  have hpair : pair.1 =
      ZFSet.pair (ordinalLCarrier ordinal).1 stage.1 :=
    orderedPairLCarrier_val (ordinalLCarrier ordinal) stage
  constructor
  · intro hentry
    have hmem : pair.1 ∈ history.1 := by
      rw [hpair]
      exact hentry
    rcases (hhistory pair).mp hmem with
      ⟨otherIndex, _hotherIndex, otherStage, otherRelation,
        hotherState, hotherCode⟩
    have hcodes :
        ZFSet.pair (ordinalLCarrier ordinal).1 stage.1 =
          ZFSet.pair otherIndex.1 otherStage.1 :=
      hpair.symm.trans hotherCode
    have hcoordinates := ZFSet.pair_inj.mp hcodes
    have hindex : otherIndex = ordinalLCarrier ordinal :=
      Subtype.ext hcoordinates.1.symm
    subst otherIndex
    rcases exists_stageStateAt_ordinal ordinal with
      ⟨relation, hcanonical⟩
    have houtputs := stageStateAt_ordinal_outputs_unique ordinal
      hotherState hcanonical
    exact Subtype.ext (hcoordinates.2.trans
      (congrArg Subtype.val houtputs.1))
  · intro hstage
    subst stage
    change ZFSet.pair (ordinalLCarrier ordinal).1
      (stageLCarrier ordinal).1 ∈ history.1
    rw [← orderedPairLCarrier_val]
    apply (hhistory (orderedPairLCarrier
      (ordinalLCarrier ordinal) (stageLCarrier ordinal))).mpr
    refine ⟨ordinalLCarrier ordinal, ?_, ?_⟩
    · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        (Order.succ bound) ordinal).mpr (Order.lt_succ_iff.mpr hordinal)
    · rcases exists_stageStateAt_ordinal ordinal with
        ⟨relation, hstate⟩
      exact ⟨stageLCarrier ordinal, relation, hstate,
        orderedPairLCarrier_val
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)⟩

private theorem stageLCarrier_zero_eq_empty :
    stageLCarrier (0 : Ordinal.{u}) = emptyLCarrier := by
  apply Subtype.ext
  change LStageZF 0 = (∅ : ZFSet.{u})
  exact LStageZF_zero

/-- The actual level `L_ordinal` obeys the bare local recursion rule in every
projected pair family that contains all levels through `bound`. -/
theorem bareHistoryLocalState_stageLCarrier_of_pairFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ pair : LCarrier.{u},
      pair.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 ∧
          BareStagePairAt index pair)
    (ordinal : Ordinal.{u}) (hordinal : ordinal ≤ bound) :
    BareHistoryLocalState history (ordinalLCarrier ordinal)
      (stageLCarrier ordinal) := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      exact Or.inl ⟨ordinalLCarrier_zero,
        stageLCarrier_zero_eq_empty⟩
  | add_one alpha _ih =>
      rw [← Order.succ_eq_add_one]
      refine Or.inr (Or.inl
        ⟨ordinalLCarrier alpha, stageLCarrier alpha,
          ordinalLCarrier_succ_val alpha, ?_, ?_⟩)
      · apply (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
          hhistory ((Order.le_succ alpha).trans hordinal)
          (stageLCarrier alpha)).mpr
        rfl
      · change LStageZF (Order.succ alpha) =
          Godel.godelDef (LStageZF alpha)
        rw [LStageZF_succ,
          Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  | limit limit hl _ih =>
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · constructor
        · intro hzero
          have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
            hzero.trans ordinalLCarrier_zero.symm
          exact hl.ne_bot (ordinalLCarrier_injective hcodes)
        · exact ordinalLCarrier_limit_no_predecessor hl
      · intro z
        constructor
        · intro hz
          change z.1 ∈ LStageZF limit at hz
          rcases (mem_LStageZF_limit_iff hl).mp hz with
            ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
          have hindex :
              (ordinalLCarrier earlierOrdinal).1 ∈
                (ordinalLCarrier limit).1 :=
            (ordinalLCarrier_mem_ordinalLCarrier_iff
              limit earlierOrdinal).mpr hearlierOrdinal
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            stageLCarrier earlierOrdinal, ?_, ?_⟩
          · apply (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
              hhistory (hearlierOrdinal.le.trans hordinal)
              (stageLCarrier earlierOrdinal)).mpr
            rfl
          · exact hzEarlier
        · rintro ⟨earlierIndex, hindex, earlierStage,
            hearlierEntry, hzEarlier⟩
          rcases Ordinal.mem_toZFSet_iff.mp hindex with
            ⟨earlierOrdinal, hearlierOrdinal, hcode⟩
          have hindexEq :
              earlierIndex = ordinalLCarrier earlierOrdinal := by
            apply Subtype.ext
            exact hcode.symm
          subst earlierIndex
          have hearlierStage :=
            (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
              hhistory (hearlierOrdinal.le.trans hordinal)
              earlierStage).mp hearlierEntry
          change z.1 ∈ LStageZF limit
          apply (mem_LStageZF_limit_iff hl).mpr
          refine ⟨earlierOrdinal, hearlierOrdinal, ?_⟩
          simpa only [hearlierStage, stageLCarrier_val] using hzEarlier

/-- A projected pair family is a genuine valid bare history through its
bound. -/
theorem bareValidStageHistory_of_pairFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ pair : LCarrier.{u},
      pair.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 ∧
          BareStagePairAt index pair) :
    BareValidStageHistory history (ordinalLCarrier bound) := by
  intro index hindex
  have hindexSucc :
      index.1 ∈ (ordinalLCarrier (Order.succ bound)).1 := by
    rcases hindex with hindex | rfl
    · exact Ordinal.toZFSet_monotone (Order.le_succ bound) hindex
    · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        (Order.succ bound) bound).mpr (Order.lt_succ bound)
  rcases exists_eq_ordinalLCarrier_of_mem hindexSucc with
    ⟨ordinal, hordinalSucc, rfl⟩
  have hordinal : ordinal ≤ bound :=
    Order.lt_succ_iff.mp hordinalSucc
  refine ⟨stageLCarrier ordinal, ?_, ?_, ?_⟩
  · apply (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
      hhistory hordinal (stageLCarrier ordinal)).mpr
    rfl
  · intro otherStage hother
    exact (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
      hhistory hordinal otherStage).mp hother
  · exact bareHistoryLocalState_stageLCarrier_of_pairFamily
      hhistory ordinal hordinal

/-- Every ambient ordinal has a full-`L` witness for the relation-free stage
formula, with output exactly `LStageZF ordinal`. -/
theorem bareStageAt_stageLCarrier (ordinal : Ordinal.{u}) :
    BareStageAt (ordinalLCarrier ordinal) (stageLCarrier ordinal) := by
  rcases exists_bareStagePairFamily ordinal with ⟨history, hhistory⟩
  refine ⟨history,
    bareValidStageHistory_of_pairFamily hhistory, ?_⟩
  apply (bareHistoryEntry_iff_stageLCarrier_of_pairFamily
    hhistory (le_refl ordinal) (stageLCarrier ordinal)).mpr
  rfl

/-! ## Identification with the previously defined hierarchy -/

/-- A valid history through a later ordinal remains valid through every
earlier ordinal. -/
theorem BareValidStageHistory.restrictOrdinal
    {history : LCarrier.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : BareValidStageHistory history (ordinalLCarrier beta))
    (halpha : alpha ≤ beta) :
    BareValidStageHistory history (ordinalLCarrier alpha) := by
  intro index hindex
  apply hvalid index
  rcases hindex with hindex | rfl
  · left
    exact Ordinal.toZFSet_monotone halpha hindex
  · rcases halpha.eq_or_lt with rfl | halpha
    · exact Or.inr rfl
    · exact Or.inl
        ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr halpha)

/-- An entry in an ordinal-bounded valid history gives a self-contained
`BareStageAt` witness at every earlier canonical index. -/
theorem bareStageAt_of_validHistory
    {history index stage : LCarrier.{u}}
    {alpha beta : Ordinal.{u}}
    (hindex : index = ordinalLCarrier alpha)
    (halpha : alpha ≤ beta)
    (hvalid : BareValidStageHistory history (ordinalLCarrier beta))
    (hentry : BareHistoryEntry history index stage) :
    BareStageAt index stage := by
  subst index
  exact ⟨history, hvalid.restrictOrdinal halpha, hentry⟩

/-- At its bound, validity transfers the local recursion rule to any entry
at that bound. -/
theorem BareValidStageHistory.localState_of_entry
    {history bound stage : LCarrier.{u}}
    (hvalid : BareValidStageHistory history bound)
    (hentry : BareHistoryEntry history bound stage) :
    BareHistoryLocalState history bound stage := by
  rcases hvalid bound (Or.inr rfl) with
    ⟨chosenStage, _hchosen, hunique, hlocal⟩
  have hstage := hunique stage hentry
  simpa only [hstage] using hlocal

private theorem emptyLCarrier_ne_insert_self_bare
    (predecessor : LCarrier.{u}) :
    ¬ emptyLCarrier.1 = insert predecessor.1 predecessor.1 := by
  intro h
  have hmem : predecessor.1 ∈ emptyLCarrier.1 := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact not_mem_emptyLCarrier predecessor hmem

/-- On the canonical zero index, the local rule has exactly the empty stage. -/
theorem bareHistoryLocalState_zero_iff
    (history stage : LCarrier.{u}) :
    BareHistoryLocalState history (ordinalLCarrier 0) stage ↔
      stage = emptyLCarrier := by
  rw [ordinalLCarrier_zero]
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · exact hbase.2
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, hpredecessor, _⟩
      exact (emptyLCarrier_ne_insert_self_bare
        predecessorIndex hpredecessor).elim
    · exact (hlimit.1.1 rfl).elim
  · rintro rfl
    exact Or.inl ⟨rfl, rfl⟩

/-- On a canonical successor index, the local rule is exactly one
`godelDef` step from the canonical predecessor entry. -/
theorem bareHistoryLocalState_successor_iff
    (history : LCarrier.{u}) (alpha : Ordinal.{u})
    (stage : LCarrier.{u}) :
    BareHistoryLocalState history
        (ordinalLCarrier (Order.succ alpha)) stage ↔
      ∃ predecessorStage : LCarrier.{u},
        BareHistoryEntry history (ordinalLCarrier alpha)
          predecessorStage ∧
        stage.1 = Godel.godelDef predecessorStage.1 := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes :
          ordinalLCarrier (Order.succ alpha) = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : Order.succ alpha = 0 :=
        ordinalLCarrier_injective hcodes
      exact (Order.succ_ne_bot alpha hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, predecessorStage,
          hpredecessor, hentry, hstage⟩
      have hindex :=
        (ordinalLCarrier_successor_predecessor_iff
          alpha predecessorIndex).mp hpredecessor
      subst predecessorIndex
      exact ⟨predecessorStage, hentry, hstage⟩
    · have hpredecessor :
          ∃ predecessor : LCarrier.{u},
            (ordinalLCarrier (Order.succ alpha)).1 =
              insert predecessor.1 predecessor.1 :=
        ⟨ordinalLCarrier alpha, ordinalLCarrier_succ_val alpha⟩
      exact (hlimit.1.2 hpredecessor).elim
  · rintro ⟨predecessorStage, hentry, hstage⟩
    exact Or.inr (Or.inl
      ⟨ordinalLCarrier alpha, predecessorStage,
        ordinalLCarrier_succ_val alpha, hentry, hstage⟩)

/-- On a nonzero limit ordinal, the local rule is exactly the union of all
earlier stage entries. -/
theorem bareHistoryLocalState_limit_iff
    (history : LCarrier.{u}) {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) (stage : LCarrier.{u}) :
    BareHistoryLocalState history (ordinalLCarrier limit) stage ↔
      BareHistoryLimitState history (ordinalLCarrier limit) stage := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : limit = 0 := ordinalLCarrier_injective hcodes
      exact (hl.ne_bot hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, hpredecessor, _⟩
      exact (ordinalLCarrier_limit_no_predecessor hl
        ⟨predecessorIndex, hpredecessor⟩).elim
    · exact hlimit.2
  · intro hlimit
    refine Or.inr (Or.inr ⟨?_, hlimit⟩)
    constructor
    · intro hzero
      have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hzero.trans ordinalLCarrier_zero.symm
      exact hl.ne_bot (ordinalLCarrier_injective hcodes)
    · exact ordinalLCarrier_limit_no_predecessor hl

/-- Semantic exactness: every ordinal-indexed output admitted by the bare
formula is the already defined constructible stage `LStageZF ordinal`.
This is a conditional correctness theorem, not yet an internal-existence
theorem for arbitrary `L_theta`. -/
theorem bareStageAt_ordinal_eq_stageLCarrier (ordinal : Ordinal.{u}) :
    ∀ {stage : LCarrier.{u}},
      BareStageAt (ordinalLCarrier ordinal) stage →
        stage = stageLCarrier ordinal := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro stage hstate
      rcases hstate with ⟨history, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hstage :=
        (bareHistoryLocalState_zero_iff history stage).mp hlocal
      apply Subtype.ext
      rw [hstage]
      change (∅ : ZFSet.{u}) = LStageZF 0
      exact (LStageZF_zero : LStageZF (0 : Ordinal.{u}) = ∅).symm
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      intro stage hstate
      rcases hstate with ⟨history, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hentry
      rcases (bareHistoryLocalState_successor_iff
          history alpha stage).mp hlocal with
        ⟨predecessorStage, predecessorEntry, hstage⟩
      have hpredecessorState :
          BareStageAt (ordinalLCarrier alpha) predecessorStage :=
        bareStageAt_of_validHistory rfl (Order.le_succ alpha)
          hvalid predecessorEntry
      have hpredecessor := ih hpredecessorState
      apply Subtype.ext
      calc
        stage.1 = Godel.godelDef predecessorStage.1 := hstage
        _ = Godel.godelDef (LStageZF alpha) := by
          rw [hpredecessor]
          rfl
        _ = Constructible.DefZF (LStageZF alpha) :=
          (Godel.DefZF_eq_godelDef
            (LStageZF_isTransitive alpha)).symm
        _ = LStageZF (Order.succ alpha) := (LStageZF_succ alpha).symm
        _ = (stageLCarrier (Order.succ alpha)).1 := rfl
  | limit limit hl ih =>
      intro stage hstate
      rcases hstate with ⟨history, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hlimit :=
        (bareHistoryLocalState_limit_iff history hl stage).mp hlocal
      apply lCarrier_extensionality
      intro z
      constructor
      · intro hz
        rcases (hlimit z).mp hz with
          ⟨earlierIndex, hindex, earlierStage,
            hearlierEntry, hzEarlier⟩
        rcases Ordinal.mem_toZFSet_iff.mp hindex with
          ⟨earlierOrdinal, hearlierOrdinal, hcode⟩
        have hindexEq : earlierIndex = ordinalLCarrier earlierOrdinal := by
          apply Subtype.ext
          exact hcode.symm
        subst earlierIndex
        have hearlierState :
            BareStageAt (ordinalLCarrier earlierOrdinal) earlierStage :=
          bareStageAt_of_validHistory rfl hearlierOrdinal.le
            hvalid hearlierEntry
        have hearlierStage := ih earlierOrdinal hearlierOrdinal hearlierState
        change z.1 ∈ LStageZF limit
        apply (mem_LStageZF_limit_iff hl).mpr
        refine ⟨earlierOrdinal, hearlierOrdinal, ?_⟩
        simpa only [hearlierStage, stageLCarrier_val] using hzEarlier
      · intro hz
        change z.1 ∈ LStageZF limit at hz
        rcases (mem_LStageZF_limit_iff hl).mp hz with
          ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
        have hindex :
            (ordinalLCarrier earlierOrdinal).1 ∈
              (ordinalLCarrier limit).1 :=
          (ordinalLCarrier_mem_ordinalLCarrier_iff
            limit earlierOrdinal).mpr hearlierOrdinal
        rcases hvalid (ordinalLCarrier earlierOrdinal) (Or.inl hindex) with
          ⟨earlierStage, hearlierEntry, _hunique, _hlocal⟩
        have hearlierState :
            BareStageAt (ordinalLCarrier earlierOrdinal) earlierStage :=
          bareStageAt_of_validHistory rfl hearlierOrdinal.le
            hvalid hearlierEntry
        have hearlierStage := ih earlierOrdinal hearlierOrdinal hearlierState
        apply (hlimit z).mpr
        refine ⟨ordinalLCarrier earlierOrdinal, hindex,
          earlierStage, hearlierEntry, ?_⟩
        simpa only [hearlierStage, stageLCarrier_val] using hzEarlier

/-- Consequently the bare formula has at most one output at every canonical
ordinal index. -/
theorem bareStageAt_ordinal_unique (ordinal : Ordinal.{u})
    {stage otherStage : LCarrier.{u}}
    (hstage : BareStageAt (ordinalLCarrier ordinal) stage)
    (hother : BareStageAt (ordinalLCarrier ordinal) otherStage) :
    stage = otherStage :=
  (bareStageAt_ordinal_eq_stageLCarrier ordinal hstage).trans
    (bareStageAt_ordinal_eq_stageLCarrier ordinal hother).symm

/-- Exact full-`L` semantics at a canonical ordinal index. -/
theorem bareStageAt_ordinal_iff
    (ordinal : Ordinal.{u}) (stage : LCarrier.{u}) :
    BareStageAt (ordinalLCarrier ordinal) stage ↔
      stage = stageLCarrier ordinal := by
  constructor
  · exact bareStageAt_ordinal_eq_stageLCarrier ordinal
  · rintro rfl
    exact bareStageAt_stageLCarrier ordinal

/-- The syntactic formula therefore defines exactly `LStageZF ordinal` in
the full constructible universe. -/
theorem satisfies_bareStageAtFormula_ordinal_iff
    (ordinal : Ordinal.{u}) (stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem bareStageAtFormula
        (bareStageAtLAssignment (ordinalLCarrier ordinal) stage) ↔
      stage = stageLCarrier ordinal := by
  rw [satisfies_bareStageAtFormula,
    bareStageAt_ordinal_iff]

/-- Full-`L` existence and uniqueness, packaged in the form needed by
function-form Replacement. -/
theorem existsUnique_bareStageAt_ordinal (ordinal : Ordinal.{u}) :
    ∃! stage : LCarrier.{u},
      BareStageAt (ordinalLCarrier ordinal) stage := by
  refine ⟨stageLCarrier ordinal, bareStageAt_stageLCarrier ordinal, ?_⟩
  intro stage hstage
  exact bareStageAt_ordinal_eq_stageLCarrier ordinal hstage

/-! ## Raw semantics over a transitive set -/

/-- A bounded formula interpreted with all quantifiers restricted to a
transitive `ZFSet` agrees with ambient bounded satisfaction whenever every
free variable lies in that set. -/
theorem satisfiesIn_delta0_toFO_absolute
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (formula : Delta0Formula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) formula.toFO s ↔
      Delta0Formula.Satisfies Delta0Formula.ZFMem formula s := by
  let sU : Tuple (ZFCarrier U) n := fun i => ⟨s i, hs i⟩
  calc
    SatisfiesIn (U : Set ZFSet.{u}) formula.toFO s ↔
        SatisfiesIn (U : Set ZFSet.{u}) formula.toFO
          (fun i => (sU i).1) := by rfl
    _ ↔ FOFormula.Satisfies (zfCarrierMem U) formula.toFO sU :=
      (satisfies_subtype_iff_satisfiesIn
        (U : Set ZFSet.{u}) formula.toFO sU).symm
    _ ↔ Delta0Formula.Satisfies (zfCarrierMem U) formula sU :=
      Delta0Formula.satisfies_toFO (zfCarrierMem U) formula sU
    _ ↔ Delta0Formula.Satisfies Delta0Formula.ZFMem formula
          (Delta0Formula.val sU) :=
      Delta0Formula.satisfies_absolute hU formula sU
    _ ↔ Delta0Formula.Satisfies Delta0Formula.ZFMem formula s := by
      rfl

/-- Raw counterpart of `BareHistoryEntry`. -/
def BareHistoryEntryIn
    (history index stage : ZFSet.{u}) : Prop :=
  ZFSet.pair index stage ∈ history

/-- Raw entry assignment `(history,index,stage)`. -/
def bareHistoryEntryRawAssignment
    (history index stage : ZFSet.{u}) : Tuple ZFSet.{u} 3 :=
  ![history, index, stage]

/-- Pair-code equality is bounded-absolute over every transitive carrier
containing its three displayed arguments. -/
theorem satisfiesIn_kuratowskiPairEqAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (pair index stage : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair index stage).toFO s ↔
      s pair = ZFSet.pair (s index) (s stage) := by
  rw [satisfiesIn_delta0_toFO_absolute hU _ s hs,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

/-- Exact raw semantics of a pair-coded entry inside an arbitrary transitive
set.  The reverse direction needs no Pairing axiom: if the pair belongs to
`history` and `history ∈ U`, transitivity already puts the witness in `U`. -/
theorem satisfiesIn_bareHistoryEntryAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (history index stage : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (bareHistoryEntryAt history index stage) s ↔
      ZFSet.pair (s index) (s stage) ∈ s history := by
  simp only [bareHistoryEntryAt, SatisfiesIn]
  constructor
  · rintro ⟨entry, hentryU, hentry, hpair⟩
    change entry ∈ U at hentryU
    have hentry' : entry ∈ s history := by
      simpa only [snoc_last, snoc_castSucc] using hentry
    have hsSnoc : ∀ i, snoc s entry i ∈ U := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [snoc_last] using hentryU
      · simpa only [snoc_castSucc] using hs j
    have heq := (satisfiesIn_kuratowskiPairEqAt_iff hU
      (Fin.last n) index.castSucc stage.castSucc
      (snoc s entry) hsSnoc).mp hpair
    have heq' : entry = ZFSet.pair (s index) (s stage) := by
      simpa only [snoc_last, snoc_castSucc] using heq
    rw [heq'] at hentry'
    exact hentry'
  · intro hentry
    let entry := ZFSet.pair (s index) (s stage)
    have hentryU : entry ∈ U := hU.mem_trans hentry (hs history)
    refine ⟨entry, ?_, ?_, ?_⟩
    · exact hentryU
    · simpa only [snoc_last, snoc_castSucc] using hentry
    have hsSnoc : ∀ i, snoc s entry i ∈ U := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [snoc_last] using hentryU
      · simpa only [snoc_castSucc] using hs j
    apply (satisfiesIn_kuratowskiPairEqAt_iff hU
      (Fin.last n) index.castSucc stage.castSucc
      (snoc s entry) hsSnoc).mpr
    simp only [snoc_last, snoc_castSucc, entry]

/-- Three-coordinate raw entry semantics. -/
theorem satisfiesIn_bareHistoryEntryFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (history index stage : ZFSet.{u})
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryEntryFormula
        (bareHistoryEntryRawAssignment history index stage) ↔
      BareHistoryEntryIn history index stage := by
  rw [bareHistoryEntryFormula,
    satisfiesIn_bareHistoryEntryAt_iff hU]
  · rfl
  · intro i
    fin_cases i <;> assumption

/-- Raw local-state assignment with an arbitrary thirteen-coordinate prefix. -/
def bareHistoryStateRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc fixed history) index) stage

/-- The base formula has no hidden quantifiers: it literally identifies the
index and stage coordinates with coordinate `2` of the supplied prefix. -/
theorem satisfiesIn_bareHistoryBaseStateFormula_iff
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryBaseStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      index = fixed (2 : Fin 13) ∧
      stage = fixed (2 : Fin 13) := by
  change
    (bareHistoryStateRawAssignment fixed history index stage (14 : Fin 16) =
      bareHistoryStateRawAssignment fixed history index stage (2 : Fin 16) ∧
    bareHistoryStateRawAssignment fixed history index stage (15 : Fin 16) =
      bareHistoryStateRawAssignment fixed history index stage (2 : Fin 16))
      ↔ _
  change (index = fixed (2 : Fin 13) ∧
    stage = fixed (2 : Fin 13)) ↔ _
  rfl

private theorem satisfiesIn_bare_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_bare_biimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

private theorem satisfiesIn_bare_boundedEx_iff
    (M : Set ZFSet.{u}) {n : Nat} (i : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedEx i formula) s ↔
      ∃ x : ZFSet.{u}, x ∈ M ∧ x ∈ s i ∧
        SatisfiesIn M formula (snoc s x) := by
  simp [FOFormula.boundedEx, SatisfiesIn]

/-- Raw assignment for the relation-free limit clause. -/
def bareHistoryLimitRawAssignment
    (history index stage : ZFSet.{u}) : Tuple ZFSet.{u} 3 :=
  ![history, index, stage]

/-- First expansion of the limit formula.  This theorem deliberately leaves
the nested entry formula visible; the next theorem applies transitive
bounded absoluteness to identify it with pair membership. -/
theorem satisfiesIn_bareHistoryLimitStateFormula_components
    (U : Set ZFSet.{u}) (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryLimitStateFormula
        (bareHistoryLimitRawAssignment history index stage) ↔
      ∀ z : ZFSet.{u}, z ∈ U →
        (z ∈ stage ↔
          ∃ earlierIndex : ZFSet.{u},
            earlierIndex ∈ U ∧ earlierIndex ∈ index ∧
            ∃ earlierStage : ZFSet.{u},
              earlierStage ∈ U ∧
              SatisfiesIn U
                (bareHistoryEntryAt
                  (0 : Fin 6) (4 : Fin 6) (5 : Fin 6))
                ![history, index, stage, z,
                  earlierIndex, earlierStage] ∧
              z ∈ earlierStage) := by
  simp only [bareHistoryLimitStateFormula,
    satisfiesIn_bare_all_iff, satisfiesIn_bare_biimp_iff,
    satisfiesIn_bare_boundedEx_iff, SatisfiesIn,
    bareHistoryLimitRawAssignment]
  rfl

/-- The usual internally relativized limit-stage condition: every displayed
quantifier ranges over `U`, and entries are ordinary Kuratowski pairs. -/
def BareHistoryLimitStateIn (U : Set ZFSet.{u})
    (history index stage : ZFSet.{u}) : Prop :=
  ∀ z : ZFSet.{u}, z ∈ U →
    (z ∈ stage ↔
      ∃ earlierIndex : ZFSet.{u},
        earlierIndex ∈ U ∧ earlierIndex ∈ index ∧
        ∃ earlierStage : ZFSet.{u},
          earlierStage ∈ U ∧
          BareHistoryEntryIn history earlierIndex earlierStage ∧
          z ∈ earlierStage)

/-- Exact raw semantics of the limit clause over a transitive set. -/
theorem satisfiesIn_bareHistoryLimitStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (history index stage : ZFSet.{u})
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLimitStateFormula
        (bareHistoryLimitRawAssignment history index stage) ↔
      BareHistoryLimitStateIn (U : Set ZFSet.{u})
        history index stage := by
  rw [satisfiesIn_bareHistoryLimitStateFormula_components]
  constructor
  · intro h z hzU
    have hz := h z hzU
    constructor
    · intro hzStage
      rcases hz.mp hzStage with
        ⟨earlierIndex, hearlierIndexU, hearlierIndex,
          earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mp hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩

    · rintro ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      apply hz.mpr
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mpr hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩
  · intro h z hzU
    have hz := h z hzU
    constructor
    · intro hzStage
      rcases hz.mp hzStage with
        ⟨earlierIndex, hearlierIndexU, hearlierIndex,
          earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mpr hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩
    · rintro ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
      apply hz.mpr
      have hs : ∀ i,
          ![history, index, stage, z,
            earlierIndex, earlierStage] i ∈ U := by
        intro i
        fin_cases i <;> assumption
      have hentry := (satisfiesIn_bareHistoryEntryAt_iff hU
        (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)
        ![history, index, stage, z,
          earlierIndex, earlierStage] hs).mp hearlierEntry
      exact ⟨earlierIndex, hearlierIndexU, hearlierIndex,
        earlierStage, hearlierStageU, hentry, hzEarlier⟩

/-! ### The isolated successor obligation -/

/-- Raw assignment of the existing `godelDef` output formula, with an
arbitrary thirteen-coordinate evaluator prefix. -/
def bareGodelDefOutputRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (predecessorStage stage : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (tupleCons predecessorStage fixed) stage

/-- What the current object-language evaluator says internally.  This is
kept as a satisfaction statement rather than silently identified with the
ambient `godelDef`. -/
def BareGodelDefOutputIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (predecessorStage stage : ZFSet.{u}) : Prop :=
  SatisfiesIn U Godel.RudimentaryTerm.godelDefOutputFormula
    (bareGodelDefOutputRawAssignment fixed predecessorStage stage)

/-- The precise missing absoluteness obligation for successor steps.  Later
uses may assume this predicate only after proving it for the relevant
transitive stage; its name does not assert that the obligation already holds. -/
def BareGodelDefOutputCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  ∀ predecessorStage stage : ZFSet.{u},
    predecessorStage ∈ U → stage ∈ U →
      (BareGodelDefOutputIn (U : Set ZFSet.{u}) fixed
          predecessorStage stage ↔
        stage = Godel.godelDef predecessorStage)

/-- Raw successor-witness assignment. -/
def bareHistorySuccessorWitnessRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage predecessorIndex predecessorStage : ZFSet.{u}) :
    Tuple ZFSet.{u} 18 :=
  snoc (snoc (bareHistoryStateRawAssignment fixed history index stage)
    predecessorIndex) predecessorStage

private theorem bareHistorySuccessorDefRename_fixedRaw (i : Fin 13) :
    bareHistorySuccessorDefRename i.succ.castSucc =
      Fin.castLE (by decide) i := by
  unfold bareHistorySuccessorDefRename
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

private theorem comp_bareHistorySuccessorDefRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage predecessorIndex predecessorStage : ZFSet.{u}) :
    (fun i => bareHistorySuccessorWitnessRawAssignment fixed
      history index stage predecessorIndex predecessorStage
      (bareHistorySuccessorDefRename i)) =
      bareGodelDefOutputRawAssignment fixed predecessorStage stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · change predecessorStage = predecessorStage
      rfl
    · rw [bareHistorySuccessorDefRename_fixedRaw]
      rw [show Fin.castLE (by decide) i13 =
          i13.castSucc.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [bareHistorySuccessorWitnessRawAssignment,
        bareHistoryStateRawAssignment,
        bareGodelDefOutputRawAssignment, snoc_castSucc,
        tupleCons_succ]

/-- Raw bounded absoluteness of the von Neumann successor predicate. -/
theorem satisfiesIn_successorFOAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (successor predecessor : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt successor predecessor) s ↔
      s successor = insert (s predecessor) (s predecessor) := by
  rw [Delta0Formula.successorFOAt,
    satisfiesIn_delta0_toFO_absolute hU _ s hs,
    Delta0Formula.satisfies_successorAt]

/-- Exact internally relativized successor clause.  Notice that the final
conjunct remains `BareGodelDefOutputIn`; replacing it by ambient `godelDef`
requires `BareGodelDefOutputCorrectIn`. -/
def BareHistorySuccessorStateIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  ∃ predecessorIndex : ZFSet.{u}, predecessorIndex ∈ U ∧
    ∃ predecessorStage : ZFSet.{u}, predecessorStage ∈ U ∧
      index = insert predecessorIndex predecessorIndex ∧
      BareHistoryEntryIn history predecessorIndex predecessorStage ∧
      BareGodelDefOutputIn U fixed predecessorStage stage

/-- Exact raw semantics of the successor clause over a transitive set. -/
theorem satisfiesIn_bareHistorySuccessorStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        bareHistorySuccessorStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  simp only [bareHistorySuccessorStateFormula,
    BareHistorySuccessorStateIn, SatisfiesIn]
  apply exists_congr
  intro predecessorIndex
  apply and_congr_right
  intro hpredecessorIndexU
  change predecessorIndex ∈ U at hpredecessorIndexU
  apply exists_congr
  intro predecessorStage
  apply and_congr_right
  intro hpredecessorStageU
  change predecessorStage ∈ U at hpredecessorStageU
  let witness := bareHistorySuccessorWitnessRawAssignment fixed
    history index stage predecessorIndex predecessorStage
  have hwitness : ∀ i, witness i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun i16 => ?_) i
    · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
        snoc_last] using hpredecessorStageU
    · refine Fin.lastCases ?_ (fun i15 => ?_) i16
      · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
          snoc_castSucc, snoc_last] using hpredecessorIndexU
      · refine Fin.lastCases ?_ (fun i14 => ?_) i15
        · simpa only [witness, bareHistorySuccessorWitnessRawAssignment,
            bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
            hstage
        · refine Fin.lastCases ?_ (fun i13 => ?_) i14
          · simpa only [witness,
              bareHistorySuccessorWitnessRawAssignment,
              bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
              hindex
          · refine Fin.lastCases ?_ (fun i12 => ?_) i13
            · simpa only [witness,
                bareHistorySuccessorWitnessRawAssignment,
                bareHistoryStateRawAssignment, snoc_castSucc, snoc_last] using
                hhistory
            · simpa only [witness,
                bareHistorySuccessorWitnessRawAssignment,
                bareHistoryStateRawAssignment, snoc_castSucc] using hfixed i12
  change
    (SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt (14 : Fin 18) (16 : Fin 18))
        witness ∧
      SatisfiesIn (U : Set ZFSet.{u})
        (bareHistoryEntryAt
          (13 : Fin 18) (16 : Fin 18) (17 : Fin 18)) witness ∧
      SatisfiesIn (U : Set ZFSet.{u})
        (FOFormula.rename bareHistorySuccessorDefRename
          Godel.RudimentaryTerm.godelDefOutputFormula) witness) ↔ _
  rw [satisfiesIn_successorFOAt_iff hU _ _ witness hwitness,
    satisfiesIn_bareHistoryEntryAt_iff hU _ _ _ witness hwitness,
    satisfiesIn_rename,
    comp_bareHistorySuccessorDefRename_raw]
  rfl

/-! ### The complete raw local-state semantics -/

private theorem satisfiesIn_bare_disj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

/-- Raw semantics of the test that the displayed index is zero. -/
theorem satisfiesIn_bareHistoryIndexIsZeroFormula_iff
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    SatisfiesIn U bareHistoryIndexIsZeroFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      index = fixed (2 : Fin 13) := by
  change (index = fixed (2 : Fin 13)) ↔ _
  rfl

/-- Raw semantics of the test that the displayed index is a von Neumann
successor.  The predecessor witness is, exactly as in restricted
satisfaction, required to belong to `U`. -/
theorem satisfiesIn_bareHistoryIndexHasPredecessorFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        bareHistoryIndexHasPredecessorFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor := by
  simp only [bareHistoryIndexHasPredecessorFormula, SatisfiesIn]
  apply exists_congr
  intro predecessor
  apply and_congr_right
  intro hpredecessorU
  change predecessor ∈ U at hpredecessorU
  let witness := snoc
    (bareHistoryStateRawAssignment fixed history index stage) predecessor
  have hwitness : ∀ i, witness i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun i15 => ?_) i
    · simpa only [witness, snoc_last] using hpredecessorU
    · refine Fin.lastCases ?_ (fun i14 => ?_) i15
      · simpa only [witness, bareHistoryStateRawAssignment,
          snoc_castSucc, snoc_last] using hstage
      · refine Fin.lastCases ?_ (fun i13 => ?_) i14
        · simpa only [witness, bareHistoryStateRawAssignment,
            snoc_castSucc, snoc_last] using hindex
        · refine Fin.lastCases ?_ (fun i12 => ?_) i13
          · simpa only [witness, bareHistoryStateRawAssignment,
              snoc_castSucc, snoc_last] using hhistory
          · simpa only [witness, bareHistoryStateRawAssignment,
              snoc_castSucc] using hfixed i12
  change
    SatisfiesIn (U : Set ZFSet.{u})
        (Delta0Formula.successorFOAt (14 : Fin 17) (16 : Fin 17))
        witness ↔ _
  rw [satisfiesIn_successorFOAt_iff hU _ _ witness hwitness]
  rfl

private theorem comp_bareHistoryStateRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) :
    (fun i => bareHistoryStateRawAssignment fixed history index stage
      (bareHistoryStateRename i)) =
      bareHistoryLimitRawAssignment history index stage := by
  funext i
  fin_cases i <;> rfl

/-- The ordinary three-way recursion rule interpreted inside `U`:

* at zero, both the index and stage are the supplied empty-set parameter;
* at a successor, the preceding entry is present and the internally
  evaluated Goedel-definability formula yields the new stage;
* at a nonzero nonsuccessor, the stage is the union of earlier values, with
  every displayed quantifier restricted to `U`.

No ambient `godelDef` equality is asserted in this definition. -/
def BareHistoryLocalStateIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  (index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
  BareHistorySuccessorStateIn U fixed history index stage ∨
  ((index ≠ fixed (2 : Fin 13) ∧
      ¬ ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor) ∧
    BareHistoryLimitStateIn U history index stage)

/-- The usual ambient mathematical reading of the successor clause, while
the two witnesses are still required to lie in `U`. -/
def BareHistorySuccessorStateAmbientIn (U : Set ZFSet.{u})
    (history index stage : ZFSet.{u}) : Prop :=
  ∃ predecessorIndex : ZFSet.{u}, predecessorIndex ∈ U ∧
    ∃ predecessorStage : ZFSet.{u}, predecessorStage ∈ U ∧
      index = insert predecessorIndex predecessorIndex ∧
      BareHistoryEntryIn history predecessorIndex predecessorStage ∧
      stage = Godel.godelDef predecessorStage

/-- The isolated evaluator-correctness obligation is exactly what turns the
internal successor clause into its usual ambient mathematical reading. -/
theorem bareHistorySuccessorStateIn_iff_ambient
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) (hstage : stage ∈ U)
    (hcorrect : BareGodelDefOutputCorrectIn U fixed) :
    BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
        history index stage ↔
      BareHistorySuccessorStateAmbientIn (U : Set ZFSet.{u})
        history index stage := by
  simp only [BareHistorySuccessorStateIn,
    BareHistorySuccessorStateAmbientIn]
  apply exists_congr
  intro predecessorIndex
  apply and_congr_right
  intro _hpredecessorIndexU
  apply exists_congr
  intro predecessorStage
  apply and_congr_right
  intro hpredecessorStageU
  change predecessorStage ∈ U at hpredecessorStageU
  rw [hcorrect predecessorStage stage hpredecessorStageU hstage]

/-- The standard ambient three-way recursion, with witnesses restricted to
`U` but the successor output identified with the actual `godelDef`. -/
def BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) : Prop :=
  (index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
  BareHistorySuccessorStateAmbientIn U history index stage ∨
  ((index ≠ fixed (2 : Fin 13) ∧
      ¬ ∃ predecessor : ZFSet.{u}, predecessor ∈ U ∧
        index = insert predecessor predecessor) ∧
    BareHistoryLimitStateIn U history index stage)

/-- Under the explicit evaluator-correctness hypothesis, the internally
relativized local state is the standard ambient recursion state. -/
theorem bareHistoryLocalStateIn_iff_ambient
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u}) (hstage : stage ∈ U)
    (hcorrect : BareGodelDefOutputCorrectIn U fixed) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
        history index stage ↔
      BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  simp only [BareHistoryLocalStateIn, BareHistoryLocalStateAmbientIn]
  rw [bareHistorySuccessorStateIn_iff_ambient fixed history index stage
    hstage hcorrect]

/-- Exact restricted semantics of the complete local recursion formula. -/
theorem satisfiesIn_bareHistoryLocalStateFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLocalStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  rw [bareHistoryLocalStateFormula, satisfiesIn_bare_disj_iff,
    satisfiesIn_bareHistoryBaseStateFormula_iff,
    satisfiesIn_bare_disj_iff,
    satisfiesIn_bareHistorySuccessorStateFormula_iff hU fixed
      history index stage hfixed hhistory hindex hstage]
  change
    ((index = fixed (2 : Fin 13) ∧ stage = fixed (2 : Fin 13)) ∨
      BareHistorySuccessorStateIn (U : Set ZFSet.{u}) fixed
          history index stage ∨
      ((¬ SatisfiesIn (U : Set ZFSet.{u})
            bareHistoryIndexIsZeroFormula
            (bareHistoryStateRawAssignment fixed history index stage) ∧
          ¬ SatisfiesIn (U : Set ZFSet.{u})
            bareHistoryIndexHasPredecessorFormula
            (bareHistoryStateRawAssignment fixed history index stage)) ∧
        SatisfiesIn (U : Set ZFSet.{u})
          (FOFormula.rename bareHistoryStateRename
            bareHistoryLimitStateFormula)
          (bareHistoryStateRawAssignment fixed history index stage))) ↔ _
  rw [satisfiesIn_bareHistoryIndexIsZeroFormula_iff,
    satisfiesIn_bareHistoryIndexHasPredecessorFormula_iff hU fixed
      history index stage hfixed hhistory hindex hstage,
    satisfiesIn_rename, comp_bareHistoryStateRename_raw,
    satisfiesIn_bareHistoryLimitStateFormula_iff hU
      history index stage hhistory hindex hstage]
  rfl

/-- Formula semantics in its usual ambient-recursion form.  The evaluator
correctness hypothesis is intentionally visible in the theorem type. -/
theorem satisfiesIn_bareHistoryLocalStateFormula_iff_ambient
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hindex : index ∈ U)
    (hstage : stage ∈ U)
    (hcorrect : BareGodelDefOutputCorrectIn U fixed) :
    SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLocalStateFormula
        (bareHistoryStateRawAssignment fixed history index stage) ↔
      BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u}) fixed
        history index stage := by
  rw [satisfiesIn_bareHistoryLocalStateFormula_iff hU fixed
      history index stage hfixed hhistory hindex hstage,
    bareHistoryLocalStateIn_iff_ambient fixed history index stage
      hstage hcorrect]

/-! ### Raw valid histories -/

private theorem satisfiesIn_bare_imp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s ↔
      (SatisfiesIn M left s → SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_bare_disj_iff, SatisfiesIn]
  tauto

private theorem snoc_mem_of_all_mem
    {U : ZFSet.{u}} {n : Nat} (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ U) (x : ZFSet.{u}) (hx : x ∈ U) :
    ∀ i, snoc s x i ∈ U := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [snoc_last] using hx
  · simpa only [snoc_castSucc] using hs j

/-- Raw layout `(fixed13,history,bound)`. -/
def bareValidStageHistoryRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (history bound : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (snoc fixed history) bound

/-- Raw layout after adjoining the index selected by the outer universal
quantifier. -/
def bareValidStageHistoryIndexRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (history bound index : ZFSet.{u}) :
    Tuple ZFSet.{u} 16 :=
  snoc (bareValidStageHistoryRawAssignment fixed history bound) index

/-- Raw layout after adjoining the stage selected by the index body. -/
def bareValidStageHistoryStageRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (bareValidStageHistoryIndexRawAssignment fixed history bound index)
    stage

private theorem bareValidStageHistoryRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U) :
    ∀ i, bareValidStageHistoryRawAssignment fixed history bound i ∈ U := by
  exact snoc_mem_of_all_mem _
    (snoc_mem_of_all_mem fixed hfixed history hhistory) bound hbound

private theorem bareValidStageHistoryIndexRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) :
    ∀ i,
      bareValidStageHistoryIndexRawAssignment fixed history bound index i ∈ U := by
  exact snoc_mem_of_all_mem _
    (bareValidStageHistoryRawAssignment_mem fixed history bound
      hfixed hhistory hbound) index hindex

private theorem bareValidStageHistoryStageRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i,
      bareValidStageHistoryStageRawAssignment fixed history bound index stage i ∈ U := by
  exact snoc_mem_of_all_mem _
    (bareValidStageHistoryIndexRawAssignment_mem fixed history bound index
      hfixed hhistory hbound hindex) stage hstage

/-- Direct syntactic expansion of the body at one selected index. -/
theorem satisfiesIn_bareValidStageHistoryIndexBody_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u}) :
    SatisfiesIn U bareValidStageHistoryIndexBody
        (bareValidStageHistoryIndexRawAssignment fixed history bound index) ↔
      ∃ stage : ZFSet.{u}, stage ∈ U ∧
        SatisfiesIn U
          (bareHistoryEntryAt
            (13 : Fin 17) (15 : Fin 17) (16 : Fin 17))
          (bareValidStageHistoryStageRawAssignment fixed history bound
            index stage) ∧
        ((∀ otherStage : ZFSet.{u}, otherStage ∈ U →
            SatisfiesIn U
              (bareHistoryEntryAt
                (13 : Fin 18) (15 : Fin 18) (17 : Fin 18))
              (snoc (bareValidStageHistoryStageRawAssignment fixed history
                bound index stage) otherStage) →
            otherStage = stage) ∧
          SatisfiesIn U
            (FOFormula.rename bareValidHistoryLocalRename
              bareHistoryLocalStateFormula)
            (bareValidStageHistoryStageRawAssignment fixed history bound
              index stage)) := by
  simp only [bareValidStageHistoryIndexBody, SatisfiesIn,
    satisfiesIn_bare_all_iff, satisfiesIn_bare_imp_iff,
    bareValidStageHistoryIndexRawAssignment,
    bareValidStageHistoryStageRawAssignment]
  rfl

private theorem comp_bareValidHistoryLocalRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index stage : ZFSet.{u}) :
    (fun i =>
      bareValidStageHistoryStageRawAssignment fixed history bound index stage
        (bareValidHistoryLocalRename i)) =
      bareHistoryStateRawAssignment fixed history index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · change stage = stage
    rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · change index = index
      rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · change history = history
        rfl
      · rw [bareValidHistoryLocalRename_fixed]
        rw [show Fin.castLE (by decide) i13 =
            i13.castSucc.castSucc.castSucc.castSucc by
          apply Fin.ext
          rfl]
        simp only [bareValidStageHistoryStageRawAssignment,
          bareValidStageHistoryIndexRawAssignment,
          bareValidStageHistoryRawAssignment,
          bareHistoryStateRawAssignment, snoc_castSucc]

/-- The exact internally relativized condition imposed at one selected
index of a bare history. -/
def BareValidStageHistoryIndexIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history index : ZFSet.{u}) : Prop :=
  ∃ stage : ZFSet.{u}, stage ∈ U ∧
    BareHistoryEntryIn history index stage ∧
    (∀ otherStage : ZFSet.{u}, otherStage ∈ U →
      BareHistoryEntryIn history index otherStage → otherStage = stage) ∧
    BareHistoryLocalStateIn U fixed history index stage

/-- Exact raw semantics of the validity body at one selected index. -/
theorem satisfiesIn_bareValidStageHistoryIndexBody_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history bound index : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U)
    (hindex : index ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryIndexBody
        (bareValidStageHistoryIndexRawAssignment fixed history bound index) ↔
      BareValidStageHistoryIndexIn (U : Set ZFSet.{u}) fixed
        history index := by
  rw [satisfiesIn_bareValidStageHistoryIndexBody_components]
  constructor
  · rintro ⟨stage, hstageU, hentry, hunique, hlocal⟩
    change stage ∈ U at hstageU
    have hstageAssignment :=
      bareValidStageHistoryStageRawAssignment_mem fixed history bound
        index stage hfixed hhistory hbound hindex hstageU
    have hentry' := (satisfiesIn_bareHistoryEntryAt_iff hU
      (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)
      (bareValidStageHistoryStageRawAssignment fixed history bound
        index stage) hstageAssignment).mp hentry
    have hlocal' :
        SatisfiesIn (U : Set ZFSet.{u}) bareHistoryLocalStateFormula
          (bareHistoryStateRawAssignment fixed history index stage) := by
      rw [satisfiesIn_rename,
        comp_bareValidHistoryLocalRename_raw] at hlocal
      exact hlocal
    refine ⟨stage, ?_, hentry', ?_, ?_⟩
    · exact hstageU
    · intro otherStage hotherStageU hotherEntry
      change otherStage ∈ U at hotherStageU
      apply hunique otherStage
      · exact hotherStageU
      have hotherAssignment := snoc_mem_of_all_mem _ hstageAssignment
        otherStage hotherStageU
      exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 18) (15 : Fin 18) (17 : Fin 18)
        (snoc (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) otherStage) hotherAssignment).mpr hotherEntry
    · exact (satisfiesIn_bareHistoryLocalStateFormula_iff hU fixed
        history index stage hfixed hhistory hindex hstageU).mp hlocal'
  · rintro ⟨stage, hstageU, hentry, hunique, hlocal⟩
    change stage ∈ U at hstageU
    have hstageAssignment :=
      bareValidStageHistoryStageRawAssignment_mem fixed history bound
        index stage hfixed hhistory hbound hindex hstageU
    refine ⟨stage, ?_, ?_, ?_, ?_⟩
    · exact hstageU
    · exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)
        (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) hstageAssignment).mpr hentry
    · intro otherStage hotherStageU hotherEntry
      change otherStage ∈ U at hotherStageU
      have hotherAssignment := snoc_mem_of_all_mem _ hstageAssignment
        otherStage hotherStageU
      have hotherEntry' := (satisfiesIn_bareHistoryEntryAt_iff hU
        (13 : Fin 18) (15 : Fin 18) (17 : Fin 18)
        (snoc (bareValidStageHistoryStageRawAssignment fixed history bound
          index stage) otherStage) hotherAssignment).mp hotherEntry
      apply hunique otherStage
      · exact hotherStageU
      · exact hotherEntry'
    · rw [satisfiesIn_rename,
        comp_bareValidHistoryLocalRename_raw]
      exact (satisfiesIn_bareHistoryLocalStateFormula_iff hU fixed
        history index stage hfixed hhistory hindex hstageU).mpr hlocal

/-- Direct expansion of the outer bounded-totality formula.  The outer
universal quantifier ranges over `U`; the displayed disjunction is the
von Neumann condition `index <= bound`. -/
theorem satisfiesIn_bareValidStageHistoryFormula_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u}) :
    SatisfiesIn U bareValidStageHistoryFormula
        (bareValidStageHistoryRawAssignment fixed history bound) ↔
      ∀ index : ZFSet.{u}, index ∈ U →
        (index ∈ bound ∨ index = bound) →
          SatisfiesIn U bareValidStageHistoryIndexBody
            (bareValidStageHistoryIndexRawAssignment fixed history bound
              index) := by
  simp only [bareValidStageHistoryFormula, satisfiesIn_bare_all_iff,
    satisfiesIn_bare_imp_iff, satisfiesIn_bare_disj_iff, SatisfiesIn,
    bareValidStageHistoryIndexRawAssignment]
  rfl

/-- A raw pair-coded history is total, stage-functional, and locally correct
through `bound`, with every quantified index and stage restricted to `U`.
Members of `history` that are not relevant pair entries remain harmless, just
as in `bareValidStageHistoryFormula`. -/
def BareValidStageHistoryIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u}) : Prop :=
  ∀ index : ZFSet.{u}, index ∈ U →
    (index ∈ bound ∨ index = bound) →
      BareValidStageHistoryIndexIn U fixed history index

/-- Exact raw semantics of a valid bare history over a transitive set. -/
theorem satisfiesIn_bareValidStageHistoryFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (history bound : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hhistory : history ∈ U) (hbound : bound ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryFormula
        (bareValidStageHistoryRawAssignment fixed history bound) ↔
      BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
        history bound := by
  rw [satisfiesIn_bareValidStageHistoryFormula_components]
  constructor
  · intro h index hindexU hindexBound
    change index ∈ U at hindexU
    exact (satisfiesIn_bareValidStageHistoryIndexBody_iff hU fixed
      history bound index hfixed hhistory hbound hindexU).mp
        (h index hindexU hindexBound)
  · intro h index hindexU hindexBound
    change index ∈ U at hindexU
    exact (satisfiesIn_bareValidStageHistoryIndexBody_iff hU fixed
      history bound index hfixed hhistory hbound hindexU).mpr
        (h index hindexU hindexBound)

/-! ### Raw history-independent stage output -/

/-- Raw layout `(fixed13,index,stage)`. -/
def bareStageAtRawAssignment
    (fixed : Tuple ZFSet.{u} 13) (index stage : ZFSet.{u}) :
    Tuple ZFSet.{u} 15 :=
  snoc (snoc fixed index) stage

/-- Raw layout after adjoining the hidden history witness. -/
def bareStageAtHistoryRawAssignment
    (fixed : Tuple ZFSet.{u} 13)
    (index stage history : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (bareStageAtRawAssignment fixed index stage) history

private theorem bareStageAtRawAssignment_mem
    {U : ZFSet.{u}} (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    ∀ i, bareStageAtRawAssignment fixed index stage i ∈ U := by
  exact snoc_mem_of_all_mem _
    (snoc_mem_of_all_mem fixed hfixed index hindex) stage hstage

private theorem comp_bareStageAtValidHistoryRename_raw
    (fixed : Tuple ZFSet.{u} 13)
    (index stage history : ZFSet.{u}) :
    (fun i => bareStageAtHistoryRawAssignment fixed index stage history
      (bareStageAtValidHistoryRename i)) =
      bareValidStageHistoryRawAssignment fixed history index := by
  funext i
  fin_cases i <;> rfl

/-- Direct expansion of the history-independent stage-output formula. -/
theorem satisfiesIn_bareStageAtFormula_components
    (U : Set ZFSet.{u}) (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u}) :
    SatisfiesIn U bareStageAtFormula
        (bareStageAtRawAssignment fixed index stage) ↔
      ∃ history : ZFSet.{u}, history ∈ U ∧
        SatisfiesIn U
          (FOFormula.rename bareStageAtValidHistoryRename
            bareValidStageHistoryFormula)
          (bareStageAtHistoryRawAssignment fixed index stage history) ∧
        SatisfiesIn U
          (bareHistoryEntryAt
            (15 : Fin 16) (13 : Fin 16) (14 : Fin 16))
          (bareStageAtHistoryRawAssignment fixed index stage history) := by
  simp only [bareStageAtFormula, SatisfiesIn,
    bareStageAtHistoryRawAssignment]

/-- Inside `U`, `stage` is the output at `index` when some history in `U` is
valid through `index` and contains the top pair `(index,stage)`. -/
def BareStageAtIn (U : Set ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u}) : Prop :=
  ∃ history : ZFSet.{u}, history ∈ U ∧
    BareValidStageHistoryIn U fixed history index ∧
    BareHistoryEntryIn history index stage

/-- Exact raw semantics of the history-independent stage-output formula over
a transitive set.  This theorem identifies the syntax only with the
internally relativized recursion; it does not assume successor absoluteness. -/
theorem satisfiesIn_bareStageAtFormula_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (index stage : ZFSet.{u})
    (hfixed : ∀ i, fixed i ∈ U)
    (hindex : index ∈ U) (hstage : stage ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (bareStageAtRawAssignment fixed index stage) ↔
      BareStageAtIn (U : Set ZFSet.{u}) fixed index stage := by
  rw [satisfiesIn_bareStageAtFormula_components]
  constructor
  · rintro ⟨history, hhistoryU, hvalid, hentry⟩
    change history ∈ U at hhistoryU
    have hbaseAssignment := bareStageAtRawAssignment_mem fixed index stage
      hfixed hindex hstage
    have hhistoryAssignment := snoc_mem_of_all_mem _ hbaseAssignment
      history hhistoryU
    have hvalid' :
        SatisfiesIn (U : Set ZFSet.{u}) bareValidStageHistoryFormula
          (bareValidStageHistoryRawAssignment fixed history index) := by
      rw [satisfiesIn_rename,
        comp_bareStageAtValidHistoryRename_raw] at hvalid
      exact hvalid
    have hentry' := (satisfiesIn_bareHistoryEntryAt_iff hU
      (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)
      (bareStageAtHistoryRawAssignment fixed index stage history)
      hhistoryAssignment).mp hentry
    refine ⟨history, hhistoryU, ?_, hentry'⟩
    exact (satisfiesIn_bareValidStageHistoryFormula_iff hU fixed
      history index hfixed hhistoryU hindex).mp hvalid'
  · rintro ⟨history, hhistoryU, hvalid, hentry⟩
    change history ∈ U at hhistoryU
    have hbaseAssignment := bareStageAtRawAssignment_mem fixed index stage
      hfixed hindex hstage
    have hhistoryAssignment := snoc_mem_of_all_mem _ hbaseAssignment
      history hhistoryU
    refine ⟨history, ?_, ?_, ?_⟩
    · exact hhistoryU
    · rw [satisfiesIn_rename,
        comp_bareStageAtValidHistoryRename_raw]
      exact (satisfiesIn_bareValidStageHistoryFormula_iff hU fixed
        history index hfixed hhistoryU hindex).mpr hvalid
    · exact (satisfiesIn_bareHistoryEntryAt_iff hU
        (15 : Fin 16) (13 : Fin 16) (14 : Fin 16)
        (bareStageAtHistoryRawAssignment fixed index stage history)
        hhistoryAssignment).mpr hentry

/-! ### Soundness of internal ordinal outputs -/

/-- Raw canonical evaluator parameters. -/
def stageHistoryFixedParametersRaw : Tuple ZFSet.{u} 13 :=
  fun i => (stageHistoryFixedParameters.{u} i).1

@[simp]
theorem stageHistoryFixedParametersRaw_empty :
    stageHistoryFixedParametersRaw (2 : Fin 13) = (∅ : ZFSet.{u}) := by
  change (stageHistoryFixedParameters (2 : Fin 13)).1 = (∅ : ZFSet.{u})
  rw [stageHistoryFixedParameters_empty]
  rfl

/-- Restrict an internally valid history from a canonical ordinal bound to
any smaller canonical ordinal bound. -/
theorem BareValidStageHistoryIn.restrictOrdinal
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history : ZFSet.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : BareValidStageHistoryIn U fixed history beta.toZFSet)
    (halpha : alpha ≤ beta) :
    BareValidStageHistoryIn U fixed history alpha.toZFSet := by
  intro index hindexU hindex
  apply hvalid index hindexU
  rcases hindex with hindex | rfl
  · left
    exact Ordinal.toZFSet_monotone halpha hindex
  · rcases halpha.eq_or_lt with rfl | halpha
    · exact Or.inr rfl
    · exact Or.inl (Ordinal.toZFSet_mem_toZFSet_iff.mpr halpha)

/-- Reusing the same internal history and one of its entries gives a stage
witness at every earlier canonical index. -/
theorem bareStageAtIn_of_validHistory
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history index stage : ZFSet.{u}} {alpha beta : Ordinal.{u}}
    (hhistory : history ∈ U)
    (hindex : index = alpha.toZFSet) (halpha : alpha ≤ beta)
    (hvalid : BareValidStageHistoryIn U fixed history beta.toZFSet)
    (hentry : BareHistoryEntryIn history index stage) :
    BareStageAtIn U fixed index stage := by
  subst index
  exact ⟨history, hhistory, hvalid.restrictOrdinal halpha, hentry⟩

/-- At its bound, internal validity transfers the local recursion rule to any
displayed entry at that bound. -/
theorem BareValidStageHistoryIn.localState_of_entry
    {U : Set ZFSet.{u}} {fixed : Tuple ZFSet.{u} 13}
    {history bound stage : ZFSet.{u}}
    (hvalid : BareValidStageHistoryIn U fixed history bound)
    (hboundU : bound ∈ U) (hstageU : stage ∈ U)
    (hentry : BareHistoryEntryIn history bound stage) :
    BareHistoryLocalStateIn U fixed history bound stage := by
  rcases hvalid bound hboundU (Or.inr rfl) with
    ⟨chosenStage, _hchosenStageU, _hchosenEntry, hunique, hlocal⟩
  have hstage := hunique stage hstageU hentry
  simpa only [hstage] using hlocal

private theorem empty_ne_insert_self_raw (predecessor : ZFSet.{u}) :
    ¬ (∅ : ZFSet.{u}) = insert predecessor predecessor := by
  intro h
  have hmem : predecessor ∈ (∅ : ZFSet.{u}) := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact ZFSet.notMem_empty predecessor hmem

/-- A canonical successor ordinal code has exactly its canonical predecessor,
even when the proposed predecessor is an arbitrary raw `ZFSet`. -/
theorem ordinalToZFSet_successor_predecessor_iff
    (alpha : Ordinal.{u}) (predecessor : ZFSet.{u}) :
    (Order.succ alpha).toZFSet = insert predecessor predecessor ↔
      predecessor = alpha.toZFSet := by
  constructor
  · intro h
    apply insert_self_injective
    rw [← h, Order.succ_eq_add_one]
    exact Ordinal.toZFSet_add_one alpha
  · rintro rfl
    rw [Order.succ_eq_add_one]
    exact Ordinal.toZFSet_add_one alpha

/-- A nonzero limit ordinal code is not the von Neumann successor of any raw
set. -/
theorem ordinalToZFSet_limit_no_predecessor
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    ¬ ∃ predecessor : ZFSet.{u},
      limit.toZFSet = insert predecessor predecessor := by
  rintro ⟨predecessor, hsuccessor⟩
  have hpredecessorMem : predecessor ∈ limit.toZFSet := by
    rw [hsuccessor]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases Ordinal.mem_toZFSet_iff.mp hpredecessorMem with
    ⟨beta, _hbeta, hbetaCode⟩
  subst predecessor
  have hcodes : limit.toZFSet = (Order.succ beta).toZFSet := by
    calc
      limit.toZFSet = insert beta.toZFSet beta.toZFSet := hsuccessor
      _ = (Order.succ beta).toZFSet :=
        (ordinalToZFSet_successor_predecessor_iff beta beta.toZFSet).mpr rfl |>.symm
  have hlimit : limit = Order.succ beta :=
    Ordinal.toZFSet_injective hcodes
  exact hl.succ_ne beta hlimit.symm

/-- Soundness of an internally computed ordinal stage in any transitive
carrier.  The hypotheses say exactly that the zero parameter is the actual
empty set and that the internal successor evaluator is correct.  No history
existence, reflection, or elementarity assumption is used. -/
theorem bareStageAtIn_ordinal_sound_of_transitive
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) :
    ∀ {stage : ZFSet.{u}},
      ordinal.toZFSet ∈ U → stage ∈ U →
      BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet stage →
        stage = LStageZF ordinal := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          (0 : Ordinal.{u}).toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · calc
          stage = fixed (2 : Fin 13) := hbase.2
          _ = (∅ : ZFSet.{u}) := hempty
          _ = LStageZF (0 : Ordinal.{u}) := LStageZF_zero.symm
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _hstage⟩
        have himpossible :
            (∅ : ZFSet.{u}) =
              insert predecessorIndex predecessorIndex := by
          simpa only [Ordinal.toZFSet_zero] using hpredecessor
        exact (empty_ne_insert_self_raw predecessorIndex himpossible).elim
      · have hzero :
            (0 : Ordinal.{u}).toZFSet = fixed (2 : Fin 13) := by
          rw [Ordinal.toZFSet_zero, hempty]
        exact (hlimit.1.1 hzero).elim
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          (Order.succ alpha).toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · have hcodes :
            (Order.succ alpha).toZFSet =
              (0 : Ordinal.{u}).toZFSet := by
          calc
            (Order.succ alpha).toZFSet = fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : Order.succ alpha = 0 :=
          Ordinal.toZFSet_injective hcodes
        exact (Order.succ_ne_bot alpha hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, hpredecessorIndexU,
            predecessorStage, hpredecessorStageU,
            hpredecessor, hpredecessorEntry, hstage⟩
        change predecessorIndex ∈ U at hpredecessorIndexU
        change predecessorStage ∈ U at hpredecessorStageU
        have hpredecessorIndex :
            predecessorIndex = alpha.toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            alpha predecessorIndex).mp hpredecessor
        subst predecessorIndex
        have hpredecessorAt :
            BareStageAtIn (U : Set ZFSet.{u}) fixed
              alpha.toZFSet predecessorStage :=
          bareStageAtIn_of_validHistory hhistoryU rfl
            (Order.le_succ alpha) hvalid hpredecessorEntry
        have hpredecessorStage :=
          ih hpredecessorIndexU hpredecessorStageU hpredecessorAt
        calc
          stage = Godel.godelDef predecessorStage := hstage
          _ = Godel.godelDef (LStageZF alpha) := by rw [hpredecessorStage]
          _ = Constructible.DefZF (LStageZF alpha) :=
            (Godel.DefZF_eq_godelDef
              (LStageZF_isTransitive alpha)).symm
          _ = LStageZF (Order.succ alpha) := (LStageZF_succ alpha).symm
      · have hpredecessorMem :
            alpha.toZFSet ∈ (Order.succ alpha).toZFSet :=
          Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ alpha)
        have hpredecessorU : alpha.toZFSet ∈ U :=
          hU.mem_trans hpredecessorMem hindexU
        have hpredecessor :
            (Order.succ alpha).toZFSet =
              insert alpha.toZFSet alpha.toZFSet :=
          (ordinalToZFSet_successor_predecessor_iff
            alpha alpha.toZFSet).mpr rfl
        exact (hlimit.1.2
          ⟨alpha.toZFSet, hpredecessorU, hpredecessor⟩).elim
  | limit limit hl ih =>
      intro stage hindexU hstageU hstageAt
      rcases hstageAt with ⟨history, hhistoryU, hvalid, hentry⟩
      have hlocal := hvalid.localState_of_entry hindexU hstageU hentry
      have hlocalAmbient :=
        (bareHistoryLocalStateIn_iff_ambient fixed history
          limit.toZFSet stage hstageU hcorrect).mp hlocal
      rcases hlocalAmbient with hbase | hsuccessor | hlimit
      · have hcodes : limit.toZFSet = (0 : Ordinal.{u}).toZFSet := by
          calc
            limit.toZFSet = fixed (2 : Fin 13) := hbase.1
            _ = (∅ : ZFSet.{u}) := hempty
            _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
        have hordinal : limit = 0 := Ordinal.toZFSet_injective hcodes
        exact (hl.ne_bot hordinal).elim
      · rcases hsuccessor with
          ⟨predecessorIndex, _hpredecessorIndexU,
            _predecessorStage, _hpredecessorStageU,
            hpredecessor, _hentry, _hstage⟩
        exact (ordinalToZFSet_limit_no_predecessor hl
          ⟨predecessorIndex, hpredecessor⟩).elim
      · apply ZFSet.ext
        intro z
        constructor
        · intro hz
          have hzU : z ∈ U := hU.mem_trans hz hstageU
          rcases (hlimit.2 z hzU).mp hz with
            ⟨earlierIndex, hearlierIndexU, hearlierIndex,
              earlierStage, hearlierStageU, hearlierEntry, hzEarlier⟩
          change earlierIndex ∈ U at hearlierIndexU
          change earlierStage ∈ U at hearlierStageU
          rcases Ordinal.mem_toZFSet_iff.mp hearlierIndex with
            ⟨earlierOrdinal, hearlierOrdinal, hcode⟩
          have hearlierIndexEq :
              earlierIndex = earlierOrdinal.toZFSet := hcode.symm
          subst earlierIndex
          have hearlierAt :
              BareStageAtIn (U : Set ZFSet.{u}) fixed
                earlierOrdinal.toZFSet earlierStage :=
            bareStageAtIn_of_validHistory hhistoryU rfl
              hearlierOrdinal.le hvalid hearlierEntry
          have hearlierStage := ih earlierOrdinal hearlierOrdinal
            hearlierIndexU hearlierStageU hearlierAt
          apply (mem_LStageZF_limit_iff hl).mpr
          refine ⟨earlierOrdinal, hearlierOrdinal, ?_⟩
          simpa only [hearlierStage] using hzEarlier
        · intro hz
          rcases (mem_LStageZF_limit_iff hl).mp hz with
            ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
          have hearlierIndex :
              earlierOrdinal.toZFSet ∈ limit.toZFSet :=
            Ordinal.toZFSet_mem_toZFSet_iff.mpr hearlierOrdinal
          have hearlierIndexU : earlierOrdinal.toZFSet ∈ U :=
            hU.mem_trans hearlierIndex hindexU
          rcases hvalid earlierOrdinal.toZFSet hearlierIndexU
              (Or.inl hearlierIndex) with
            ⟨earlierStage, hearlierStageU, hearlierEntry,
              _hunique, _hlocal⟩
          change earlierStage ∈ U at hearlierStageU
          have hearlierAt :
              BareStageAtIn (U : Set ZFSet.{u}) fixed
                earlierOrdinal.toZFSet earlierStage :=
            bareStageAtIn_of_validHistory hhistoryU rfl
              hearlierOrdinal.le hvalid hearlierEntry
          have hearlierStageEq := ih earlierOrdinal hearlierOrdinal
            hearlierIndexU hearlierStageU hearlierAt
          have hzEarlierStage : z ∈ earlierStage := by
            simpa only [hearlierStageEq] using hzEarlier
          have hzU : z ∈ U :=
            hU.mem_trans hzEarlierStage hearlierStageU
          apply (hlimit.2 z hzU).mpr
          exact ⟨earlierOrdinal.toZFSet, hearlierIndexU, hearlierIndex,
            earlierStage, hearlierStageU, hearlierEntry, hzEarlierStage⟩

/-- The requested specialization to a constructible level and the canonical
fixed evaluator prefix. -/
theorem bareStageAtIn_ordinal_eq_LStageZF
    (theta ordinal : Ordinal.{u}) {stage : ZFSet.{u}}
    (hcorrect : BareGodelDefOutputCorrectIn (LStageZF theta)
      stageHistoryFixedParametersRaw)
    (hindex : ordinal.toZFSet ∈ LStageZF theta)
    (hstage : stage ∈ LStageZF theta)
    (hstageAt : BareStageAtIn (LStageZF theta : Set ZFSet.{u})
      stageHistoryFixedParametersRaw ordinal.toZFSet stage) :
    stage = LStageZF ordinal :=
  bareStageAtIn_ordinal_sound_of_transitive
    (LStageZF_isTransitive theta) stageHistoryFixedParametersRaw
    stageHistoryFixedParametersRaw_empty hcorrect ordinal
    hindex hstage hstageAt

end

end Constructible.Model
