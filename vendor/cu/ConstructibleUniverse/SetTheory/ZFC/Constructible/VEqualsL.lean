/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryRecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Infinity

/-!
# The constructible universe satisfies an evaluator-coded `V = L` sentence

This file internalizes the constructible hierarchy in the membership structure
carried by `L`.  The constants used by the stage-history evaluator are first
characterized without parameters.  The resulting unary formula says that its
argument belongs to a stage produced by a valid internal history.

The main comparison theorem identifies that internal hierarchy, externalized
back to `ZFSet`, with the original class `L`. The final sentence is therefore
proved to express this property for `LCarrier`. This file does not assert the
separate, stronger adequacy theorem that the same evaluator-coded sentence is
equivalent to an independently defined internal constructible universe in
every arbitrary ZFC model.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Parameter-free canonical constants -/

/-- `s i` has no members. -/
def emptySetAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

@[simp]
theorem satisfies_emptySetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (emptySetAt i) s <->
      s i = emptyLCarrier := by
  simp only [emptySetAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact (h z hz).elim
    · intro hz
      exact (not_mem_emptyLCarrier z hz).elim
  · intro h z hz
    rw [h] at hz
    exact not_mem_emptyLCarrier z hz

/-- The von Neumann successor of `x`, packaged as an element of `L`. -/
def successorLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  ⟨insert x.1 x.1, by
    rw [ZFSet.insert_eq]
    exact union_mem_L (singleton_mem_L x.2) x.2⟩

@[simp]
theorem successorLCarrier_val (x : LCarrier.{u}) :
    (successorLCarrier x).1 = insert x.1 x.1 :=
  rfl

@[simp]
theorem successorLCarrier_ordinalLCarrier (alpha : Ordinal.{u}) :
    successorLCarrier (ordinalLCarrier alpha) =
      ordinalLCarrier (Order.succ alpha) := by
  rw [Order.succ_eq_add_one]
  apply Subtype.ext
  simp only [successorLCarrier_val, ordinalLCarrier_val,
    Ordinal.toZFSet_add_one]

@[simp]
theorem successorLCarrier_natOrdinal (n : Nat) :
    successorLCarrier (ordinalLCarrier (n : Ordinal.{u})) =
      ordinalLCarrier ((n + 1 : Nat) : Ordinal.{u}) := by
  simpa only [Nat.cast_add, Nat.cast_one, Order.succ_eq_add_one] using
    successorLCarrier_ordinalLCarrier (n : Ordinal.{u})

/-- `s succ` is the von Neumann successor of `s index`. -/
def successorSetAt {n : Nat} (succ index : Fin n) : FOFormula n :=
  Delta0Formula.successorFOAt succ index

@[simp]
theorem satisfies_successorSetAt {n : Nat} (succ index : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (successorSetAt succ index) s <->
      s succ = successorLCarrier (s index) := by
  rw [successorSetAt,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

/-- External semantics of the object-language predicate for inductive sets. -/
def IsInductiveSet (w : LCarrier.{u}) : Prop :=
  emptyLCarrier.1 ∈ w.1 /\
    forall x : LCarrier.{u}, x.1 ∈ w.1 ->
      (successorLCarrier x).1 ∈ w.1

/-- `s i` is inductive: it contains the empty set and is successor-closed. -/
def inductiveSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (emptySetAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (successorSetAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

@[simp]
theorem satisfies_inductiveSetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (inductiveSetAt i) s <->
      IsInductiveSet (s i) := by
  simp only [inductiveSetAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_emptySetAt, satisfies_successorSetAt,
    snoc_last, snoc_castSucc, IsInductiveSet]
  constructor
  · rintro ⟨⟨e, he, hemem⟩, hsucc⟩
    constructor
    · simpa only [he] using hemem
    · intro x hx
      rcases hsucc x hx with ⟨next, hnext, hnextMem⟩
      simpa only [hnext] using hnextMem
  · rintro ⟨hempty, hsucc⟩
    constructor
    · exact ⟨emptyLCarrier, rfl, hempty⟩
    · intro x hx
      exact ⟨successorLCarrier x, rfl, hsucc x hx⟩

/-- The standard `omega` in `L` is inductive. -/
theorem omegaLCarrier_isInductiveSet :
    IsInductiveSet (omegaLCarrier : LCarrier.{u}) := by
  constructor
  · exact empty_mem_omegaLCarrier
  · intro x hx
    rcases successor_mem_omegaLCarrier x hx with
      ⟨next, hnextMem, hnext⟩
    have hnextEq : next = successorLCarrier x := by
      apply lCarrier_extensionality
      intro z
      rw [hnext z, successorLCarrier_val, ZFSet.mem_insert_iff]
      simp only [Subtype.ext_iff, or_comm]
    simpa only [hnextEq] using hnextMem

/-- Every standard finite ordinal belongs to every internally inductive set. -/
theorem ordinalLCarrier_nat_mem_of_isInductiveSet
    {w : LCarrier.{u}} (hw : IsInductiveSet w) (n : Nat) :
    (ordinalLCarrier (n : Ordinal.{u})).1 ∈ w.1 := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, ordinalLCarrier_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (ordinalLCarrier (n : Ordinal.{u})) ih
      simpa only [Nat.cast_add, Nat.cast_one, Order.succ_eq_add_one,
        successorLCarrier_ordinalLCarrier] using hnext

/-- The standard `omega` is contained in every internally inductive set. -/
theorem omegaLCarrier_subset_of_isInductiveSet
    {w : LCarrier.{u}} (hw : IsInductiveSet w) :
    forall x : LCarrier.{u}, x.1 ∈ omegaLCarrier.1 -> x.1 ∈ w.1 := by
  intro x hx
  change x.1 ∈ Ordinal.omega0.toZFSet at hx
  rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, hx⟩
  rcases Ordinal.lt_omega0.mp halpha with ⟨n, hn⟩
  have hxEq : x = ordinalLCarrier (n : Ordinal.{u}) := by
    apply Subtype.ext
    calc
      x.1 = alpha.toZFSet := hx.symm
      _ = (n : Ordinal.{u}).toZFSet := congrArg Ordinal.toZFSet hn
      _ = (ordinalLCarrier (n : Ordinal.{u})).1 := rfl
  rw [hxEq]
  exact ordinalLCarrier_nat_mem_of_isInductiveSet hw n

/-- `s i` is the least inductive set, hence the model's `omega`. -/
def omegaSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (inductiveSetAt i)
    (FOFormula.all
      (FOFormula.imp
        (inductiveSetAt (Fin.last n))
        (FOFormula.boundedAll i.castSucc
          (.mem (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_omegaSetAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (omegaSetAt i) s <->
      s i = omegaLCarrier := by
  simp only [omegaSetAt, FOFormula.Satisfies,
    satisfies_inductiveSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedAll,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨homegaInd, hminimal⟩
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact hminimal omegaLCarrier omegaLCarrier_isInductiveSet z hz
    · intro hz
      exact omegaLCarrier_subset_of_isInductiveSet homegaInd z hz
  · intro h
    rw [h]
    refine ⟨omegaLCarrier_isInductiveSet, ?_⟩
    intro w hw x hx
    exact omegaLCarrier_subset_of_isInductiveSet hw x hx

/-! ## The canonical evaluator parameters -/

/-- A transparent presentation of the thirteen canonical parameters. -/
def canonicalStageParameters : Tuple LCarrier.{u} 13 :=
  ![ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((1 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((0 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((1 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((2 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((3 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((4 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((5 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((6 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((7 : Nat) : Ordinal.{u}),
    ordinalLCarrier ((8 : Nat) : Ordinal.{u}),
    omegaLCarrier]

theorem canonicalStageParameters_eq_fixed :
    (canonicalStageParameters : Tuple LCarrier.{u} 13) =
      stageHistoryFixedParameters := by
  funext i
  fin_cases i <;>
    apply Subtype.ext <;>
    norm_num [canonicalStageParameters, stageHistoryFixedParameters,
      emptyLCarrier, omegaLCarrier,
      Godel.RudimentaryTerm.varTag,
      Godel.RudimentaryTerm.appTag,
      Godel.RudimentaryTerm.operationCode,
      Ordinal.toZFSet_add_one]

/--
The thirteen evaluator parameters are, in order,
`0, 1, 0, 0, 1, ..., 8, omega`.
-/
def canonicalStageParametersFormula : FOFormula 13 :=
  .conj (emptySetAt (0 : Fin 13))
    (.conj (successorSetAt (1 : Fin 13) (0 : Fin 13))
      (.conj (.eq (2 : Fin 13) (0 : Fin 13))
        (.conj (.eq (3 : Fin 13) (0 : Fin 13))
          (.conj (successorSetAt (4 : Fin 13) (3 : Fin 13))
            (.conj (successorSetAt (5 : Fin 13) (4 : Fin 13))
              (.conj (successorSetAt (6 : Fin 13) (5 : Fin 13))
                (.conj (successorSetAt (7 : Fin 13) (6 : Fin 13))
                  (.conj (successorSetAt (8 : Fin 13) (7 : Fin 13))
                    (.conj (successorSetAt (9 : Fin 13) (8 : Fin 13))
                      (.conj (successorSetAt (10 : Fin 13) (9 : Fin 13))
                        (.conj (successorSetAt (11 : Fin 13) (10 : Fin 13))
                          (omegaSetAt (12 : Fin 13)))))))))))))

/-- The parameter specification has exactly the evaluator tuple as a model. -/
@[simp]
theorem satisfies_canonicalStageParametersFormula
    (s : Tuple LCarrier.{u} 13) :
    FOFormula.Satisfies LMem canonicalStageParametersFormula s <->
      s = stageHistoryFixedParameters := by
  simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
    satisfies_emptySetAt, satisfies_successorSetAt,
    satisfies_omegaSetAt]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12⟩
    have e0 : s 0 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := by
      simpa only [Nat.cast_zero, ordinalLCarrier_zero] using h0
    have e1 : s 1 = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by
      calc
        s 1 = successorLCarrier (s 0) := h1
        _ = successorLCarrier
            (ordinalLCarrier ((0 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e0
        _ = ordinalLCarrier ((0 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 0
        _ = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by norm_num
    have e2 : s 2 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := h2.trans e0
    have e3 : s 3 = ordinalLCarrier ((0 : Nat) : Ordinal.{u}) := h3.trans e0
    have e4 : s 4 = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by
      calc
        s 4 = successorLCarrier (s 3) := h4
        _ = successorLCarrier
            (ordinalLCarrier ((0 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e3
        _ = ordinalLCarrier ((0 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 0
        _ = ordinalLCarrier ((1 : Nat) : Ordinal.{u}) := by norm_num
    have e5 : s 5 = ordinalLCarrier ((2 : Nat) : Ordinal.{u}) := by
      calc
        s 5 = successorLCarrier (s 4) := h5
        _ = successorLCarrier
            (ordinalLCarrier ((1 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e4
        _ = ordinalLCarrier ((1 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 1
        _ = ordinalLCarrier ((2 : Nat) : Ordinal.{u}) := by norm_num
    have e6 : s 6 = ordinalLCarrier ((3 : Nat) : Ordinal.{u}) := by
      calc
        s 6 = successorLCarrier (s 5) := h6
        _ = successorLCarrier
            (ordinalLCarrier ((2 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e5
        _ = ordinalLCarrier ((2 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 2
        _ = ordinalLCarrier ((3 : Nat) : Ordinal.{u}) := by norm_num
    have e7 : s 7 = ordinalLCarrier ((4 : Nat) : Ordinal.{u}) := by
      calc
        s 7 = successorLCarrier (s 6) := h7
        _ = successorLCarrier
            (ordinalLCarrier ((3 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e6
        _ = ordinalLCarrier ((3 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 3
        _ = ordinalLCarrier ((4 : Nat) : Ordinal.{u}) := by norm_num
    have e8 : s 8 = ordinalLCarrier ((5 : Nat) : Ordinal.{u}) := by
      calc
        s 8 = successorLCarrier (s 7) := h8
        _ = successorLCarrier
            (ordinalLCarrier ((4 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e7
        _ = ordinalLCarrier ((4 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 4
        _ = ordinalLCarrier ((5 : Nat) : Ordinal.{u}) := by norm_num
    have e9 : s 9 = ordinalLCarrier ((6 : Nat) : Ordinal.{u}) := by
      calc
        s 9 = successorLCarrier (s 8) := h9
        _ = successorLCarrier
            (ordinalLCarrier ((5 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e8
        _ = ordinalLCarrier ((5 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 5
        _ = ordinalLCarrier ((6 : Nat) : Ordinal.{u}) := by norm_num
    have e10 : s 10 = ordinalLCarrier ((7 : Nat) : Ordinal.{u}) := by
      calc
        s 10 = successorLCarrier (s 9) := h10
        _ = successorLCarrier
            (ordinalLCarrier ((6 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e9
        _ = ordinalLCarrier ((6 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 6
        _ = ordinalLCarrier ((7 : Nat) : Ordinal.{u}) := by norm_num
    have e11 : s 11 = ordinalLCarrier ((8 : Nat) : Ordinal.{u}) := by
      calc
        s 11 = successorLCarrier (s 10) := h11
        _ = successorLCarrier
            (ordinalLCarrier ((7 : Nat) : Ordinal.{u})) :=
          congrArg successorLCarrier e10
        _ = ordinalLCarrier ((7 + 1 : Nat) : Ordinal.{u}) :=
          successorLCarrier_natOrdinal 7
        _ = ordinalLCarrier ((8 : Nat) : Ordinal.{u}) := by norm_num
    have hs : s = canonicalStageParameters := by
      funext i
      fin_cases i
      all_goals assumption
    exact hs.trans canonicalStageParameters_eq_fixed
  · rintro rfl
    rw [← canonicalStageParameters_eq_fixed]
    simp [canonicalStageParameters]
    refine ⟨?_, ?_⟩
    · simpa only [ordinalLCarrier_zero, Order.succ_eq_add_one,
        zero_add] using
        (successorLCarrier_ordinalLCarrier (0 : Ordinal.{u})).symm
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals congr 1 <;> norm_num

/-! ## Internal stages -/

/-- The stage coordinate of a valid internal history at `index`. -/
def InternalLStageAt (index stage : LCarrier.{u}) : Prop :=
  ∃ relation : LCarrier.{u}, StageStateAt index stage relation

/-- Layout `(fixed13, index, stage)`.  The relation coordinate is hidden. -/
def internalLStageAtLAssignment
    (index stage : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) stage

/-- A formula defining the internal constructible stage at one index. -/
def internalLStageAtFormula : FOFormula 15 :=
  .ex stageStateAtFormula

@[simp]
theorem satisfies_internalLStageAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalLStageAtFormula
        (internalLStageAtLAssignment index stage) ↔
      InternalLStageAt index stage := by
  simp only [internalLStageAtFormula, FOFormula.Satisfies,
    InternalLStageAt]
  change (∃ relation : LCarrier.{u},
      FOFormula.Satisfies LMem stageStateAtFormula
        (stageStateAtLAssignment index stage relation)) ↔ _
  simp only [satisfies_stageStateAtFormula]

/-- At a canonical ordinal index, the internally evaluated stage is exactly
the externally constructed level `L_alpha`. -/
theorem internalLStageAt_ordinal_iff
    (alpha : Ordinal.{u}) (stage : LCarrier.{u}) :
    InternalLStageAt (ordinalLCarrier alpha) stage ↔
      stage = stageLCarrier alpha := by
  constructor
  · rintro ⟨relation, hstate⟩
    rcases exists_stageStateAt_ordinal alpha with
      ⟨canonicalRelation, hcanonical⟩
    exact (stageStateAt_ordinal_outputs_unique
      alpha hstate hcanonical).1
  · rintro rfl
    exact exists_stageStateAt_ordinal alpha

/-! ## Ordinals of the internal model -/

/-- Transitivity has the expected semantics when quantifiers range over `L`.
The only extra step compared with set-sized carriers is closure of `L` under
membership. -/
theorem satisfies_ordinalTransitive_lCarrier (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.transitive ![x] ↔
      x.1.IsTransitive := by
  simp only [OrdinalFormula.transitive,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    Matrix.cons_val_zero, snoc_last]
  constructor
  · intro h y hy z hz
    have hyL : y ∈ L := mem_L_of_mem hy x.2
    have hzL : z ∈ L := mem_L_of_mem hz hyL
    exact h ⟨y, hyL⟩ hy ⟨z, hzL⟩ hz
  · intro hx y hy z hz
    exact hx.mem_trans hz hy

/-- Every member being transitive also has its ambient semantics in `L`. -/
theorem satisfies_ordinalMembersTransitive_lCarrier
    (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.membersTransitive ![x] ↔
      ∀ y ∈ x.1, y.IsTransitive := by
  simp only [OrdinalFormula.membersTransitive,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    Matrix.cons_val_zero, snoc_last]
  constructor
  · intro h y hy z hz w hw
    have hyL : y ∈ L := mem_L_of_mem hy x.2
    have hzL : z ∈ L := mem_L_of_mem hz hyL
    have hwL : w ∈ L := mem_L_of_mem hw hzL
    exact h ⟨y, hyL⟩ hy ⟨z, hzL⟩ hz ⟨w, hwL⟩ hw
  · intro h y hy z hz w hw
    exact (h y.1 hy).mem_trans hw hz

/-- The parameter-free ordinal formula is absolute to `LCarrier`. -/
@[simp]
theorem satisfies_isOrdinal_lCarrier (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem OrdinalFormula.isOrdinal ![x] ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [OrdinalFormula.isOrdinal, FOFormula.Satisfies,
    satisfies_ordinalTransitive_lCarrier,
    satisfies_ordinalMembersTransitive_lCarrier]

/-- Every internally recognized ordinal is a unique canonical ordinal code. -/
theorem exists_eq_ordinalLCarrier_of_isOrdinal
    (index : LCarrier.{u}) (hindex : index.1.IsOrdinal) :
    ∃ alpha : Ordinal.{u}, index = ordinalLCarrier alpha := by
  refine ⟨index.1.rank, ?_⟩
  apply Subtype.ext
  exact hindex.toZFSet_rank_eq.symm

/-- Put the one-variable ordinal predicate at coordinate `i`. -/
def ordinalAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.rename (fun _ : Fin 1 => i) OrdinalFormula.isOrdinal

@[simp]
theorem satisfies_ordinalAt {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (ordinalAt i) s ↔
      (s i).1.IsOrdinal := by
  rw [ordinalAt, FOFormula.satisfies_rename]
  have hassignment : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hassignment, satisfies_isOrdinal_lCarrier]

/-! ## The internally constructible class -/

/-- Layout `(fixed13, x)`. -/
def constructibleWithParametersLAssignment
    (x : LCarrier.{u}) : Tuple LCarrier.{u} 14 :=
  snoc stageHistoryFixedParameters x

/-- The assignment after adjoining witnesses for the stage index and stage. -/
def constructibleWitnessLAssignment
    (x index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (constructibleWithParametersLAssignment x) index) stage

/-- Select `(fixed13, index, stage)` from `(fixed13, x, index, stage)`. -/
def constructibleInternalStageRename : Fin 15 → Fin 16 :=
  Fin.lastCases
    (15 : Fin 16)
    (fun i14 => Fin.lastCases
      (14 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

private theorem comp_constructibleInternalStageRename
    (x index stage : LCarrier.{u}) :
    (fun i => constructibleWitnessLAssignment x index stage
      (constructibleInternalStageRename i)) =
      internalLStageAtLAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · rw [show constructibleInternalStageRename
          i13.castSucc.castSucc =
          i13.castSucc.castSucc.castSucc by
        simp only [constructibleInternalStageRename,
          Fin.lastCases_castSucc]
        apply Fin.ext
        rfl]
      simp only [constructibleWitnessLAssignment,
        constructibleWithParametersLAssignment,
        internalLStageAtLAssignment, snoc_castSucc]

/-- With the thirteen evaluator constants supplied, `x` belongs to a stage
at an internally recognized ordinal index.  Layout: `(fixed13, x)`. -/
def constructibleWithParametersFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename constructibleInternalStageRename
          internalLStageAtFormula)
        (.mem (13 : Fin 16) (15 : Fin 16)))))

/-- The internal stage predicate defines exactly membership in some external
level of the constructible hierarchy. -/
@[simp]
theorem satisfies_constructibleWithParametersFormula
    (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem constructibleWithParametersFormula
        (constructibleWithParametersLAssignment x) ↔
      ∃ alpha : Ordinal.{u}, x.1 ∈ LStageZF alpha := by
  simp only [constructibleWithParametersFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨index, stage, hindexFormula, hstageFormula, hxstage⟩
    have hindex : index.1.IsOrdinal := by
      exact (satisfies_ordinalAt (14 : Fin 16)
        (constructibleWitnessLAssignment x index stage)).mp
        hindexFormula
    have hstage : InternalLStageAt index stage := by
      apply (satisfies_internalLStageAtFormula index stage).mp
      rw [← comp_constructibleInternalStageRename x index stage]
      exact (FOFormula.satisfies_rename LMem internalLStageAtFormula
        constructibleInternalStageRename
        (constructibleWitnessLAssignment x index stage)).mp
        hstageFormula
    change x.1 ∈ stage.1 at hxstage
    rcases exists_eq_ordinalLCarrier_of_isOrdinal index hindex with
      ⟨alpha, rfl⟩
    have hstageEq :=
      (internalLStageAt_ordinal_iff alpha stage).mp hstage
    subst stage
    exact ⟨alpha, by
      simpa only [stageLCarrier_val] using hxstage⟩
  · rintro ⟨alpha, hxstage⟩
    refine ⟨ordinalLCarrier alpha, stageLCarrier alpha, ?_, ?_, ?_⟩
    · apply (satisfies_ordinalAt (14 : Fin 16)
        (constructibleWitnessLAssignment x
          (ordinalLCarrier alpha) (stageLCarrier alpha))).mpr
      exact ZFSet.isOrdinal_toZFSet alpha
    · apply (FOFormula.satisfies_rename LMem internalLStageAtFormula
        constructibleInternalStageRename
        (constructibleWitnessLAssignment x
          (ordinalLCarrier alpha) (stageLCarrier alpha))).mpr
      rw [comp_constructibleInternalStageRename,
        satisfies_internalLStageAtFormula]
      exact (internalLStageAt_ordinal_iff
        alpha (stageLCarrier alpha)).mpr rfl
    · change x.1 ∈ (stageLCarrier alpha).1
      simpa only [stageLCarrier_val] using hxstage

/-- The externalization of the class which `L` internally calls
constructible. -/
def RelativeL : Set ZFSet.{u} :=
  {x | ∃ hx : x ∈ L,
    FOFormula.Satisfies LMem constructibleWithParametersFormula
      (constructibleWithParametersLAssignment ⟨x, hx⟩)}

@[simp]
theorem mem_relativeL_iff {x : ZFSet.{u}} :
    x ∈ RelativeL ↔ x ∈ L := by
  constructor
  · rintro ⟨hxL, _hxInternal⟩
    exact hxL
  · intro hxL
    refine ⟨hxL, ?_⟩
    rw [satisfies_constructibleWithParametersFormula]
    exact mem_L_iff.mp hxL

/-- Stagewise comparison theorem: the class computed as `L` inside `L` is
the original external constructible universe. -/
theorem relativeL_eq_L : RelativeL = (L : Set ZFSet.{u}) := by
  ext x
  exact mem_relativeL_iff

/-! ## A parameter-free evaluator-coded sentence for `V = L` -/

/-- Before closing the evaluator parameters, require that they are the
canonical constants and that every set belongs to an internally computed
constructible stage. -/
def vEqualsLCoreFormula : FOFormula 13 :=
  .conj canonicalStageParametersFormula
    (FOFormula.all constructibleWithParametersFormula)

/-- Over `LCarrier`, the core formula has exactly the canonical parameter
assignment.  Its universal clause follows from the stagewise comparison. -/
@[simp]
theorem satisfies_vEqualsLCoreFormula
    (s : Tuple LCarrier.{u} 13) :
    FOFormula.Satisfies LMem vEqualsLCoreFormula s ↔
      s = stageHistoryFixedParameters := by
  simp only [vEqualsLCoreFormula, FOFormula.Satisfies,
    satisfies_canonicalStageParametersFormula,
    FOFormula.satisfies_all]
  constructor
  · exact fun h => h.1
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro x
    change FOFormula.Satisfies LMem
      constructibleWithParametersFormula
      (constructibleWithParametersLAssignment x)
    rw [satisfies_constructibleWithParametersFormula]
    exact mem_L_iff.mp x.2

/-- A genuine parameter-free evaluator-coded sentence. The thirteen
existentially bound variables are uniquely forced to be the evaluator
constants by `canonicalStageParametersFormula`. -/
def vEqualsLSentence : FirstOrder.Language.setTheory.Sentence :=
  (Model.toBoundedFormula vEqualsLCoreFormula).exs

/-- The constructible universe, as a first-order membership structure,
satisfies the evaluator-coded sentence proved correct above for `LCarrier`. -/
theorem lCarrier_models_vEqualsL :
    LCarrier.{u} ⊨ vEqualsLSentence := by
  change ((Model.toBoundedFormula vEqualsLCoreFormula).exs).Realize
    (default : Empty → LCarrier.{u})
  rw [FirstOrder.Language.BoundedFormula.realize_exs]
  refine ⟨stageHistoryFixedParameters, ?_⟩
  rw [Subsingleton.elim
    (default : Empty → LCarrier.{u}) Empty.elim]
  rw [Model.lCarrier_realize_toBoundedFormula,
    satisfies_vEqualsLCoreFormula]

end

end Constructible.Model
