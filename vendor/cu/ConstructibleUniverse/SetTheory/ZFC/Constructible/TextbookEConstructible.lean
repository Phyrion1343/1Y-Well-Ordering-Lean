/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEInternalTasks
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryConstructible

/-!
# Constructibility of the textbook E values

This file proves directly that the standard-natural-number values of the
textbook recursion `E(a,n,m)` are constructible whenever `a` is.  The proof
does not place `L` inside a transitive set model of ZF.

The main preliminary step is closure under finite function spaces.  Every
finite function graph with values in a constructible set is itself
constructible.  The whole finite function space is then obtained by one
bounded definition over a constructible level containing all those graphs.
The atomic relations and existential projection are handled by the same
bounded-section argument.  Finally, strong induction on the numerical `E`
code follows the five clauses from the textbook definition.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## A bounded-definition closure lemma for `L` -/

/-- A set all of whose members are constructible is constructible when one
fixed bounded formula defines it from finitely many constructible
parameters. -/
private theorem mem_L_of_delta0_definition
    {z : ZFSet.{u}} {n : Nat}
    (params : Tuple ZFSet.{u} n) (hparams : ∀ i, params i ∈ L)
    (formula : Delta0Formula (n + 1))
    (correct : ∀ q : ZFSet.{u},
      Delta0Formula.Satisfies Delta0Formula.ZFMem formula
          (snoc params q) ↔ q ∈ z)
    (hmembers : ∀ q ∈ z, q ∈ L) :
    z ∈ L := by
  rcases exists_LStage_for_tuple params hparams with
    ⟨parameterStage, hparameterStage⟩
  rcases exists_LStage_for_members hmembers with
    ⟨memberStage, hmemberStage⟩
  let stage : Ordinal.{u} := max parameterStage memberStage
  let stageParams : Tuple (ZFCarrier (LStageZF stage)) n :=
    fun i =>
      ⟨params i,
        LStageZF_mono (le_max_left parameterStage memberStage)
          (hparameterStage i)⟩
  let certificate : Delta0Section (LStageZF stage) z :=
    { arity := n
      params := stageParams
      formula := formula
      correct := by
        intro q
        have hvalues : Delta0Formula.val stageParams = params := by
          funext i
          rfl
        simpa only [hvalues] using correct q.1 }
  refine ⟨Order.succ stage, ?_⟩
  rw [LStageZF_succ]
  apply certificate.mem_DefZF (LStageZF_isTransitive stage)
  intro q hq
  exact LStageZF_mono (le_max_right parameterStage memberStage)
    (hmemberStage q hq)

/-! ## Finite tuple spaces preserve constructibility -/

/-- Adjoining one constructible element to a constructible set preserves
constructibility. -/
theorem textbookInsert_mem_L {x a : ZFSet.{u}}
    (hx : x ∈ L) (ha : a ∈ L) : insert x a ∈ L := by
  rw [ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L hx) ha

/-- The graph of a finite tuple of members of a constructible set belongs to
`L`. -/
theorem textbookTupleGraph_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) {n : Nat}
    (tuple : Tuple (ZFCarrier a) n) :
    textbookTupleGraph tuple ∈ L := by
  induction n with
  | zero =>
      have hempty : textbookTupleGraph tuple = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro q hq
        rcases (mem_textbookTupleGraph_iff tuple).mp hq with ⟨i, _⟩
        exact Fin.elim0 i
      rw [hempty]
      exact empty_mem_L
  | succ n ih =>
      let initial : Tuple (ZFCarrier a) n :=
        fun i => tuple i.castSucc
      let finalEntry : ZFCarrier a := tuple (Fin.last n)
      have htuple : tuple = snoc initial finalEntry := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [finalEntry]
        · simp [initial]
      rw [htuple, textbookTupleGraph_snoc]
      apply textbookInsert_mem_L
      · exact orderedPair_mem_L (natCode_mem_L n)
          (mem_L_of_mem finalEntry.2 ha)
      · exact ih initial

/-- The actual set of all functions from a standard finite ordinal to a
constructible set is constructible. -/
theorem textbookTupleSpace_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n : Nat) :
    textbookTupleSpace a n ∈ L := by
  let params : Tuple ZFSet.{u} 2 := ![natCode n, a]
  apply mem_L_of_delta0_definition params (by
      intro i
      fin_cases i
      · exact natCode_mem_L n
      · exact ha)
    (TextbookDefFormula.isFunctionDeltaAt
      (2 : Fin 3) (0 : Fin 3) (1 : Fin 3))
  · intro graph
    rw [TextbookDefFormula.satisfies_isFunctionDeltaAt]
    exact mem_textbookTupleSpace_iff.symm
  · intro graph hgraph
    rcases exists_textbookTupleGraph_eq_of_isFunc
        (mem_textbookTupleSpace_iff.mp hgraph) with
      ⟨tuple, rfl⟩
    exact textbookTupleGraph_mem_L ha tuple

/-! ## The four set operations occurring in the E clauses -/

/-- The atomic membership relation on a finite tuple space is constructible. -/
theorem textbookDInZF_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n i j : Nat) :
    textbookDInZF a n i j ∈ L := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact natCode_mem_L i
      · exact natCode_mem_L j)
    TextbookDefFormula.dInMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.dInMemberDelta
          ![a, natCode n, natCode i, natCode j, graph] ↔ _
    rw [TextbookDefFormula.satisfies_dInMemberDelta]
    rw [← textbookDInCodeZF_natCode]
    rw [mem_textbookDInCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem (textbookDInZF_subset_tupleSpace a n i j hgraph)
      hspace

/-- The atomic equality relation on a finite tuple space is constructible. -/
theorem textbookDEqZF_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n i j : Nat) :
    textbookDEqZF a n i j ∈ L := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact natCode_mem_L i
      · exact natCode_mem_L j)
    TextbookDefFormula.dEqMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.dEqMemberDelta
          ![a, natCode n, natCode i, natCode j, graph] ↔ _
    rw [TextbookDefFormula.satisfies_dEqMemberDelta]
    rw [← textbookDEqCodeZF_natCode]
    rw [mem_textbookDEqCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem (textbookDEqZF_subset_tupleSpace a n i j hgraph)
      hspace

/-- Relative difference of constructible sets is constructible. -/
theorem relativeDifferenceZF_mem_L
    {space removed : ZFSet.{u}}
    (hspace : space ∈ L) (hremoved : removed ∈ L) :
    relativeDifferenceZF space removed ∈ L := by
  simpa [relativeDifferenceZF, Godel.op, Godel.F1] using
    (Godel.op_mem_L (i := (1 : Fin 9)) hspace hremoved)

/-- Intersection of constructible sets is constructible. -/
theorem intersectionZF_mem_L
    {left right : ZFSet.{u}} (hleft : left ∈ L) (hright : right ∈ L) :
    intersectionZF left right ∈ L := by
  have hleftRight : relativeDifferenceZF left right ∈ L :=
    relativeDifferenceZF_mem_L hleft hright
  have hresult :
      relativeDifferenceZF left (relativeDifferenceZF left right) ∈ L :=
    relativeDifferenceZF_mem_L hleft hleftRight
  have heq :
      relativeDifferenceZF left (relativeDifferenceZF left right) =
        intersectionZF left right := by
    apply ZFSet.ext
    intro x
    simp only [mem_relativeDifferenceZF_iff, mem_intersectionZF_iff]
    tauto
  rwa [heq] at hresult

/-- The textbook existential projection of a constructible relation is
constructible. -/
theorem textbookExistsProjZF_mem_L
    {a relation : ZFSet.{u}} (ha : a ∈ L) (hrelation : relation ∈ L)
    (n : Nat) : textbookExistsProjZF a n relation ∈ L := by
  let params : Tuple ZFSet.{u} 3 := ![a, natCode n, relation]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact hrelation)
    TextbookDefFormula.existsProjMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.existsProjMemberDelta
          ![a, natCode n, relation, graph] ↔ _
    rw [TextbookDefFormula.satisfies_existsProjMemberDelta]
    rw [← textbookExistsProjCodeZF_natCode]
    rw [mem_textbookExistsProjCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem
      (textbookExistsProjZF_subset_tupleSpace a n relation hgraph) hspace

/-! ## Strong induction through the five E clauses -/

/-- Every standard-code value of the textbook enumeration is constructible
when its set parameter is constructible. -/
theorem textbookEZF_natCode_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ L := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases hdecode : textbookEDecode m with
      | none =>
          rw [textbookEZF_eq_empty_of_decode_none a n m hdecode]
          exact empty_mem_L
      | some fields =>
          rcases fields with ⟨i, j, tag⟩
          have hdecoded :=
            (textbookEDecode_eq_some_iff m i j tag).mp hdecode
          rcases hdecoded with ⟨htag, hm⟩
          subst m
          have hi : i < textbookECode i j tag :=
            textbookECode_index_lt i j tag
          have htagCases :
              tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 := by
            omega
          rcases htagCases with rfl | rfl | rfl | rfl | rfl
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_zero a n i j hin hjn,
                  textbookDInCodeZF_natCode]
                exact textbookDInZF_mem_L ha n i j
              · rw [textbookEZF_code_zero_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_L
            · rw [textbookEZF_code_zero_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_L
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_one a n i j hin hjn,
                  textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_L ha n i j
              · rw [textbookEZF_code_one_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_L
            · rw [textbookEZF_code_one_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_L
          · rw [textbookEZF_code_two]
            exact relativeDifferenceZF_mem_L
              (textbookTupleSpace_mem_L ha n) (ih i hi n)
          · have hj : j < textbookECode i j 3 := by
              apply lt_of_lt_of_le
                (lt_of_lt_of_le j.lt_two_pow_self
                  (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j))
              simp only [textbookECode]
              have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
              have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
              simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                Nat.le_mul_of_pos_left (3 ^ j) (Nat.mul_pos htwo hfive)
            rw [textbookEZF_code_three]
            exact intersectionZF_mem_L (ih i hi n) (ih j hj n)
          · rw [textbookEZF_code_four,
              textbookExistsProjCodeZF_natCode]
            exact textbookExistsProjZF_mem_L ha (ih i hi (n + 1)) n

namespace Model

/-- A standard-code `E` value, packaged as an actual member of `L`. -/
def textbookEZFLCarrier
    (U : LCarrier.{u}) (n m : Nat) : LCarrier.{u} :=
  ⟨textbookEZF U.1 (natCode n) (natCode m),
    textbookEZF_natCode_mem_L U.2 n m⟩

@[simp]
theorem textbookEZFLCarrier_val
    (U : LCarrier.{u}) (n m : Nat) :
    (textbookEZFLCarrier U n m).1 =
      textbookEZF U.1 (natCode n) (natCode m) :=
  rfl

end Model

end

end Constructible
