/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDefinability

/-!
# Textbook enumeration of positive-arity formula relations

For a formula with `n + 1` free variables, this file recursively constructs
the actual relation set on the textbook tuple space `a^(n+1)`.  Atomic
formulas use `D_in` and `D_eq`; negation uses relative complement;
conjunction uses intersection; and existential quantification uses the
textbook projection operation.

The semantic correctness theorem is proved on the Kuratowski function graph
which represents each tuple.  The closure clauses then show that the relation
belongs to the genuine internal set `textbookDfZF a (n + 1)`, so completeness
of the textbook `E` enumeration supplies a natural-number code for it.

Only positive arities are asserted.  This is mathematically significant:
the textbook convention makes the zero-arity projection empty, whereas an
ordinary closed existential sentence can be true.  Skolem matrices have the
positive arity `n + 1`, so no needed witness relation is lost and the
zero-arity convention is not silently identified with sentence semantics.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- The recursively generated textbook relation set.  At arity zero this
still follows the textbook's exceptional projection convention; semantic
correctness is therefore stated below only under `n != 0`. -/
noncomputable def textbookFormulaRelationZF
    (a : ZFSet.{u}) : {n : Nat} -> FOFormula n -> ZFSet.{u}
  | n, .mem i j => textbookDInZF a n i.1 j.1
  | n, .eq i j => textbookDEqZF a n i.1 j.1
  | n, .neg formula =>
      relativeDifferenceZF (textbookTupleSpace a n)
        (textbookFormulaRelationZF a formula)
  | _, .conj formula psi =>
      intersectionZF
        (textbookFormulaRelationZF a formula)
        (textbookFormulaRelationZF a psi)
  | n, .ex formula =>
      textbookExistsProjZF a n
        (textbookFormulaRelationZF a formula)

/-- The positive-arity specialization used by Skolem matrices. -/
noncomputable def textbookPositiveFormulaRelation
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) : ZFSet.{u} :=
  textbookFormulaRelationZF a formula

/-- On every represented tuple, the recursively constructed relation has
exactly the ordinary Tarskian semantics of the source formula. -/
theorem textbookTupleGraph_mem_textbookFormulaRelationZF_iff_of_ne_zero
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula n)
    (hn : n ≠ 0) (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookFormulaRelationZF a formula ↔
      FOFormula.Satisfies (zfCarrierMem a) formula s := by
  induction formula with
  | mem i j =>
      simpa only [textbookFormulaRelationZF, FOFormula.Satisfies,
        zfCarrierMem] using
        (textbookTupleGraph_mem_DInZF_iff s i j)
  | eq i j =>
      simpa only [textbookFormulaRelationZF, FOFormula.Satisfies] using
        (textbookTupleGraph_mem_DEqZF_iff s i j)
  | neg formula ih =>
      simp only [textbookFormulaRelationZF,
        mem_relativeDifferenceZF_iff,
        textbookTupleGraph_mem_tupleSpace, true_and,
        FOFormula.Satisfies, ih hn]
  | conj formula psi ihFormula ihPsi =>
      simp only [textbookFormulaRelationZF,
        mem_intersectionZF_iff, FOFormula.Satisfies,
        ihFormula hn, ihPsi hn]
  | @ex m formula ih =>
      rw [textbookFormulaRelationZF,
        textbookTupleGraph_mem_existsProjZF_iff hn]
      apply exists_congr
      intro x
      exact ih (Nat.succ_ne_zero m) (snoc s x)

/-- Positive arity removes the exceptional zero-arity case. -/
@[simp]
theorem textbookTupleGraph_mem_textbookPositiveFormulaRelation_iff
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) (n + 1)) :
    textbookTupleGraph s ∈ textbookPositiveFormulaRelation a formula ↔
      FOFormula.Satisfies (zfCarrierMem a) formula s := by
  exact textbookTupleGraph_mem_textbookFormulaRelationZF_iff_of_ne_zero
    a formula (Nat.succ_ne_zero n) s

/-- Every positive-arity formula relation belongs to the textbook `Df` set
at the matching arity. -/
theorem textbookFormulaRelationZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula n) :
    textbookFormulaRelationZF a formula ∈ textbookDfZF a n := by
  induction formula with
  | mem i j =>
      exact textbookDInZF_mem_textbookDfZF a i.2 j.2
  | eq i j =>
      exact textbookDEqZF_mem_textbookDfZF a i.2 j.2
  | neg formula ih =>
      simpa only [textbookFormulaRelationZF, textbookTupleSpace] using
        (textbookDfZF_relativeDifference a ih)
  | conj formula psi ihFormula ihPsi =>
      simpa only [textbookFormulaRelationZF] using
        (textbookDfZF_intersection a ihFormula ihPsi)
  | ex formula ih =>
      simpa only [textbookFormulaRelationZF] using
        (textbookDfZF_existsProjection a ih)

/-- Every positive-arity formula relation belongs to the textbook `Df` set
at the matching arity. -/
theorem textbookPositiveFormulaRelation_mem_textbookDfZF
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    textbookPositiveFormulaRelation a formula ∈
      textbookDfZF a (n + 1) := by
  exact textbookFormulaRelationZF_mem_textbookDfZF a formula

/-- Completeness of the textbook `E` enumeration supplies a code for the
relation of every positive-arity formula. -/
theorem exists_textbookEZF_eq_textbookPositiveFormulaRelation
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    ∃ code : Nat,
      textbookEZF a (natCode (n + 1)) (natCode code) =
        textbookPositiveFormulaRelation a formula :=
  exists_textbookEZF_eq_of_mem_textbookDfZF
    (textbookPositiveFormulaRelation_mem_textbookDfZF a formula)

/-- Semantic form of the preceding enumeration theorem: one textbook `E`
value recognizes exactly the satisfying represented tuples. -/
theorem exists_textbookECode_for_positiveFormula
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    ∃ code : Nat, ∀ s : Tuple (ZFCarrier a) (n + 1),
      textbookTupleGraph s ∈
          textbookEZF a (natCode (n + 1)) (natCode code) ↔
        FOFormula.Satisfies (zfCarrierMem a) formula s := by
  rcases exists_textbookEZF_eq_textbookPositiveFormulaRelation
      a formula with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  intro s
  rw [hcode]
  exact textbookTupleGraph_mem_textbookPositiveFormulaRelation_iff
    a formula s

end

end Constructible
