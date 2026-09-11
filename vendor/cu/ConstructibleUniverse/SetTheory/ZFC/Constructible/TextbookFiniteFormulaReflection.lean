/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection

/-!
# Simultaneous reflection for a finite list of fixed-arity formulas

`exists_reflecting_LStage` reflects one formula at a time.  This file adds
the small bounded interface used when a finite collection of formulas has to
be reflected at one common constructible level.  The formulas have one fixed
free-variable arity, so the same parameter tuple can be used for every member
of the list.

The proof follows the textbook finite-fragment argument: fold the list into
one conjunction, take the reflection ordinal of that conjunction, and project
the resulting `ClosesFrom` proof back to each listed formula.  This is finite
fragment reflection only; it does not assert full elementarity.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-- Right-associated conjunction with a distinguished first formula. -/
def textbookFormulaConjunction {n : Nat}
    (head : FOFormula n) : List (FOFormula n) -> FOFormula n
  | [] => head
  | formula :: rest =>
      FOFormula.conj formula (textbookFormulaConjunction head rest)

@[simp]
theorem textbookFormulaConjunction_nil {n : Nat}
    (head : FOFormula n) :
    textbookFormulaConjunction head [] = head :=
  rfl

@[simp]
theorem textbookFormulaConjunction_cons {n : Nat}
    (head formula : FOFormula n) (rest : List (FOFormula n)) :
    textbookFormulaConjunction head (formula :: rest) =
      FOFormula.conj formula (textbookFormulaConjunction head rest) :=
  rfl

/-- `ClosesFrom` for the folded conjunction projects to every list member. -/
theorem closesFrom_textbookFormulaConjunction_of_mem
    {n : Nat} {head : FOFormula n} {rest : List (FOFormula n)}
    {alpha beta : Ordinal.{u}}
    (hclose : ClosesFrom
      (textbookFormulaConjunction head rest) alpha beta)
    {formula : FOFormula n}
    (hformula : formula = head ∨ formula ∈ rest) :
    ClosesFrom formula alpha beta := by
  induction rest generalizing head with
  | nil =>
      rcases hformula with hhead | hformula
      · subst formula
        exact hclose
      · simp at hformula
  | cons first rest ih =>
      change
        ClosesFrom first alpha beta ∧
          ClosesFrom (textbookFormulaConjunction head rest) alpha beta at hclose
      rcases hformula with hhead | hformula
      · subst formula
        exact ih hclose.2 (Or.inl rfl)
      · rw [List.mem_cons] at hformula
        rcases hformula with rfl | hformula
        · exact hclose.1
        · exact ih hclose.2 (Or.inr hformula)

/-- One constructible level reflects every member of a finite fixed-arity
formula list, for every tuple of parameters from that level. -/
theorem exists_LStage_reflecting_formulaList
    {n : Nat} (head : FOFormula n) (rest : List (FOFormula n))
    (start : Ordinal.{u}) :
    ∃ beta : Ordinal.{u},
      start ≤ beta ∧ Order.IsSuccLimit beta ∧
        ∀ {formula : FOFormula n},
          (formula = head ∨ formula ∈ rest) →
          ∀ (s : Tuple ZFSet.{u} n),
            (∀ i, s i ∈ LStageZF beta) →
              (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
                  formula s ↔
                Model.SatisfiesIn (L : Set ZFSet.{u}) formula s) := by
  let conjunction := textbookFormulaConjunction head rest
  let beta := reflectionOrdinal conjunction start
  refine ⟨beta, le_reflectionOrdinal conjunction start,
    reflectionOrdinal_isSuccLimit conjunction start, ?_⟩
  intro formula hformula s hs
  exact satisfiesIn_stage_iff_L_of_closes formula beta
    (closesFrom_textbookFormulaConjunction_of_mem
      (closesFrom_reflectionOrdinal conjunction start) hformula)
    s hs

/-- List-shaped wrapper for `exists_LStage_reflecting_formulaList`. -/
theorem exists_LStage_reflecting_nonempty_formulaList
    {n : Nat} (formulas : List (FOFormula n))
    (hformulas : formulas ≠ []) (start : Ordinal.{u}) :
    ∃ beta : Ordinal.{u},
      start ≤ beta ∧ Order.IsSuccLimit beta ∧
        ∀ {formula : FOFormula n},
          formula ∈ formulas →
          ∀ (s : Tuple ZFSet.{u} n),
            (∀ i, s i ∈ LStageZF beta) →
              (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
                  formula s ↔
                Model.SatisfiesIn (L : Set ZFSet.{u}) formula s) := by
  cases formulas with
  | nil => simp at hformulas
  | cons head rest =>
      simpa only [List.mem_cons] using
        (exists_LStage_reflecting_formulaList head rest start)

/-- The common reflecting level can also be chosen to contain a displayed
constructible seed. -/
theorem exists_LStage_reflecting_nonempty_formulaList_containing
    {n : Nat} (formulas : List (FOFormula n))
    (hformulas : formulas ≠ []) (seed : ZFSet.{u})
    (hseedL : ∀ x ∈ seed, x ∈ L) :
    ∃ beta : Ordinal.{u},
      seed ⊆ LStageZF beta ∧ Order.IsSuccLimit beta ∧
        ∀ {formula : FOFormula n},
          formula ∈ formulas →
          ∀ (s : Tuple ZFSet.{u} n),
            (∀ i, s i ∈ LStageZF beta) →
              (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
                  formula s ↔
                Model.SatisfiesIn (L : Set ZFSet.{u}) formula s) := by
  rcases exists_LStage_for_members hseedL with ⟨alpha, hseedAlpha⟩
  let start : Ordinal.{u} := max alpha (Order.succ 0)
  rcases exists_LStage_reflecting_nonempty_formulaList
      formulas hformulas start with
    ⟨beta, hstartBeta, hbetaLimit, hreflect⟩
  refine ⟨beta, ?_, hbetaLimit, hreflect⟩
  intro x hx
  exact LStageZF_mono
    ((le_max_left alpha (Order.succ 0)).trans hstartBeta)
    (hseedAlpha x hx)

end ZFC

end Constructible
