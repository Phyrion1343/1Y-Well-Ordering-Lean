/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPositiveFormulaEnumeration

/-!
# Definable subsets as textbook E sections

Every member of the genuine internal definable powerset `DefZF a` is a
section of one relation in the textbook enumeration `E`.  The parameters are
represented by an actual finite function graph in `a^n`.

Only the direction needed for the cardinality bound is asserted here.  An
arbitrary value of `E` need not be treated as a section unless its arity and
parameter graph satisfy the displayed side conditions.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- Every internally represented definable subset of `a` has a textbook
`E`-section presentation with one finite tuple graph of parameters. -/
theorem exists_textbookE_section_of_mem_DefZF
    {a z : ZFSet.{u}} (hz : z ∈ DefZF a) :
    ∃ n m : Nat, ∃ p : ZFSet.{u},
      p ∈ textbookTupleSpace a n ∧
        ∀ x, x ∈ a →
          (x ∈ z ↔
            textbookTupleSnocGraph p n x ∈
              textbookEZF a (natCode (n + 1)) (natCode m)) := by
  rcases mem_DefZF_iff_exists_satisfies.mp hz with
    ⟨_hza, n, params, formula, hformula⟩
  rcases exists_textbookECode_for_positiveFormula a formula with
    ⟨code, hcode⟩
  refine ⟨n, code, textbookTupleGraph params,
    textbookTupleGraph_mem_tupleSpace params, ?_⟩
  intro x hx
  let xCarrier : ZFCarrier a := ⟨x, hx⟩
  calc
    x ∈ z ↔
        FOFormula.Satisfies (zfCarrierMem a) formula
          (snoc params xCarrier) := by
            simpa only [xCarrier] using hformula xCarrier
    _ ↔ textbookTupleGraph (snoc params xCarrier) ∈
          textbookEZF a (natCode (n + 1)) (natCode code) :=
      (hcode (snoc params xCarrier)).symm
    _ ↔ textbookTupleSnocGraph (textbookTupleGraph params) n x ∈
          textbookEZF a (natCode (n + 1)) (natCode code) := by
      rw [textbookTupleGraph_snoc]

end

end Constructible
