/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeArithmetic

/-!
# Metatheoretic decoding of the textbook enumeration code

Wang, *Axiomatic Set Theory*, Section 6.4 uses the five tags `0, ..., 4`
in codes of the form `2 ^ i * 3 ^ j * 5 ^ tag`.  This file supplies a
checked decoder for those natural-number codes.  It first reads the three
prime exponents and then re-encodes them; the latter check rejects zero and
numbers having any additional prime factor.

This is only an auxiliary operation on Lean's metatheoretic type `Nat`.
It is not an internal operation of a ZF model and is never used as though
its graph were automatically available to Separation or Replacement.  The
corresponding object-language graph formula and its absoluteness are proved
separately in `TextbookECodeFormula`.
-/

@[expose] public section

namespace Constructible

/-- Decode an accepted textbook constructor code into its two indices and
one of the five tags.  The re-encoding test is essential: factorization at
`2`, `3`, and `5` alone cannot detect other prime factors. -/
def textbookEDecode (m : Nat) : Option (Nat × Nat × Nat) :=
  let i := m.factorization 2
  let j := m.factorization 3
  let tag := m.factorization 5
  if tag < 5 ∧ m = textbookECode i j tag then
    some (i, j, tag)
  else
    none

/-- The decoder accepts exactly the five tagged textbook codes. -/
theorem textbookEDecode_eq_some_iff (m i j tag : Nat) :
    textbookEDecode m = some (i, j, tag) ↔
      tag < 5 ∧ m = textbookECode i j tag := by
  simp only [textbookEDecode]
  split_ifs with h
  · rcases h with ⟨htag, hcode⟩
    constructor
    · intro hsome
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨hi, hj, htag'⟩
      subst i
      subst j
      subst tag
      exact ⟨htag, hcode⟩
    · rintro ⟨_, hcode'⟩
      have hfields := textbookECode_injective_fields
        (hcode.symm.trans hcode')
      rcases hfields with ⟨hi, hj, htag'⟩
      simp only [hi, hj, htag']
  · constructor
    · intro hnone
      cases hnone
    · rintro ⟨htag, hcode⟩
      apply (h ?_).elim
      constructor
      · rw [hcode, textbookECode_factorization_five]
        exact htag
      · rw [hcode]
        simp only [textbookECode_factorization_two,
          textbookECode_factorization_three, textbookECode_factorization_five]

/-- Every valid textbook code decodes to the fields from which it was made. -/
@[simp]
theorem textbookEDecode_textbookECode (i j tag : Nat) (htag : tag < 5) :
    textbookEDecode (textbookECode i j tag) = some (i, j, tag) := by
  rw [textbookEDecode_eq_some_iff]
  exact ⟨htag, rfl⟩

@[simp]
theorem textbookEDecode_code_zero (i j : Nat) :
    textbookEDecode (textbookECode i j 0) = some (i, j, 0) := by
  exact textbookEDecode_textbookECode i j 0 (by decide)

@[simp]
theorem textbookEDecode_code_one (i j : Nat) :
    textbookEDecode (textbookECode i j 1) = some (i, j, 1) := by
  exact textbookEDecode_textbookECode i j 1 (by decide)

@[simp]
theorem textbookEDecode_code_two (i j : Nat) :
    textbookEDecode (textbookECode i j 2) = some (i, j, 2) := by
  exact textbookEDecode_textbookECode i j 2 (by decide)

@[simp]
theorem textbookEDecode_code_three (i j : Nat) :
    textbookEDecode (textbookECode i j 3) = some (i, j, 3) := by
  exact textbookEDecode_textbookECode i j 3 (by decide)

@[simp]
theorem textbookEDecode_code_four (i j : Nat) :
    textbookEDecode (textbookECode i j 4) = some (i, j, 4) := by
  exact textbookEDecode_textbookECode i j 4 (by decide)

/-- A successfully decoded natural number has unique constructor fields.
The proof deliberately reduces uniqueness to the prime-factorization
injectivity theorem for `textbookECode`. -/
theorem textbookEDecode_some_fields_unique
    {m i j tag i' j' tag' : Nat}
    (h : textbookEDecode m = some (i, j, tag))
    (h' : textbookEDecode m = some (i', j', tag')) :
    i = i' ∧ j = j' ∧ tag = tag' := by
  have hcode := (textbookEDecode_eq_some_iff m i j tag).mp h
  have hcode' := (textbookEDecode_eq_some_iff m i' j' tag').mp h'
  exact textbookECode_injective_fields (hcode.2.symm.trans hcode'.2)

end Constructible
