/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Arithmetic facts for the textbook enumeration code

Wang, *Axiomatic Set Theory*, Section 6.4 enumerates the five constructors
used to generate definable relations by natural numbers of the form

`2 ^ i * 3 ^ j * 5 ^ tag`.

This file records only the metatheoretic arithmetic facts about that code.
It does not claim that exponentiation, multiplication, or decoding has
already been represented by a first-order formula inside a ZF model.  Those
internal graph formulas and their absoluteness are separate obligations.
-/

@[expose] public section

namespace Constructible

/-- The exact prime-power code used in the five clauses defining `E`. -/
def textbookECode (i j tag : Nat) : Nat :=
  2 ^ i * 3 ^ j * 5 ^ tag

theorem textbookECode_ne_zero (i j tag : Nat) :
    textbookECode i j tag ≠ 0 := by
  simp [textbookECode]

theorem textbookECode_pos (i j tag : Nat) :
    0 < textbookECode i j tag :=
  Nat.pos_of_ne_zero (textbookECode_ne_zero i j tag)

@[simp]
theorem textbookECode_factorization_two (i j tag : Nat) :
    (textbookECode i j tag).factorization 2 = i := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

@[simp]
theorem textbookECode_factorization_three (i j tag : Nat) :
    (textbookECode i j tag).factorization 3 = j := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

@[simp]
theorem textbookECode_factorization_five (i j tag : Nat) :
    (textbookECode i j tag).factorization 5 = tag := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

/-- Unique factorization makes all three fields of the textbook code unique. -/
theorem textbookECode_injective_fields
    {i j tag i' j' tag' : Nat}
    (h : textbookECode i j tag = textbookECode i' j' tag') :
    i = i' /\ j = j' /\ tag = tag' := by
  constructor
  . simpa only [textbookECode_factorization_two] using
      congrArg (fun n : Nat => n.factorization 2) h
  constructor
  . simpa only [textbookECode_factorization_three] using
      congrArg (fun n : Nat => n.factorization 3) h
  . simpa only [textbookECode_factorization_five] using
      congrArg (fun n : Nat => n.factorization 5) h

/-- The recursive reference `i` in every constructor clause is earlier than
the code of that clause.  This is the numerical decrease used by the
well-founded recursion defining `E`. -/
theorem textbookECode_index_lt (i j tag : Nat) :
    i < textbookECode i j tag := by
  have hthree : 0 < 3 ^ j := Nat.pow_pos (by decide)
  have hfive : 0 < 5 ^ tag := Nat.pow_pos (by decide)
  apply lt_of_lt_of_le i.lt_two_pow_self
  simp only [textbookECode]
  simpa only [Nat.mul_assoc] using
    Nat.le_mul_of_pos_right (2 ^ i) (Nat.mul_pos hthree hfive)

end Constructible
