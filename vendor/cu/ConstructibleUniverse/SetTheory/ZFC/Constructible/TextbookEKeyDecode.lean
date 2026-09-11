/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomain

/-!
# Metatheoretic decoding of keys in the textbook recursion domain

The recursion defining the textbook enumeration `E(a,n,m)` is indexed by
the actual set `omega x omega`. Its keys are Kuratowski pairs

`<natCode m, natCode n>`,

where the first coordinate is the recursive code `m` and the second is the
arity `n`. This file supplies the corresponding partial decoder into Lean's
metatheoretic type `Nat x Nat`.

`Classical.choose` below is used only to read the two unique coordinates in
the external implementation of the recursion step. The decoder is not an
internal function of a ZF model, and no Separation or Replacement argument
may use it as though its graph were internally available. The internal
domain and key formulas, together with their restricted semantics, are
proved independently in `TextbookEDomain`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Unique standard coordinates -/

/-- Two representations of a set as a pair of standard natural-number
codes have the same fields. -/
theorem textbookEKey_natCode_fields_unique
    {key : ZFSet.{u}} {m n m' n' : Nat}
    (h : key = ZFSet.pair (natCode m) (natCode n))
    (h' : key = ZFSet.pair (natCode m') (natCode n')) :
    And (m = m') (n = n') := by
  have hcoordinates := ZFSet.pair_inj.mp (h.symm.trans h')
  exact And.intro
    (natCode_injective hcoordinates.1)
    (natCode_injective hcoordinates.2)

/-- The proposition that `key` has standard natural-number coordinates,
packaged with the two coordinates as one metatheoretic product. -/
def IsTextbookEKey (key : ZFSet.{u}) : Prop :=
  Exists fun coordinates : Prod Nat Nat =>
    key = ZFSet.pair (natCode coordinates.1) (natCode coordinates.2)

/-- Decode a genuine textbook recursion key. Keys outside the represented
set `omega x omega` are sent to `none`.

The output order is `(recursiveCode, arity)`, matching the domain key
`<m,n>` and not the opposite order used by some graph encodings. -/
noncomputable def textbookEKeyDecode
    (key : ZFSet.{u}) : Option (Prod Nat Nat) := by
  classical
  exact if h : IsTextbookEKey key then some (Classical.choose h) else none

/-! ## Exact decoder specification -/

/-- The decoder returns `(m,n)` exactly for the Kuratowski key
`<natCode m,natCode n>`. -/
theorem textbookEKeyDecode_eq_some_iff
    (key : ZFSet.{u}) (m n : Nat) :
    Iff (textbookEKeyDecode key = some (m, n))
      (key = ZFSet.pair (natCode m) (natCode n)) := by
  rw [textbookEKeyDecode]
  split_ifs with hkey
  · have hcoordinates :
        key = ZFSet.pair (natCode (Classical.choose hkey).1)
          (natCode (Classical.choose hkey).2) :=
      Classical.choose_spec hkey
    constructor
    · intro hsome
      have hchosen : Classical.choose hkey = (m, n) :=
        Option.some.inj hsome
      rw [hchosen] at hcoordinates
      exact hcoordinates
    · intro hrequested
      have hfields := textbookEKey_natCode_fields_unique
        hcoordinates hrequested
      have hchosen : Classical.choose hkey = (m, n) :=
        Prod.ext hfields.1 hfields.2
      exact congrArg some hchosen
  · constructor
    · intro hnone
      cases hnone
    · intro hrequested
      exfalso
      apply hkey
      exact Exists.intro (m, n) hrequested

@[simp]
theorem textbookEKeyDecode_pair_natCode (m n : Nat) :
    textbookEKeyDecode
      (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) = some (m, n) := by
  rw [textbookEKeyDecode_eq_some_iff]

/-- Any two successful decodings of one key have identical fields. -/
theorem textbookEKeyDecode_some_fields_unique
    {key : ZFSet.{u}} {m n m' n' : Nat}
    (h : textbookEKeyDecode key = some (m, n))
    (h' : textbookEKeyDecode key = some (m', n')) :
    And (m = m') (n = n') := by
  exact textbookEKey_natCode_fields_unique
    ((textbookEKeyDecode_eq_some_iff key m n).mp h)
    ((textbookEKeyDecode_eq_some_iff key m' n').mp h')

/-! ## Agreement with the actual set-coded domain -/

/-- Existence of decoded fields is exactly membership in the actual
set-coded recursion domain `omega x omega`. -/
theorem textbookEKeyDecode_exists_iff_mem_textbookEDomain
    (key : ZFSet.{u}) :
    Iff
      (Exists fun m : Nat => Exists fun n : Nat =>
        textbookEKeyDecode key = some (m, n))
      (key ∈ TextbookEDomain) := by
  constructor
  · intro hdecoded
    cases hdecoded with
    | intro m hdecodedN =>
      cases hdecodedN with
      | intro n hdecode =>
        have hkey :=
          (textbookEKeyDecode_eq_some_iff key m n).mp hdecode
        have hmOmega :
            (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode m)).mpr (Exists.intro m rfl)
        have hnOmega :
            (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode n)).mpr (Exists.intro n rfl)
        apply mem_textbookEDomain_iff.mpr
        exact Exists.intro (natCode m)
          (And.intro hmOmega
            (Exists.intro (natCode n) (And.intro hnOmega hkey)))
  · intro hdomain
    have hrepresentation := mem_textbookEDomain_iff.mp hdomain
    cases hrepresentation with
    | intro m hmAnd =>
      have hm := hmAnd.1
      cases hmAnd.2 with
      | intro n hnAnd =>
        have hn := hnAnd.1
        have hkey := hnAnd.2
        have hmCode :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm
        cases hmCode with
        | intro mCode hmEq =>
          have hnCode :=
            (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp hn
          cases hnCode with
          | intro nCode hnEq =>
            subst m
            subst n
            exact Exists.intro mCode (Exists.intro nCode
              ((textbookEKeyDecode_eq_some_iff
                key mCode nCode).mpr hkey))

/-- Every element of the recursion domain has decoded coordinates in the
declared order `(recursiveCode, arity)`. -/
theorem exists_textbookEKeyDecode_of_mem_textbookEDomain
    {key : ZFSet.{u}} (hkey : key ∈ TextbookEDomain) :
    Exists fun m : Nat => Exists fun n : Nat =>
      And (textbookEKeyDecode key = some (m, n))
        (key = ZFSet.pair (natCode m) (natCode n)) := by
  have hdecoded :=
    (textbookEKeyDecode_exists_iff_mem_textbookEDomain key).mpr hkey
  cases hdecoded with
  | intro m hdecodedN =>
    cases hdecodedN with
    | intro n hdecode =>
      exact Exists.intro m (Exists.intro n
        (And.intro hdecode
          ((textbookEKeyDecode_eq_some_iff key m n).mp hdecode)))

end

end Constructible
