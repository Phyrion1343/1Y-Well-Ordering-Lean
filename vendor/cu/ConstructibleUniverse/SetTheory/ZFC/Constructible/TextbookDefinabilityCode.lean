/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDefinability

/-!
# Set-coded indices for the textbook definability operations

The core definitions in `TextbookDefinability` use Lean natural numbers for
their finite arities and indices.  The textbook absoluteness argument also
needs ambient, meta-level total functions whose arguments are sets.  This
file supplies that intermediate, set-coded interface.  It does not yet supply
internal function graphs, first-order definitions, or absoluteness proofs.

Each arity, coordinate-index, or stage argument is decoded only when it is a
member of the standard von Neumann `omega`; the set and relation arguments
remain arbitrary.  Operations return the empty set when a coded argument is
invalid.  On standard codes the definitions reduce exactly to the
`Nat`-indexed core; no internal formula or absoluteness claim is made here.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Decoding standard natural-number sets -/

/-- Decode a member of the ambient standard von Neumann `omega`, and reject
every other set.  The chosen witness is unique by injectivity of `natCode`.
This meta-level decoder must not be used as an internal definition in a
nontransitive model; later absoluteness arguments explicitly prove that a
transitive ZF model's internally defined omega is this ambient omega. -/
noncomputable def textbookNatDecode (x : ZFSet.{u}) : Option Nat :=
  by
    classical
    exact if hx : x ∈ Ordinal.omega0.toZFSet then
      some (Classical.choose
        (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx))
    else
      none

theorem textbookNatDecode_eq_some_iff {x : ZFSet.{u}} {n : Nat} :
    textbookNatDecode x = some n ↔ x = natCode n := by
  unfold textbookNatDecode
  split_ifs with hx
  · let k := Classical.choose
      (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx)
    have hk : x = natCode k :=
      Classical.choose_spec
        (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx)
    constructor
    · intro h
      have hkn : k = n := Option.some.inj h
      simpa only [hkn] using hk
    · intro hxn
      apply congrArg some
      apply natCode_injective
      rw [← hk, hxn]
  · constructor
    · intro h
      cases h
    · intro hxn
      exfalso
      apply hx
      rw [hxn]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩

@[simp]
theorem textbookNatDecode_natCode (n : Nat) :
    textbookNatDecode (natCode n : ZFSet.{u}) = some n :=
  textbookNatDecode_eq_some_iff.mpr rfl

theorem textbookNatDecode_eq_none_iff {x : ZFSet.{u}} :
    textbookNatDecode x = none ↔ x ∉ Ordinal.omega0.toZFSet := by
  constructor
  · intro hdecode hx
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
      ⟨n, rfl⟩
    simp at hdecode
  · intro hx
    simp only [textbookNatDecode]
    exact dif_neg hx

theorem textbookNatDecode_isSome_iff {x : ZFSet.{u}} :
    (textbookNatDecode x).isSome ↔ x ∈ Ordinal.omega0.toZFSet := by
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨n, hn⟩
    have hx : x = natCode n := textbookNatDecode_eq_some_iff.mp hn
    rw [hx]
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩
  · intro hx
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
      ⟨n, rfl⟩
    simp

/-! ## Total set-coded operations -/

/-- The finite power `a^n`, totalized to the empty set off `omega`. -/
noncomputable def textbookTupleSpaceCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookTupleSpace a n'
  | none => ∅

/-- The set-coded version of `D_in(a,n,i,j)`. -/
noncomputable def textbookDInCodeZF
    (a n i j : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n, textbookNatDecode i, textbookNatDecode j with
  | some n', some i', some j' => textbookDInZF a n' i' j'
  | _, _, _ => ∅

/-- The set-coded version of `D_eq(a,n,i,j)`. -/
noncomputable def textbookDEqCodeZF
    (a n i j : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n, textbookNatDecode i, textbookNatDecode j with
  | some n', some i', some j' => textbookDEqZF a n' i' j'
  | _, _, _ => ∅

/-- The set-coded existential projection. -/
noncomputable def textbookExistsProjCodeZF
    (a n r : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookExistsProjZF a n' r
  | none => ∅

/-- The set-coded atomic stage `D(0,a,n)`. -/
noncomputable def textbookDZeroCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookDZeroZF a n'
  | none => ∅

/-- The set-coded finite stage `D(k,a,n)`. -/
noncomputable def textbookDStageCodeZF
    (a k n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode k, textbookNatDecode n with
  | some k', some n' => textbookDStageZF a k' n'
  | _, _ => ∅

/-- The set-coded union `Df(a,n)` of all finite stages. -/
noncomputable def textbookDfCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookDfZF a n'
  | none => ∅

@[simp]
theorem textbookTupleSpaceCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookTupleSpaceCodeZF a (natCode n) = textbookTupleSpace a n := by
  simp [textbookTupleSpaceCodeZF]

@[simp]
theorem textbookDInCodeZF_natCode
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDInCodeZF a (natCode n) (natCode i) (natCode j) =
      textbookDInZF a n i j := by
  simp [textbookDInCodeZF]

@[simp]
theorem textbookDEqCodeZF_natCode
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) =
      textbookDEqZF a n i j := by
  simp [textbookDEqCodeZF]

@[simp]
theorem textbookExistsProjCodeZF_natCode
    (a r : ZFSet.{u}) (n : Nat) :
    textbookExistsProjCodeZF a (natCode n) r =
      textbookExistsProjZF a n r := by
  simp [textbookExistsProjCodeZF]

@[simp]
theorem textbookDZeroCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookDZeroCodeZF a (natCode n) = textbookDZeroZF a n := by
  simp [textbookDZeroCodeZF]

@[simp]
theorem textbookDStageCodeZF_natCode
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageCodeZF a (natCode k) (natCode n) =
      textbookDStageZF a k n := by
  simp [textbookDStageCodeZF]

@[simp]
theorem textbookDfCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookDfCodeZF a (natCode n) = textbookDfZF a n := by
  simp [textbookDfCodeZF]

@[simp]
theorem textbookTupleSpaceCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookTupleSpaceCodeZF a n = ∅ := by
  simp [textbookTupleSpaceCodeZF,
    textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_arity_not_mem_omega
    {a n i j : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_left_not_mem_omega
    {a n i j : ZFSet.{u}} (hi : i ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hi]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_right_not_mem_omega
    {a n i j : ZFSet.{u}} (hj : j ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hj]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_arity_not_mem_omega
    {a n i j : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_left_not_mem_omega
    {a n i j : ZFSet.{u}} (hi : i ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hi]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_right_not_mem_omega
    {a n i j : ZFSet.{u}} (hj : j ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hj]

@[simp]
theorem textbookExistsProjCodeZF_eq_empty_of_not_mem_omega
    {a n r : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookExistsProjCodeZF a n r = ∅ := by
  simp [textbookExistsProjCodeZF,
    textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDZeroCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDZeroCodeZF a n = ∅ := by
  simp [textbookDZeroCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDStageCodeZF_eq_empty_of_stage_not_mem_omega
    {a k n : ZFSet.{u}} (hk : k ∉ Ordinal.omega0.toZFSet) :
    textbookDStageCodeZF a k n = ∅ := by
  simp [textbookDStageCodeZF, textbookNatDecode_eq_none_iff.mpr hk]

@[simp]
theorem textbookDStageCodeZF_eq_empty_of_arity_not_mem_omega
    {a k n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDStageCodeZF a k n = ∅ := by
  simp [textbookDStageCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDfCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDfCodeZF a n = ∅ := by
  simp [textbookDfCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

end Constructible
