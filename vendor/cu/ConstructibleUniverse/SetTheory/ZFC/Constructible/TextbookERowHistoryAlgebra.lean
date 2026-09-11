/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RestrictionGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomain

/-!
# Row algebra for the textbook E history

The recursion defining the textbook enumeration `E(a,n,m)` is organized in
rows.  Before row `m` is evaluated, its predecessor domain is the actual
set-coded product `m x omega`.  Passing from `m` to `m + 1` adjoins exactly
the row `{m} x omega`.

This file records that decomposition directly for actual Kuratowski
restriction graphs.  Every domain and graph below is a `ZFSet`; external
`Set ZFSet` predicates are not used as history objects.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Restriction graphs over unions -/

/-- Restricting a function to an internal union is the internal union of
the two restriction graphs. -/
theorem predecessorRestrictionGraph_union
    (left right : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph (left ∪ right) f =
      predecessorRestrictionGraph left f ∪
        predecessorRestrictionGraph right f := by
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨x, hx, rfl⟩
    rcases ZFSet.mem_union.mp hx with hxLeft | hxRight
    · exact ZFSet.mem_union.mpr
        (Or.inl (pair_mem_predecessorRestrictionGraph f hxLeft))
    · exact ZFSet.mem_union.mpr
        (Or.inr (pair_mem_predecessorRestrictionGraph f hxRight))
  · intro hpair
    rcases ZFSet.mem_union.mp hpair with hpairLeft | hpairRight
    · rcases mem_predecessorRestrictionGraph_iff.mp hpairLeft with
        ⟨x, hx, rfl⟩
      exact pair_mem_predecessorRestrictionGraph f
        (ZFSet.mem_union.mpr (Or.inl hx))
    · rcases mem_predecessorRestrictionGraph_iff.mp hpairRight with
        ⟨x, hx, rfl⟩
      exact pair_mem_predecessorRestrictionGraph f
        (ZFSet.mem_union.mpr (Or.inr hx))

/-! ## The set-coded row -/

/-- The actual set-coded `m`-th row `{m} x omega`. -/
def textbookERowDomainZF (m : Nat) : ZFSet.{u} :=
  ZFSet.prod ({natCode m} : ZFSet.{u}) textbookEOmegaZF

@[simp]
theorem mem_textbookERowDomainZF_iff
    {m : Nat} {key : ZFSet.{u}} :
    key ∈ textbookERowDomainZF m ↔
      ∃ n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
        key = ZFSet.pair (natCode m) n := by
  rw [textbookERowDomainZF, ZFSet.mem_prod]
  constructor
  · rintro ⟨i, hi, n, hn, hkey⟩
    have hiEq : i = (natCode m : ZFSet.{u}) := by
      simpa only [ZFSet.mem_singleton] using hi
    subst i
    exact ⟨n, hn, hkey⟩
  · rintro ⟨n, hn, hkey⟩
    exact ⟨natCode m, by simp, n, hn, hkey⟩

/-- The actual Kuratowski graph contributed by row `m`. -/
def textbookERowRestrictionGraph
    (m : Nat) (f : ZFSet.{u} -> ZFSet.{u}) : ZFSet.{u} :=
  predecessorRestrictionGraph (textbookERowDomainZF m) f

@[simp]
theorem mem_textbookERowRestrictionGraph_iff
    {m : Nat} {f : ZFSet.{u} -> ZFSet.{u}} {pair : ZFSet.{u}} :
    pair ∈ textbookERowRestrictionGraph m f ↔
      ∃ n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
        ZFSet.pair
          (ZFSet.pair (natCode m) n)
          (f (ZFSet.pair (natCode m) n)) = pair := by
  rw [textbookERowRestrictionGraph,
    mem_predecessorRestrictionGraph_iff]
  constructor
  · rintro ⟨key, hkey, rfl⟩
    rcases mem_textbookERowDomainZF_iff.mp hkey with
      ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨ZFSet.pair (natCode m) n,
      mem_textbookERowDomainZF_iff.mpr ⟨n, hn, rfl⟩, rfl⟩

/-! ## Zero and successor histories -/

/-- The predecessor domain before row zero is empty. -/
@[simp]
theorem textbookEPredecessorDomain_zero :
    ZFSet.prod (natCode 0 : ZFSet.{u}) textbookEOmegaZF = ∅ := by
  apply ZFSet.ext
  intro key
  constructor
  · intro hkey
    rcases ZFSet.mem_prod.mp hkey with ⟨i, hi, _n, _hn, _hkey⟩
    have hiEmpty : i ∈ (∅ : ZFSet.{u}) := by
      simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero] using hi
    exact (ZFSet.notMem_empty i hiEmpty).elim
  · intro hkey
    exact (ZFSet.notMem_empty key hkey).elim

/-- The predecessor restriction graph before row zero is empty. -/
@[simp]
theorem predecessorRestrictionGraph_textbookE_zero
    (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode 0) textbookEOmegaZF) f =
      ∅ := by
  rw [textbookEPredecessorDomain_zero]
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨x, hx, _⟩
    exact (ZFSet.notMem_empty x hx).elim
  · intro hpair
    exact (ZFSet.notMem_empty pair hpair).elim

/-- The predecessor domain for row `m + 1` is the old predecessor domain
plus the whole `m`-th row. -/
theorem textbookEPredecessorDomain_succ (m : Nat) :
    ZFSet.prod (natCode (m + 1) : ZFSet.{u}) textbookEOmegaZF =
      ZFSet.prod (natCode m) textbookEOmegaZF ∪
        textbookERowDomainZF m := by
  apply ZFSet.ext
  intro key
  constructor
  · intro hkey
    rcases ZFSet.mem_prod.mp hkey with ⟨i, hi, n, hn, hkeyEq⟩
    rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff] at hi
    rcases hi with hiEq | hiOld
    · apply ZFSet.mem_union.mpr
      right
      apply mem_textbookERowDomainZF_iff.mpr
      exact ⟨n, hn, hkeyEq.trans (by rw [hiEq])⟩
    · apply ZFSet.mem_union.mpr
      left
      exact ZFSet.mem_prod.mpr ⟨i, hiOld, n, hn, hkeyEq⟩
  · intro hkey
    rcases ZFSet.mem_union.mp hkey with hkeyOld | hkeyRow
    · rcases ZFSet.mem_prod.mp hkeyOld with
        ⟨i, hi, n, hn, hkeyEq⟩
      apply ZFSet.mem_prod.mpr
      refine ⟨i, ?_, n, hn, hkeyEq⟩
      rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff]
      exact Or.inr hi
    · rcases mem_textbookERowDomainZF_iff.mp hkeyRow with
        ⟨n, hn, hkeyEq⟩
      apply ZFSet.mem_prod.mpr
      refine ⟨natCode m, ?_, n, hn, hkeyEq⟩
      rw [natCode_succ_eq_insert, ZFSet.mem_insert_iff]
      exact Or.inl rfl

/-- Passing to row `m + 1` extends the old restriction graph by exactly the
actual graph contributed by row `m`. -/
theorem predecessorRestrictionGraph_textbookE_succ
    (m : Nat) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode (m + 1)) textbookEOmegaZF) f =
      predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF) f ∪
        textbookERowRestrictionGraph m f := by
  rw [textbookEPredecessorDomain_succ,
    predecessorRestrictionGraph_union,
    textbookERowRestrictionGraph]

end

end Constructible
