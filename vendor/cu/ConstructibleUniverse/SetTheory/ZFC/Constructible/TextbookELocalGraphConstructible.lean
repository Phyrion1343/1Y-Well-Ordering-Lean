/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERowHistoryConstructible
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalDomainLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible

/-!
# Constructible local graphs for the textbook E recursion

The local graph at `<m,n>` is the restriction of `textbookEByKey` to the
literal textbook local domain `{<m,n>} union (m x omega)`.  This file proves
that the whole graph is an actual element of `L`.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- Restriction to a one-point domain is the corresponding one-point graph. -/
theorem predecessorRestrictionGraph_singleton
    (x : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) :
    predecessorRestrictionGraph ({x} : ZFSet.{u}) f =
      ({ZFSet.pair x (f x)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro pair
  constructor
  · intro hpair
    rcases mem_predecessorRestrictionGraph_iff.mp hpair with
      ⟨source, hsource, hsourcePair⟩
    have hsourceEq : source = x := by
      simpa only [ZFSet.mem_singleton] using hsource
    subst source
    rw [ZFSet.mem_singleton]
    exact hsourcePair.symm
  · intro hpair
    have hpairEq : pair = ZFSet.pair x (f x) := by
      simpa only [ZFSet.mem_singleton] using hpair
    apply mem_predecessorRestrictionGraph_iff.mpr
    exact ⟨x, by simp, hpairEq.symm⟩

namespace Model

/-- The literal restriction graph on the local domain of a standard key is
an actual member of `L`. -/
theorem textbookELocalRestrictionGraph_mem_L
    (a : LCarrier.{u}) (m n : Nat) :
    predecessorRestrictionGraph
        (textbookELocalDomainLCarrier m n).1
        (textbookEByKey a.1) ∈ L := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  have hn : (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)
  have hdomain := textbookE_localRecursionDomain_eq
    (m := (natCode m : ZFSet.{u}))
    (n := (natCode n : ZFSet.{u})) hm hn
  have hhistory := textbookEPredecessorRestrictionGraph_mem_L a m
  have hkeyL : ZFSet.pair (natCode m) (natCode n) ∈ L :=
    orderedPair_mem_L (natCode_mem_L m) (natCode_mem_L n)
  have hvalueL :
      textbookEByKey a.1 (ZFSet.pair (natCode m) (natCode n)) ∈ L := by
    simpa only [textbookEZF] using
      (textbookEZF_natCode_mem_L a.2 n m)
  have hentryL :
      ZFSet.pair
          (ZFSet.pair (natCode m) (natCode n))
          (textbookEByKey a.1
            (ZFSet.pair (natCode m) (natCode n))) ∈ L :=
    orderedPair_mem_L hkeyL hvalueL
  rw [textbookELocalDomainLCarrier_val, hdomain, ZFSet.insert_eq,
    predecessorRestrictionGraph_union,
    predecessorRestrictionGraph_singleton]
  exact union_mem_L (singleton_mem_L hentryL) hhistory

/-- The canonical local graph, packaged as an actual `LCarrier`. -/
def textbookELocalGraphLCarrier
    (a : LCarrier.{u}) (m n : Nat) : LCarrier.{u} :=
  ⟨predecessorRestrictionGraph
      (textbookELocalDomainLCarrier m n).1
      (textbookEByKey a.1),
    textbookELocalRestrictionGraph_mem_L a m n⟩

@[simp]
theorem textbookELocalGraphLCarrier_val
    (a : LCarrier.{u}) (m n : Nat) :
    (textbookELocalGraphLCarrier a m n).1 =
      predecessorRestrictionGraph
        (textbookELocalDomainLCarrier m n).1
        (textbookEByKey a.1) :=
  rfl

end Model

end

end Constructible
