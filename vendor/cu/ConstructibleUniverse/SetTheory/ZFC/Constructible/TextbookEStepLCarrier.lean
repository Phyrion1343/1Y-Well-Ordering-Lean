/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible

/-!
# The textbook E step over the constructible universe

This file begins the class-model version of the textbook `E` recursion by
proving that its one-step functional preserves constructibility.  The proof
follows the five clauses of the definition.  In particular, the history
lookup is treated as the actual total operation `uniqueGraphLookupZF`; it is
not replaced by an external choice function.

The exact `LCarrier` semantics of `textbookEStepFormula` is developed below
this closure layer.  The full recursion-value formula additionally requires
the set-like relation and local-solution construction over `LCarrier`; those
are separate obligations.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Closure of the total history lookup -/

/-- The total unique-value lookup of two constructible sets is constructible.
If the graph has a unique value at the key, that value is a component of a
Kuratowski pair belonging to the graph.  Otherwise the lookup is empty. -/
theorem uniqueGraphLookupZF_mem_L
    {graph key : ZFSet.{u}} (hgraph : graph ∈ L) (_hkey : key ∈ L) :
    uniqueGraphLookupZF graph key ∈ L := by
  by_cases hunique : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
  · rcases hunique with ⟨value, hvalue, hvalueUnique⟩
    rw [uniqueGraphLookupZF_eq_of_unique hvalue hvalueUnique]
    have hpairL : ZFSet.pair key value ∈ L :=
      mem_L_of_mem hvalue hgraph
    have hunorderedPair : ({key, value} : ZFSet.{u}) ∈
        ZFSet.pair key value := by
      simp [ZFSet.pair]
    have hunorderedPairL : ({key, value} : ZFSet.{u}) ∈ L :=
      mem_L_of_mem hunorderedPair hpairL
    exact mem_L_of_mem (by simp) hunorderedPairL
  · rw [uniqueGraphLookupZF_eq_empty_of_not_unique hunique]
    exact empty_mem_L

/-! ## Closure of the complete E step -/

/-- The textbook recursion functional maps a constructible parameter and a
constructible history to a constructible value at every genuine key. -/
theorem textbookEStep_mem_L
    {a key history : ZFSet.{u}} (ha : a ∈ L)
    (hhistory : history ∈ L)
    (hkeyDomain : key ∈ TextbookEDomain) :
    textbookEStep a key history ∈ L := by
  rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
    ⟨m, n, hdecode, _hkeyEq⟩
  unfold textbookEStep
  rw [hdecode]
  simp only
  cases hcode : textbookEDecode m with
  | none =>
      exact empty_mem_L
  | some fields =>
      rcases fields with ⟨i, j, tag⟩
      cases tag with
      | zero =>
          simp only
          split_ifs
          · rw [textbookDInCodeZF_natCode]
            exact textbookDInZF_mem_L ha n i j
          · exact empty_mem_L
      | succ tag =>
          cases tag with
          | zero =>
              simp only
              split_ifs
              · rw [textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_L ha n i j
              · exact empty_mem_L
          | succ tag =>
              cases tag with
              | zero =>
                  simp only
                  have hlookup :
                      uniqueGraphLookupZF history
                          (ZFSet.pair (natCode i) (natCode n)) ∈ L :=
                    uniqueGraphLookupZF_mem_L hhistory
                      (orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n))
                  exact relativeDifferenceZF_mem_L
                    (textbookTupleSpace_mem_L ha n) hlookup
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp only
                      have hleft :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode i) (natCode n)) ∈ L :=
                        uniqueGraphLookupZF_mem_L hhistory
                          (orderedPair_mem_L
                            (natCode_mem_L i) (natCode_mem_L n))
                      have hright :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode j) (natCode n)) ∈ L :=
                        uniqueGraphLookupZF_mem_L hhistory
                          (orderedPair_mem_L
                            (natCode_mem_L j) (natCode_mem_L n))
                      exact intersectionZF_mem_L hleft hright
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp only
                          have hrelation :
                              uniqueGraphLookupZF history
                                  (ZFSet.pair (natCode i)
                                    (natCode (n + 1))) ∈ L :=
                            uniqueGraphLookupZF_mem_L hhistory
                              (orderedPair_mem_L
                                (natCode_mem_L i) (natCode_mem_L (n + 1)))
                          rw [textbookExistsProjCodeZF_natCode]
                          exact textbookExistsProjZF_mem_L ha hrelation n
                      | succ tag =>
                          exact empty_mem_L

namespace Model

/-- The one-step value packaged as an element of `LCarrier`. -/
def textbookEStepLCarrier
    (a key history : LCarrier.{u}) (hkeyDomain : key.1 ∈ TextbookEDomain) :
    LCarrier.{u} :=
  ⟨textbookEStep a.1 key.1 history.1,
    textbookEStep_mem_L a.2 history.2 hkeyDomain⟩

@[simp]
theorem textbookEStepLCarrier_val
    (a key history : LCarrier.{u}) (hkeyDomain : key.1 ∈ TextbookEDomain) :
    (textbookEStepLCarrier a key history hkeyDomain).1 =
      textbookEStep a.1 key.1 history.1 :=
  rfl

end Model

end

end Constructible
