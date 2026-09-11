/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERowHistoryAlgebra
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERowEntryFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStepBranchesLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion

/-!
# Constructible row histories for the textbook E recursion

The history available before row `m` is the actual Kuratowski restriction
graph of the ambient recursive solution on `m x omega`.  This file proves,
by induction on the external natural number `m`, that this graph is an
element of `L`.

At the successor step, Replacement over the internal omega collects the
actual entries of the next row.  The recursion equation and the exact
predecessor-set computation identify that row with the corresponding
restriction of `textbookEByKey`.  Thus no external function graph is used
as an internal history witness.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

private theorem natCode_mem_textbookEOmega_rowHistory (m : Nat) :
    (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode m)).mpr ⟨m, rfl⟩

/-- On a key in row `m`, the ambient recursion equation uses exactly the
history restricted to `m x omega`. -/
private theorem textbookEByKey_eq_step_rowHistory
    (a : ZFSet.{u}) (m : Nat) {n : ZFSet.{u}}
    (hn : n ∈ textbookEOmegaZF) :
    textbookEByKey a (ZFSet.pair (natCode m) n) =
      textbookEStep a (ZFSet.pair (natCode m) n)
        (predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF)
          (textbookEByKey a)) := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    natCode_mem_textbookEOmega_rowHistory m
  have hkey :
      ZFSet.pair (natCode m : ZFSet.{u}) n ∈ TextbookEDomain :=
    (pair_mem_textbookEDomain_iff (natCode m) n).mpr ⟨hm, hn⟩
  have hpredecessors :
      ZFSet.prod (natCode m : ZFSet.{u}) textbookEOmegaZF =
        displayedPredecessors TextbookEDomain TextbookERelation
          textbookERelation_isWellFoundedSetLikeOn.2.2
          (ZFSet.pair (natCode m) n) :=
    eq_displayedPredecessors_of_isPredecessorSet
      textbookERelation_isWellFoundedSetLikeOn.2.2 hkey
      (textbookE_predecessorSet hm hn)
  rw [textbookEByKey_eq a hkey, ← hpredecessors]

namespace Model

local notation "LMem" => lCarrierMem

/-- The complete history before any standard row is an actual element of
`L`.  Its elements are precisely the Kuratowski graph pairs of
`textbookEByKey` whose first coordinate is below `m`. -/
theorem textbookEPredecessorRestrictionGraph_mem_L
    (a : LCarrier.{u}) (m : Nat) :
    predecessorRestrictionGraph
        (ZFSet.prod (natCode m) textbookEOmegaZF)
        (textbookEByKey a.1) ∈ L := by
  induction m with
  | zero =>
      rw [predecessorRestrictionGraph_textbookE_zero]
      exact empty_mem_L
  | succ m ih =>
      let historyZF : ZFSet.{u} :=
        predecessorRestrictionGraph
          (ZFSet.prod (natCode m) textbookEOmegaZF)
          (textbookEByKey a.1)
      let history : LCarrier.{u} := ⟨historyZF, ih⟩
      let mL : LCarrier.{u} := ⟨natCode m, natCode_mem_L m⟩
      have hstep :
          ∀ n : LCarrier.{u}, n.1 ∈ omegaLCarrier.1 →
            ExistsUnique fun output : LCarrier.{u} =>
              FOFormula.Satisfies LMem
                TextbookEFormula.textbookEStepFormula
                ![a, orderedPairLCarrier mL n, history, output] := by
        intro n hn
        have hmOmega :
            (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
          natCode_mem_textbookEOmega_rowHistory m
        have hkeyDomain :
            (orderedPairLCarrier mL n).1 ∈ TextbookEDomain := by
          apply (pair_mem_textbookEDomain_iff (natCode m) n.1).mpr
          exact ⟨hmOmega, hn⟩
        let output : LCarrier.{u} :=
          textbookEStepLCarrier a (orderedPairLCarrier mL n)
            history hkeyDomain
        refine ⟨output, ?_, ?_⟩
        · apply (satisfies_textbookEStepFormula_lCarrier_iff
            a (orderedPairLCarrier mL n) history output).mpr
          exact ⟨hkeyDomain, rfl⟩
        · intro other hother
          have hotherSem :=
            (satisfies_textbookEStepFormula_lCarrier_iff
              a (orderedPairLCarrier mL n) history other).mp hother
          apply Subtype.ext
          simpa only [output, textbookEStepLCarrier_val] using hotherSem.2
      rcases exists_textbookERowEntryFamily a history mL hstep with
        ⟨row, hrow⟩
      have hrowEq :
          row.1 =
            textbookERowRestrictionGraph m (textbookEByKey a.1) := by
        apply ZFSet.ext
        intro pair
        constructor
        · intro hpair
          let entry : LCarrier.{u} :=
            ⟨pair, mem_L_of_mem hpair row.2⟩
          rcases (hrow entry).mp hpair with
            ⟨n, hnOmega, hentryFormula⟩
          rcases (satisfies_textbookERowEntryFormula
              a history mL n entry).mp hentryFormula with
            ⟨key, output, hkey, houtputFormula, hentry⟩
          have houtput :=
            (satisfies_textbookEStepFormula_lCarrier_iff
              a key history output).mp houtputFormula
          have hrecursion :=
            textbookEByKey_eq_step_rowHistory a.1 m hnOmega
          have houtputEq :
              output.1 =
                textbookEByKey a.1
                  (ZFSet.pair (natCode m) n.1) := by
            calc
              output.1 =
                  textbookEStep a.1 key.1 history.1 :=
                houtput.2
              _ = textbookEStep a.1
                    (ZFSet.pair (natCode m) n.1)
                    (predecessorRestrictionGraph
                      (ZFSet.prod (natCode m) textbookEOmegaZF)
                      (textbookEByKey a.1)) := by
                  rw [hkey]
              _ = textbookEByKey a.1
                    (ZFSet.pair (natCode m) n.1) :=
                hrecursion.symm
          apply mem_textbookERowRestrictionGraph_iff.mpr
          refine ⟨n.1, hnOmega, ?_⟩
          simpa only [hkey, houtputEq] using hentry.symm
        · intro hpair
          rcases mem_textbookERowRestrictionGraph_iff.mp hpair with
            ⟨n, hnOmega, hpair⟩
          have hnL : n ∈ L :=
            mem_L_of_mem hnOmega omegaLCarrier.2
          let nL : LCarrier.{u} := ⟨n, hnL⟩
          have hmOmega :
              (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
            natCode_mem_textbookEOmega_rowHistory m
          have hkeyDomain :
              (orderedPairLCarrier mL nL).1 ∈ TextbookEDomain := by
            apply (pair_mem_textbookEDomain_iff (natCode m) n).mpr
            exact ⟨hmOmega, hnOmega⟩
          let output : LCarrier.{u} :=
            textbookEStepLCarrier a (orderedPairLCarrier mL nL)
              history hkeyDomain
          let entry : LCarrier.{u} :=
            orderedPairLCarrier (orderedPairLCarrier mL nL) output
          have houtputFormula :
              FOFormula.Satisfies LMem
                TextbookEFormula.textbookEStepFormula
                ![a, orderedPairLCarrier mL nL, history, output] := by
            apply (satisfies_textbookEStepFormula_lCarrier_iff
              a (orderedPairLCarrier mL nL) history output).mpr
            exact ⟨hkeyDomain, rfl⟩
          have hentryFormula :
              FOFormula.Satisfies LMem textbookERowEntryFormula
                ![a, history, mL, nL, entry] := by
            apply (satisfies_textbookERowEntryFormula
              a history mL nL entry).mpr
            exact ⟨orderedPairLCarrier mL nL, output, rfl,
              houtputFormula, rfl⟩
          have hentryMem : entry.1 ∈ row.1 :=
            (hrow entry).mpr ⟨nL, hnOmega, hentryFormula⟩
          have hrecursion :=
            textbookEByKey_eq_step_rowHistory a.1 m hnOmega
          have hentryEq :
              entry.1 =
                ZFSet.pair
                  (ZFSet.pair (natCode m) n)
                  (textbookEByKey a.1
                    (ZFSet.pair (natCode m) n)) := by
            change
              ZFSet.pair (ZFSet.pair (natCode m) n)
                  (textbookEStep a.1
                    (ZFSet.pair (natCode m) n) history.1) =
                ZFSet.pair (ZFSet.pair (natCode m) n)
                  (textbookEByKey a.1
                    (ZFSet.pair (natCode m) n))
            rw [show history.1 =
                predecessorRestrictionGraph
                  (ZFSet.prod (natCode m) textbookEOmegaZF)
                  (textbookEByKey a.1) by rfl,
              ← hrecursion]
          rw [← hpair]
          simpa only [hentryEq] using hentryMem
      rw [predecessorRestrictionGraph_textbookE_succ, ← hrowEq]
      exact union_mem_L ih row.2

end Model

end

end Constructible
