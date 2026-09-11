/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEFormulaLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalSolutionDecodeLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalSolutionLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookELocalGraphConstructible

/-!
# Exact semantics of the textbook E formula over L

The public first-order formula for the textbook enumeration is now proved
equivalent, over `LCarrier`, to the original recursively defined function.
The reverse implication uses the actual constructible local graph; the
forward implication decodes any formula witness and applies textbook local
solution agreement.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

/-- Exact semantics at externally indexed standard natural-number codes. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n m : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier m, output] <->
      output.1 = textbookEZF a.1 (natCode n) (natCode m) := by
  let nL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let mL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier m
  have hkey : orderedPairLCarrier mL nL =
      textbookEKeyLCarrier m n := by
    apply Subtype.ext
    rfl
  have hkeyVal : ZFSet.pair mL.1 nL.1 =
      (textbookEKeyLCarrier m n).1 := by
    rw [← orderedPairLCarrier_val, hkey]
  have hsemantic :=
    satisfies_textbookEZFFormula_lCarrier_iff_localSolution
      a nL mL output
  change FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
      ![a, nL, mL, output] <-> _
  constructor
  · intro hformula
    rcases hsemantic.mp hformula with
      ⟨_homega, graph, hlocal, hpair⟩
    rw [hkey] at hlocal
    have hpair' :
        ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈ graph.1 := by
      simpa only [hkeyVal] using hpair
    have hvalue :=
      textbookEByKey_eq_of_satisfies_localSolution_lCarrier
        a graph output m n hlocal hpair'
    simpa only [textbookEKeyLCarrier_val, textbookEZF] using hvalue
  · intro hvalue
    have hnOmega : nL.1 ∈ textbookEOmegaZF := by
      apply (IndexedSequenceZF.mem_omega_iff_exists_natCode nL.1).mpr
      exact ⟨n, by simp only [nL,
        TextbookNatFormula.textbookNatCodeLCarrier_val]⟩
    have hmOmega : mL.1 ∈ textbookEOmegaZF := by
      apply (IndexedSequenceZF.mem_omega_iff_exists_natCode mL.1).mpr
      exact ⟨m, by simp only [mL,
        TextbookNatFormula.textbookNatCodeLCarrier_val]⟩
    let graph : LCarrier.{u} := textbookELocalGraphLCarrier a m n
    have hlocal :=
      textbookECanonicalLocalGraph_satisfies_localSolution
        a graph m n (by rfl)
    have htop : (textbookEKeyLCarrier m n).1 ∈
        (textbookELocalDomainLCarrier m n).1 := by
      change (textbookEKeyLCarrier m n).1 ∈
        localRecursionDomain TextbookEDomain TextbookERelation
          textbookERelation_hasSetPredecessorsOn
          (textbookEKeyLCarrier m n).1
      exact mem_localRecursionDomain_iff.mpr (Or.inl rfl)
    have hpair :
        ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈ graph.1 := by
      have hcanonical := pair_mem_predecessorRestrictionGraph
        (textbookEByKey a.1) htop
      have houtput : output.1 =
          textbookEByKey a.1 (textbookEKeyLCarrier m n).1 := by
        simpa only [textbookEKeyLCarrier_val, textbookEZF] using hvalue
      rw [← houtput] at hcanonical
      simpa only [graph, textbookELocalGraphLCarrier_val] using hcanonical
    apply hsemantic.mpr
    refine ⟨⟨hnOmega, hmOmega⟩, graph, ?_, ?_⟩
    · rw [hkey]
      exact hlocal
    · simpa only [hkeyVal] using hpair

/-- Full exact semantics for arbitrary `LCarrier` arguments.  Membership in
the standard internal omega supplies the unique external natural-number
codes used by the preceding theorem. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      (n.1 ∈ textbookEOmegaZF /\ m.1 ∈ textbookEOmegaZF) /\
        output.1 = textbookEZF a.1 n.1 m.1 := by
  constructor
  · intro hformula
    have homega :=
      (satisfies_textbookEZFFormula_lCarrier_iff_localSolution
        a n m output).mp hformula |>.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n.1).mp
        homega.1 with ⟨nCode, hnCode⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m.1).mp
        homega.2 with ⟨mCode, hmCode⟩
    have hn : n = TextbookNatFormula.textbookNatCodeLCarrier nCode :=
      Subtype.ext hnCode
    have hm : m = TextbookNatFormula.textbookNatCodeLCarrier mCode :=
      Subtype.ext hmCode
    subst n
    subst m
    have hvalue :=
      (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a output nCode mCode).mp hformula
    refine ⟨homega, ?_⟩
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using hvalue
  · rintro ⟨homega, hvalue⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n.1).mp
        homega.1 with ⟨nCode, hnCode⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m.1).mp
        homega.2 with ⟨mCode, hmCode⟩
    have hn : n = TextbookNatFormula.textbookNatCodeLCarrier nCode :=
      Subtype.ext hnCode
    have hm : m = TextbookNatFormula.textbookNatCodeLCarrier mCode :=
      Subtype.ext hmCode
    subst n
    subst m
    apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
      a output nCode mCode).mpr
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using hvalue

end Model

end

end Constructible
