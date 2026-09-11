/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDefinability
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement

/-!
# Exact semantics of the textbook Df formula over L

The exact internal semantics of the textbook enumeration `E` is used with
Replacement over the genuine internal omega.  This first proves that every
fixed-arity set `textbookDfZF a n` belongs to `L`, and then identifies the
public first-order graph for `Df` with that set over `LCarrier`.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

/-! ## Replacement-range semantics over LCarrier -/

@[simp]
theorem satisfies_replacementRangeFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (a y : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementRangeFormula phi)
        (snoc (snoc params a) y) <->
      exists x : LCarrier.{u}, x.1 ∈ a.1 /\
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y) := by
  simp only [replacementRangeFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  apply exists_congr
  intro x
  change
    (LMem (snoc (snoc (snoc params a) y) x (Fin.last (n + 2)))
          (snoc (snoc (snoc params a) y) x
            (Fin.last n).castSucc.castSucc) /\
        FOFormula.Satisfies LMem phi
          (fun i => snoc (snoc (snoc params a) y) x
            (replacementRangeRename i))) <-> _
  simp only [snoc_last, snoc_castSucc, comp_replacementRangeRename]

/-! ## The fixed-arity Df set is constructible -/

private theorem textbookEFormula_assignment
    (a n code output : LCarrier.{u}) :
    snoc (snoc ![a, n] code) output = ![a, n, code, output] := by
  funext i
  fin_cases i <;> rfl

/-- Every fixed-arity textbook definability set is an actual member of `L`.
The witness is the Replacement range of the exact `E` formula on omega. -/
theorem textbookDfZF_mem_L (a : LCarrier.{u}) (n : Nat) :
    textbookDfZF a.1 n ∈ L := by
  let nL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let params : Tuple LCarrier.{u} 2 := ![a, nL]
  have hfun : forall code : LCarrier.{u},
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        ExistsUnique fun output : LCarrier.{u} =>
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            (snoc (snoc params code) output) := by
    intro code hcode
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
        hcode with ⟨m, hcodeValue⟩
    have hcodeEq :
        code = TextbookNatFormula.textbookNatCodeLCarrier m := by
      apply Subtype.ext
      exact hcodeValue
    subst code
    let output : LCarrier.{u} := textbookEZFLCarrier a n m
    refine ⟨output, ?_, ?_⟩
    · change FOFormula.Satisfies LMem
        TextbookEFormula.textbookEZFFormula
          (snoc (snoc params
            (TextbookNatFormula.textbookNatCodeLCarrier m)) output)
      rw [show snoc (snoc params
          (TextbookNatFormula.textbookNatCodeLCarrier m)) output =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, output] by
        simpa only [params, nL] using textbookEFormula_assignment
          a (TextbookNatFormula.textbookNatCodeLCarrier n)
            (TextbookNatFormula.textbookNatCodeLCarrier m) output]
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a output n m).mpr rfl
    · intro other hother
      apply Subtype.ext
      have hformula :
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m, other] := by
        rw [← textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
          (TextbookNatFormula.textbookNatCodeLCarrier m) other]
        simpa only [params, nL] using hother
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a other n m).mp hformula
  rcases exists_replacementLCarrier
      TextbookEFormula.textbookEZFFormula params omegaLCarrier hfun with
    ⟨range, hrange⟩
  have hrangeEq : range.1 = textbookDfZF a.1 n := by
    apply ZFSet.ext
    intro relation
    constructor
    · intro hrelationRange
      let relationL : LCarrier.{u} :=
        ⟨relation, mem_L_of_mem hrelationRange range.2⟩
      rcases (hrange relationL).mp hrelationRange with
        ⟨code, hcode, hformula⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
          hcode with ⟨m, hcodeValue⟩
      have hcodeEq :
          code = TextbookNatFormula.textbookNatCodeLCarrier m := by
        apply Subtype.ext
        exact hcodeValue
      subst code
      apply mem_textbookDfZF_iff_exists_textbookEZF.mpr
      refine ⟨m, ?_⟩
      have hformula' :
          FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m, relationL] := by
        rw [← textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
          (TextbookNatFormula.textbookNatCodeLCarrier m) relationL]
        simpa only [params, nL] using hformula
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relationL n m).mp hformula' |>.symm
    · intro hrelationDf
      rcases mem_textbookDfZF_iff_exists_textbookEZF.mp hrelationDf with
        ⟨m, hrelationValue⟩
      have hrelationL : relation ∈ L := by
        rw [← hrelationValue]
        exact textbookEZF_natCode_mem_L a.2 n m
      let relationCarrier : LCarrier.{u} := ⟨relation, hrelationL⟩
      apply (hrange relationCarrier).mpr
      let code : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier m
      refine ⟨code, ?_, ?_⟩
      · change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩
      · rw [show snoc (snoc params code) relationCarrier =
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier m,
              relationCarrier] by
          simpa only [params, nL, code] using textbookEFormula_assignment
            a (TextbookNatFormula.textbookNatCodeLCarrier n)
              (TextbookNatFormula.textbookNatCodeLCarrier m)
              relationCarrier]
        apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
          a relationCarrier n m).mpr
        exact hrelationValue.symm
  rw [← hrangeEq]
  exact range.2

/-- The fixed-arity Df set packaged as an `LCarrier`. -/
def textbookDfZFLCarrier (a : LCarrier.{u}) (n : Nat) : LCarrier.{u} :=
  ⟨textbookDfZF a.1 n, textbookDfZF_mem_L a n⟩

@[simp]
theorem textbookDfZFLCarrier_val (a : LCarrier.{u}) (n : Nat) :
    (textbookDfZFLCarrier a n).1 = textbookDfZF a.1 n :=
  rfl

/-! ## Exact semantics of the public Df formula -/

private theorem textbookDfRange_assignment
    (a n output omega relation : LCarrier.{u}) :
    (fun i => ![a, n, output, omega, relation]
      (TextbookDfFormula.textbookDfRangeParameters i)) =
      ![a, n, omega, relation] := by
  funext i
  fin_cases i <;> rfl

private theorem textbookDfRange_snoc_assignment
    (a n omega relation : LCarrier.{u}) :
    ![a, n, omega, relation] =
      snoc (snoc ![a, n] omega) relation := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
    (a output relation : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem
        (FOFormula.rename TextbookDfFormula.textbookDfRangeParameters
          (replacementRangeFormula TextbookEFormula.textbookEZFFormula))
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n, output,
          omegaLCarrier, relation] <->
      exists m : Nat,
        textbookEZF a.1 (natCode n) (natCode m) = relation.1 := by
  rw [FOFormula.satisfies_rename,
    textbookDfRange_assignment,
    textbookDfRange_snoc_assignment,
    satisfies_replacementRangeFormula_lCarrier]
  constructor
  · rintro ⟨code, hcode, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
        hcode with ⟨m, hcodeValue⟩
    have hcodeEq :
        code = TextbookNatFormula.textbookNatCodeLCarrier m := by
      apply Subtype.ext
      exact hcodeValue
    subst code
    refine ⟨m, ?_⟩
    have hformula' :
        FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, relation] := by
      rw [← textbookEFormula_assignment a
        (TextbookNatFormula.textbookNatCodeLCarrier n)
        (TextbookNatFormula.textbookNatCodeLCarrier m) relation]
      exact hformula
    exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
      a relation n m).mp hformula' |>.symm
  · rintro ⟨m, hm⟩
    let code : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier m
    refine ⟨code, ?_, ?_⟩
    · change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode m)).mpr ⟨m, rfl⟩
    · rw [show snoc
          (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n] code)
          relation =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier m, relation] by
        simpa only [code] using textbookEFormula_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
            (TextbookNatFormula.textbookNatCodeLCarrier m) relation]
      apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relation n m).mpr
      exact hm.symm

private theorem satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem
        TextbookDfFormula.textbookDfMembersFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] <->
      output.1 = textbookDfZF a.1 n := by
  rw [TextbookDfFormula.textbookDfMembersFormula,
    FOFormula.satisfies_all]
  constructor
  · intro hall
    apply ZFSet.ext
    intro relation
    constructor
    · intro hrelationOutput
      let relationL : LCarrier.{u} :=
        ⟨relation, mem_L_of_mem hrelationOutput output.2⟩
      have hbody := hall relationL
      have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] relationL =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationL] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment, FOFormula.satisfies_biimp] at hbody
      change (relationL.1 ∈ output.1 <->
        FOFormula.Satisfies LMem
          (FOFormula.rename
            TextbookDfFormula.textbookDfRangeParameters
            (replacementRangeFormula
              TextbookEFormula.textbookEZFFormula))
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationL]) at hbody
      have hiff : relationL.1 ∈ output.1 <->
          exists m : Nat,
            textbookEZF a.1 (natCode n) (natCode m) = relationL.1 :=
        hbody.trans
          (satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
            a output relationL n)
      exact mem_textbookDfZF_iff_exists_textbookEZF.mpr
        (hiff.mp hrelationOutput)
    · intro hrelationDf
      have hrelationL : relation ∈ L :=
        mem_L_of_mem hrelationDf (textbookDfZF_mem_L a n)
      let relationCarrier : LCarrier.{u} := ⟨relation, hrelationL⟩
      have hbody := hall relationCarrier
      have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] relationCarrier =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationCarrier] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment, FOFormula.satisfies_biimp] at hbody
      change (relationCarrier.1 ∈ output.1 <->
        FOFormula.Satisfies LMem
          (FOFormula.rename
            TextbookDfFormula.textbookDfRangeParameters
            (replacementRangeFormula
              TextbookEFormula.textbookEZFFormula))
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier, relationCarrier]) at hbody
      have hiff : relationCarrier.1 ∈ output.1 <->
          exists m : Nat,
            textbookEZF a.1 (natCode n) (natCode m) = relationCarrier.1 :=
        hbody.trans
          (satisfies_textbookDfRangeFormula_lCarrier_natCode_iff
            a output relationCarrier n)
      exact hiff.mpr
        (mem_textbookDfZF_iff_exists_textbookEZF.mp hrelationDf)
  · intro houtput relation
    have hassignment :
        snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] relation =
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier, relation] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment, FOFormula.satisfies_biimp]
    change (relation.1 ∈ output.1 <-> _)
    rw [satisfies_textbookDfRangeFormula_lCarrier_natCode_iff]
    rw [houtput, mem_textbookDfZF_iff_exists_textbookEZF]

/-- Exact `LCarrier` semantics of the public Df graph at standard codes. -/
@[simp]
theorem satisfies_textbookDfZFFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem TextbookDfFormula.textbookDfZFFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n, output] <->
      output.1 = textbookDfZF a.1 n := by
  rw [TextbookDfFormula.textbookDfZFFormula]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homega, _hnOmega, hmembers⟩
    have homegaEq : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omega)).mp homega
    subst omega
    have hassignment :
        snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omegaLCarrier =
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output, omegaLCarrier] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment] at hmembers
    exact (satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
      a output n).mp hmembers
  · intro houtput
    refine ⟨omegaLCarrier, ?_, ?_, ?_⟩
    · exact (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          output] omegaLCarrier)).mpr rfl
    · change (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · have hassignment :
          snoc ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output] omegaLCarrier =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            output, omegaLCarrier] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment]
      exact (satisfies_textbookDfMembersFormula_lCarrier_natCode_iff
        a output n).mpr houtput

/-- Exact semantics on arbitrary set-coded indices. -/
@[simp]
theorem satisfies_textbookDfZFFormula_lCarrier_iff
    (a index output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDfFormula.textbookDfZFFormula
        ![a, index, output] <->
      index.1 ∈ textbookEOmegaZF /\
        output.1 = textbookDfCodeZF a.1 index.1 := by
  constructor
  · intro hformula
    have hraw := hformula
    rw [TextbookDfFormula.textbookDfZFFormula] at hraw
    simp only [FOFormula.Satisfies] at hraw
    rcases hraw with ⟨omega, homega, hindexOmega, _hmembers⟩
    have homegaEq : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 3)
        (snoc ![a, index, output] omega)).mp homega
    subst omega
    change index.1 ∈ textbookEOmegaZF at hindexOmega
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindexOmega with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    refine ⟨hindexOmega, ?_⟩
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookDfCodeZF_natCode] using
        (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
          a output n).mp hformula
  · rintro ⟨hindexOmega, houtput⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindexOmega with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    apply (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
      a output n).mpr
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookDfCodeZF_natCode] using houtput

end Model

end

end Constructible
