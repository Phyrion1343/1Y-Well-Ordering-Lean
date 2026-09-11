/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDfFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections

/-!
# An internal injection from fixed-arity Df into omega

For a relation in `textbookDfZF a n`, select its least textbook `E` code.
Leastness is expressed by one first-order formula over `LCarrier`, and
Replacement constructs the actual Kuratowski graph in `L`.

The external definition `firstTextbookECode` is used only to prove existence
and identify the formula's unique output.  It is not used as the internal
function witness.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The least-code formula -/

/-- Select `[a,arity,code,relation]` from
`[a,arity,omega,relation,code]`. -/
def textbookEAtSelectedCodeRename : Fin 4 -> Fin 5 :=
  ![0, 1, 4, 3]

/-- Under the bounded quantifier, select `[a,arity,earlier,relation]` from
`[a,arity,omega,relation,code,earlier]`. -/
def textbookEAtEarlierCodeRename : Fin 4 -> Fin 6 :=
  ![0, 1, Fin.last 5, 3]

/-- Layout `[a,arity,omega,relation,code]`: `code` is the least member of
`omega` at which `E(a,arity,-)` outputs `relation`. -/
def leastTextbookECodeFormula : FOFormula 5 :=
  .conj
    (.mem (4 : Fin 5) (2 : Fin 5))
    (.conj
      (FOFormula.rename textbookEAtSelectedCodeRename
        TextbookEFormula.textbookEZFFormula)
      (FOFormula.boundedAll (4 : Fin 5)
        (.neg (FOFormula.rename textbookEAtEarlierCodeRename
          TextbookEFormula.textbookEZFFormula))))

private theorem comp_textbookEAtSelectedCodeRename
    (a arity omega relation code : LCarrier.{u}) :
    (fun i => ![a, arity, omega, relation, code]
      (textbookEAtSelectedCodeRename i)) =
      ![a, arity, code, relation] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_textbookEAtEarlierCodeRename
    (a arity omega relation code earlier : LCarrier.{u}) :
    (fun i => snoc ![a, arity, omega, relation, code] earlier
      (textbookEAtEarlierCodeRename i)) =
      ![a, arity, earlier, relation] := by
  funext i
  fin_cases i <;> rfl

/-- Direct semantics of the least-code formula. -/
@[simp]
theorem satisfies_leastTextbookECodeFormula
    (a arity omega relation code : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastTextbookECodeFormula
        ![a, arity, omega, relation, code] <->
      code.1 ∈ omega.1 /\
        FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
          ![a, arity, code, relation] /\
        forall earlier : LCarrier.{u}, earlier.1 ∈ code.1 ->
          Not (FOFormula.Satisfies LMem
            TextbookEFormula.textbookEZFFormula
            ![a, arity, earlier, relation]) := by
  simp only [leastTextbookECodeFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_boundedAll,
    comp_textbookEAtSelectedCodeRename,
    comp_textbookEAtEarlierCodeRename]
  change
    (code.1 ∈ omega.1 /\
      FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, arity, code, relation] /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ code.1 ->
        Not (FOFormula.Satisfies LMem
          TextbookEFormula.textbookEZFFormula
          ![a, arity, earlier, relation])) <-> _
  rfl

private theorem leastCode_assignment
    (a arity omega relation code : LCarrier.{u}) :
    snoc (snoc ![a, arity, omega] relation) code =
      ![a, arity, omega, relation, code] := by
  funext i
  fin_cases i <;> rfl

/-! ## Identification with the external least code -/

/-- On a genuine member of fixed-arity Df, the object-language least-code
formula has exactly the expected standard natural-number value. -/
theorem satisfies_leastTextbookECodeFormula_natCode_iff
    (a relation code : LCarrier.{u}) (n : Nat)
    (hrelation : relation.1 ∈ textbookDfZF a.1 n) :
    FOFormula.Satisfies LMem leastTextbookECodeFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          omegaLCarrier, relation, code] <->
      code.1 = natCode
        (firstTextbookECode a.1 n ⟨relation.1, hrelation⟩) := by
  let relationDf : ZFCarrier (textbookDfZF a.1 n) :=
    ⟨relation.1, hrelation⟩
  let first : Nat := firstTextbookECode a.1 n relationDf
  constructor
  · intro hformula
    rcases (satisfies_leastTextbookECodeFormula
      a (TextbookNatFormula.textbookNatCodeLCarrier n)
        omegaLCarrier relation code).mp hformula with
      ⟨hcodeOmega, hcodeFormula, hminimal⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode code.1).mp
        hcodeOmega with ⟨m, hcodeValue⟩
    have hcodeEq : code = TextbookNatFormula.textbookNatCodeLCarrier m := by
      apply Subtype.ext
      exact hcodeValue
    subst code
    have hm : textbookEZF a.1 (natCode n) (natCode m) = relation.1 := by
      exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relation n m).mp hcodeFormula |>.symm
    have hfirstLe : first <= m := by
      exact firstTextbookECode_minimal a.1 n relationDf hm
    have hmLe : m <= first := by
      by_contra hnot
      have hfirstLt : first < m := Nat.lt_of_not_ge hnot
      let earlier : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier first
      have hearlier : earlier.1 ∈
          (TextbookNatFormula.textbookNatCodeLCarrier m).1 := by
        change (natCode first : ZFSet.{u}) ∈ natCode m
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode first) m).mpr ⟨first, hfirstLt, rfl⟩
      have hnotEarlier := hminimal earlier hearlier
      apply hnotEarlier
      apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relation n first).mpr
      exact textbookEZF_firstTextbookECode a.1 n relationDf |>.symm
    have hmEq : m = first := Nat.le_antisymm hmLe hfirstLe
    rw [hmEq]
    exact TextbookNatFormula.textbookNatCodeLCarrier_val first
  · intro hcode
    have hcodeEq : code =
        TextbookNatFormula.textbookNatCodeLCarrier first := by
      apply Subtype.ext
      exact hcode.trans
        (TextbookNatFormula.textbookNatCodeLCarrier_val first).symm
    subst code
    apply (satisfies_leastTextbookECodeFormula
      a (TextbookNatFormula.textbookNatCodeLCarrier n)
        omegaLCarrier relation
          (TextbookNatFormula.textbookNatCodeLCarrier first)).mpr
    refine ⟨?_, ?_, ?_⟩
    · change (natCode first : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode first)).mpr ⟨first, rfl⟩
    · apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a relation n first).mpr
      exact textbookEZF_firstTextbookECode a.1 n relationDf |>.symm
    · intro earlier hearlier hformula
      rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
          earlier.1 first).mp hearlier with
        ⟨m, hmFirst, hearlierValue⟩
      have hearlierEq :
          earlier = TextbookNatFormula.textbookNatCodeLCarrier m := by
        apply Subtype.ext
        exact hearlierValue
      subst earlier
      have hm : textbookEZF a.1 (natCode n) (natCode m) = relation.1 := by
        exact (satisfies_textbookEZFFormula_lCarrier_natCode_iff
          a relation n m).mp hformula |>.symm
      have hfirstLe : first <= m :=
        firstTextbookECode_minimal a.1 n relationDf hm
      exact (Nat.not_le_of_lt hmFirst) hfirstLe

/-! ## The actual internal injection graph -/

/-- Replacement of the least-code formula produces a genuine internal
injection from `textbookDfZF a n` into the internal omega. -/
theorem injects_textbookDfZF_omega_lCarrier
    (a : LCarrier.{u}) (n : Nat) :
    Injects LMem (textbookDfZFLCarrier a n) omegaLCarrier := by
  let arity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let params : Tuple LCarrier.{u} 3 := ![a, arity, omegaLCarrier]
  let domain : LCarrier.{u} := textbookDfZFLCarrier a n
  have hfun : forall relation : LCarrier.{u},
      relation.1 ∈ domain.1 ->
        ExistsUnique fun code : LCarrier.{u} =>
          FOFormula.Satisfies LMem leastTextbookECodeFormula
            (snoc (snoc params relation) code) := by
    intro relation hrelation
    let first := firstTextbookECode a.1 n
      ⟨relation.1, hrelation⟩
    let code : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier first
    refine ⟨code, ?_, ?_⟩
    · change FOFormula.Satisfies LMem leastTextbookECodeFormula
        (snoc (snoc params relation) code)
      rw [show snoc (snoc params relation) code =
          ![a, arity, omegaLCarrier, relation, code] by
        simpa only [params] using
          leastCode_assignment a arity omegaLCarrier relation code]
      apply (satisfies_leastTextbookECodeFormula_natCode_iff
        a relation code n hrelation).mpr
      rfl
    · intro other hother
      apply Subtype.ext
      apply (satisfies_leastTextbookECodeFormula_natCode_iff
        a relation other n hrelation).mp
      rw [← leastCode_assignment]
      simpa only [params, arity] using hother
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      leastTextbookECodeFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall relation code : LCarrier.{u},
      GraphValue LMem graph relation code <->
        relation.1 ∈ domain.1 /\
          FOFormula.Satisfies LMem leastTextbookECodeFormula
            (snoc (snoc params relation) code) := by
    intro relation code
    constructor
    · rintro ⟨pair, hpairGraph, hpairRC⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨relation', hrelation', code', hcode', hpairEq⟩
      have hpairRCEq :=
        (isKuratowskiPairOf_lCarrier_iff pair relation code).mp hpairRC
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairRCEq)
      have hrelationEq : relation' = relation :=
        Subtype.ext hcoordinates.1
      have hcodeEq : code' = code := Subtype.ext hcoordinates.2
      subst relation'
      subst code'
      exact ⟨hrelation', hcode'⟩
    · rintro ⟨hrelation, hcode⟩
      let pair := orderedPairLCarrier relation code
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨relation, hrelation, code, hcode, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair relation code).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain omegaLCarrier := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨relation, hrelation, code, hcode, hpairEq⟩
    have hcodeOmega : code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
      have hcode' := hcode
      rw [leastCode_assignment] at hcode'
      exact (satisfies_leastTextbookECodeFormula
        a arity omegaLCarrier relation code).mp hcode' |>.1
    exact ⟨relation, hrelation, code, hcodeOmega,
      (isKuratowskiPairOf_lCarrier_iff
        pair relation code).mpr hpairEq⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro relation hrelation
    rcases hfun relation hrelation with ⟨code, hcode, hcodeUnique⟩
    have hcodeOmega : code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
      have hcode' := hcode
      rw [leastCode_assignment] at hcode'
      exact (satisfies_leastTextbookECodeFormula
        a arity omegaLCarrier relation code).mp hcode' |>.1
    refine ⟨code, hcodeOmega,
      (hvalue relation code).mpr ⟨hrelation, hcode⟩, ?_⟩
    intro other _hotherOmega hrelationOther
    apply hcodeUnique other
    exact (hvalue relation other).mp hrelationOther |>.2
  · intro code _hcodeOmega relation hrelation hrelationCode
      other hother hotherCode
    have hrelationFormula :=
      (hvalue relation code).mp hrelationCode |>.2
    have hotherFormula :=
      (hvalue other code).mp hotherCode |>.2
    rw [leastCode_assignment] at hrelationFormula hotherFormula
    have hrelationE := (satisfies_leastTextbookECodeFormula
      a arity omegaLCarrier relation code).mp hrelationFormula |>.2.1
    have hotherE := (satisfies_leastTextbookECodeFormula
      a arity omegaLCarrier other code).mp hotherFormula |>.2.1
    have hrelationValue :=
      (satisfies_textbookEZFFormula_lCarrier_iff
        a arity code relation).mp hrelationE |>.2
    have hotherValue :=
      (satisfies_textbookEZFFormula_lCarrier_iff
        a arity code other).mp hotherE |>.2
    apply Subtype.ext
    exact hotherValue.trans hrelationValue.symm

end

end Constructible.ContinuumFormula
