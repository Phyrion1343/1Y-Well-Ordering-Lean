/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalTextbookDfFamily
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOmegaProductAbsorption

/-!
# An internal enumeration bound for all finite-arity Df relations

The union of all fixed-arity `Df(a,n)` is injected into omega by assigning to
each relation its least arity and, at that arity, its least textbook `E` code.
Both minimizations are expressed in the object language.  Replacement
constructs the actual graph into `omega x omega`, which is then composed with
the already constructed internal pairing injection into omega.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Membership in a fixed-arity Df set -/

/-- Select `[a,arity,output]` from `[a,relation,arity,output]`. -/
def relationInTextbookDfOutputRename : Fin 3 -> Fin 4 :=
  ![0, 2, Fin.last 3]

/-- Layout `[a,relation,arity]`: `relation` belongs to `Df(a,arity)`. -/
def relationInTextbookDfFormula : FOFormula 3 :=
  .ex (.conj
    (FOFormula.rename relationInTextbookDfOutputRename
      TextbookDfFormula.textbookDfZFFormula)
    (.mem (1 : Fin 3).castSucc (Fin.last 3)))

private theorem comp_relationInTextbookDfOutputRename
    (a relation arity output : LCarrier.{u}) :
    (fun i => snoc ![a, relation, arity] output
      (relationInTextbookDfOutputRename i)) =
      ![a, arity, output] := by
  funext i
  fin_cases i <;> rfl

/-- Exact semantics at a standard arity. -/
@[simp]
theorem satisfies_relationInTextbookDfFormula_natCode_iff
    (a relation : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem relationInTextbookDfFormula
        ![a, relation,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      relation.1 ∈ textbookDfZF a.1 n := by
  simp only [relationInTextbookDfFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨output, houtputFormula, hrelationOutput⟩
    rw [comp_relationInTextbookDfOutputRename] at houtputFormula
    have houtput :=
      (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
        a output n).mp houtputFormula
    change relation.1 ∈ output.1 at hrelationOutput
    rwa [houtput] at hrelationOutput
  · intro hrelation
    let output : LCarrier.{u} := textbookDfZFLCarrier a n
    refine ⟨output, ?_, ?_⟩
    · rw [comp_relationInTextbookDfOutputRename]
      exact (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
        a output n).mpr rfl
    · exact hrelation

/-! ## The least arity -/

/-- Select `[a,relation,arity]` from `[a,omega,relation,arity]`. -/
def relationInTextbookDfSelectedRename : Fin 3 -> Fin 4 :=
  ![0, 2, 3]

/-- Under the bounded quantifier, select `[a,relation,earlier]` from
`[a,omega,relation,arity,earlier]`. -/
def relationInTextbookDfEarlierRename : Fin 3 -> Fin 5 :=
  ![0, 2, Fin.last 4]

/-- Layout `[a,omega,relation,arity]`: `arity` is the least finite arity at
which `relation` belongs to `Df(a,arity)`. -/
def leastTextbookDfArityFormula : FOFormula 4 :=
  .conj
    (.mem (3 : Fin 4) (1 : Fin 4))
    (.conj
      (FOFormula.rename relationInTextbookDfSelectedRename
        relationInTextbookDfFormula)
      (FOFormula.boundedAll (3 : Fin 4)
        (.neg (FOFormula.rename relationInTextbookDfEarlierRename
          relationInTextbookDfFormula))))

private theorem comp_relationInTextbookDfSelectedRename
    (a omega relation arity : LCarrier.{u}) :
    (fun i => ![a, omega, relation, arity]
      (relationInTextbookDfSelectedRename i)) =
      ![a, relation, arity] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_relationInTextbookDfEarlierRename
    (a omega relation arity earlier : LCarrier.{u}) :
    (fun i => snoc ![a, omega, relation, arity] earlier
      (relationInTextbookDfEarlierRename i)) =
      ![a, relation, earlier] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_leastTextbookDfArityFormula
    (a omega relation arity : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastTextbookDfArityFormula
        ![a, omega, relation, arity] <->
      arity.1 ∈ omega.1 /\
        FOFormula.Satisfies LMem relationInTextbookDfFormula
          ![a, relation, arity] /\
        forall earlier : LCarrier.{u}, earlier.1 ∈ arity.1 ->
          Not (FOFormula.Satisfies LMem relationInTextbookDfFormula
            ![a, relation, earlier]) := by
  simp only [leastTextbookDfArityFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_boundedAll,
    comp_relationInTextbookDfSelectedRename,
    comp_relationInTextbookDfEarlierRename]
  change
    (arity.1 ∈ omega.1 /\
      FOFormula.Satisfies LMem relationInTextbookDfFormula
        ![a, relation, arity] /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ arity.1 ->
        Not (FOFormula.Satisfies LMem relationInTextbookDfFormula
          ![a, relation, earlier])) <-> _
  rfl

/-- The externally described least arity.  It is used only to prove that the
object-language least-arity formula has a unique output. -/
noncomputable def firstTextbookDfArity
    (a relation : LCarrier.{u})
    (hrelation : relation.1 ∈ (internalTextbookDfRelations a).1) : Nat :=
  by
    classical
    exact Nat.find
      ((mem_internalTextbookDfRelations_iff a relation).mp hrelation)

theorem firstTextbookDfArity_spec
    (a relation : LCarrier.{u})
    (hrelation : relation.1 ∈ (internalTextbookDfRelations a).1) :
    relation.1 ∈ textbookDfZF a.1
      (firstTextbookDfArity a relation hrelation) := by
  classical
  exact Nat.find_spec ((mem_internalTextbookDfRelations_iff
    a relation).mp hrelation)

theorem firstTextbookDfArity_minimal
    (a relation : LCarrier.{u})
    (hrelation : relation.1 ∈ (internalTextbookDfRelations a).1)
    {n : Nat} (hn : relation.1 ∈ textbookDfZF a.1 n) :
    firstTextbookDfArity a relation hrelation <= n := by
  classical
  exact Nat.find_min' ((mem_internalTextbookDfRelations_iff
    a relation).mp hrelation) hn

/-- The object-language least arity is exactly the external least arity. -/
theorem satisfies_leastTextbookDfArityFormula_iff
    (a relation arity : LCarrier.{u})
    (hrelation : relation.1 ∈ (internalTextbookDfRelations a).1) :
    FOFormula.Satisfies LMem leastTextbookDfArityFormula
        ![a, omegaLCarrier, relation, arity] <->
      arity.1 = natCode
        (firstTextbookDfArity a relation hrelation) := by
  let first := firstTextbookDfArity a relation hrelation
  constructor
  · intro hformula
    rcases (satisfies_leastTextbookDfArityFormula
      a omegaLCarrier relation arity).mp hformula with
      ⟨harityOmega, harityFormula, hminimal⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode arity.1).mp
        harityOmega with ⟨n, harityValue⟩
    have harityEq :
        arity = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact harityValue
    subst arity
    have hn : relation.1 ∈ textbookDfZF a.1 n :=
      (satisfies_relationInTextbookDfFormula_natCode_iff
        a relation n).mp harityFormula
    have hfirstLe : first <= n :=
      firstTextbookDfArity_minimal a relation hrelation hn
    have hnLe : n <= first := by
      by_contra hnot
      have hfirstLt : first < n := Nat.lt_of_not_ge hnot
      let earlier : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier first
      have hearlier : earlier.1 ∈
          (TextbookNatFormula.textbookNatCodeLCarrier n).1 := by
        change (natCode first : ZFSet.{u}) ∈ natCode n
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode first) n).mpr ⟨first, hfirstLt, rfl⟩
      apply hminimal earlier hearlier
      apply (satisfies_relationInTextbookDfFormula_natCode_iff
        a relation first).mpr
      exact firstTextbookDfArity_spec a relation hrelation
    have hnEq : n = first := Nat.le_antisymm hnLe hfirstLe
    rw [hnEq]
    exact TextbookNatFormula.textbookNatCodeLCarrier_val first
  · intro harity
    have harityEq : arity =
        TextbookNatFormula.textbookNatCodeLCarrier first := by
      apply Subtype.ext
      exact harity.trans
        (TextbookNatFormula.textbookNatCodeLCarrier_val first).symm
    subst arity
    apply (satisfies_leastTextbookDfArityFormula
      a omegaLCarrier relation
        (TextbookNatFormula.textbookNatCodeLCarrier first)).mpr
    refine ⟨?_, ?_, ?_⟩
    · change (natCode first : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode first)).mpr ⟨first, rfl⟩
    · apply (satisfies_relationInTextbookDfFormula_natCode_iff
        a relation first).mpr
      exact firstTextbookDfArity_spec a relation hrelation
    · intro earlier hearlier hearlierFormula
      rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
          earlier.1 first).mp hearlier with
        ⟨n, hnFirst, hearlierValue⟩
      have hearlierEq :
          earlier = TextbookNatFormula.textbookNatCodeLCarrier n := by
        apply Subtype.ext
        exact hearlierValue
      subst earlier
      have hn : relation.1 ∈ textbookDfZF a.1 n :=
        (satisfies_relationInTextbookDfFormula_natCode_iff
          a relation n).mp hearlierFormula
      have hfirstLe :=
        firstTextbookDfArity_minimal a relation hrelation hn
      exact (Nat.not_le_of_lt hnFirst) hfirstLe

/-! ## Combining the least arity and least E code -/

/-- Select `[a,omega,relation,arity]` from
`[a,omega,relation,output,arity,code]`. -/
def leastTextbookDfPairArityRename : Fin 4 -> Fin 6 :=
  ![0, 1, 2, 4]

/-- Select `[a,arity,omega,relation,code]` from
`[a,omega,relation,output,arity,code]`. -/
def leastTextbookDfPairCodeRename : Fin 5 -> Fin 6 :=
  ![0, 4, 1, 2, 5]

/-- Layout `[a,omega,relation,output]`: `output` is the Kuratowski pair of
the least arity and the least `E` code at that arity. -/
def leastTextbookDfPairFormula : FOFormula 4 :=
  .ex (.ex
    (.conj
      (FOFormula.rename leastTextbookDfPairArityRename
        leastTextbookDfArityFormula)
      (.conj
        (FOFormula.rename leastTextbookDfPairCodeRename
          leastTextbookECodeFormula)
        (kuratowskiPairAt
          (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)))))

private theorem leastTextbookDfPair_assignment
    (a omega relation output arity code : LCarrier.{u}) :
    snoc (snoc ![a, omega, relation, output] arity) code =
      ![a, omega, relation, output, arity, code] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_leastTextbookDfPairArityRename
    (a omega relation output arity code : LCarrier.{u}) :
    (fun i => ![a, omega, relation, output, arity, code]
      (leastTextbookDfPairArityRename i)) =
      ![a, omega, relation, arity] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_leastTextbookDfPairCodeRename
    (a omega relation output arity code : LCarrier.{u}) :
    (fun i => ![a, omega, relation, output, arity, code]
      (leastTextbookDfPairCodeRename i)) =
      ![a, arity, omega, relation, code] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_leastTextbookDfPairFormula
    (a omega relation output : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastTextbookDfPairFormula
        ![a, omega, relation, output] <->
      exists arity code : LCarrier.{u},
        FOFormula.Satisfies LMem leastTextbookDfArityFormula
          ![a, omega, relation, arity] /\
        FOFormula.Satisfies LMem leastTextbookECodeFormula
          ![a, arity, omega, relation, code] /\
        IsKuratowskiPairOf LMem output arity code := by
  simp only [leastTextbookDfPairFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, satisfies_kuratowskiPairAt]
  apply exists_congr
  intro arity
  apply exists_congr
  intro code
  rw [leastTextbookDfPair_assignment,
    comp_leastTextbookDfPairArityRename,
    comp_leastTextbookDfPairCodeRename]
  rfl

private theorem leastTextbookDfPair_relation_assignment
    (a omega relation output : LCarrier.{u}) :
    snoc (snoc ![a, omega] relation) output =
      ![a, omega, relation, output] := by
  funext i
  fin_cases i <;> rfl

/-! ## The Replacement graph and final omega bound -/

/-- All finite-arity textbook definable relations admit one internally
represented injection into omega. -/
theorem injects_internalTextbookDfRelations_omega_lCarrier
    (a : LCarrier.{u}) :
    Injects LMem (internalTextbookDfRelations a) omegaLCarrier := by
  let domain : LCarrier.{u} := internalTextbookDfRelations a
  let params : Tuple LCarrier.{u} 2 := ![a, omegaLCarrier]
  have hfun : forall relation : LCarrier.{u},
      relation.1 ∈ domain.1 ->
        ExistsUnique fun output : LCarrier.{u} =>
          FOFormula.Satisfies LMem leastTextbookDfPairFormula
            (snoc (snoc params relation) output) := by
    intro relation hrelation
    let firstArity : Nat :=
      firstTextbookDfArity a relation hrelation
    have hfixed : relation.1 ∈ textbookDfZF a.1 firstArity :=
      firstTextbookDfArity_spec a relation hrelation
    let arity : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier firstArity
    let relationDf : ZFCarrier (textbookDfZF a.1 firstArity) :=
      ⟨relation.1, hfixed⟩
    let firstCode : Nat :=
      firstTextbookECode a.1 firstArity relationDf
    let code : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier firstCode
    let output : LCarrier.{u} := orderedPairLCarrier arity code
    refine ⟨output, ?_, ?_⟩
    · change FOFormula.Satisfies LMem leastTextbookDfPairFormula
        (snoc (snoc params relation) output)
      rw [show snoc (snoc params relation) output =
          ![a, omegaLCarrier, relation, output] by
        simpa only [params] using
          leastTextbookDfPair_relation_assignment
            a omegaLCarrier relation output]
      apply (satisfies_leastTextbookDfPairFormula
        a omegaLCarrier relation output).mpr
      refine ⟨arity, code, ?_, ?_, ?_⟩
      · apply (satisfies_leastTextbookDfArityFormula_iff
          a relation arity hrelation).mpr
        rfl
      · apply (satisfies_leastTextbookECodeFormula_natCode_iff
          a relation code firstArity hfixed).mpr
        rfl
      · exact (isKuratowskiPairOf_lCarrier_iff
          output arity code).mpr rfl
    · intro other hother
      have hother' :
          FOFormula.Satisfies LMem leastTextbookDfPairFormula
            ![a, omegaLCarrier, relation, other] := by
        rw [← leastTextbookDfPair_relation_assignment]
        simpa only [params] using hother
      rcases (satisfies_leastTextbookDfPairFormula
        a omegaLCarrier relation other).mp hother' with
        ⟨otherArity, otherCode, hotherArity,
          hotherCode, hotherPair⟩
      have hotherArityRaw :=
        (satisfies_leastTextbookDfArityFormula_iff
          a relation otherArity hrelation).mp hotherArity
      have hotherArityEq : otherArity = arity := by
        apply Subtype.ext
        exact hotherArityRaw.trans
          (TextbookNatFormula.textbookNatCodeLCarrier_val
            firstArity).symm
      subst otherArity
      have hotherCodeRaw :=
        (satisfies_leastTextbookECodeFormula_natCode_iff
          a relation otherCode firstArity hfixed).mp hotherCode
      have hotherCodeEq : otherCode = code := by
        apply Subtype.ext
        exact hotherCodeRaw.trans
          (TextbookNatFormula.textbookNatCodeLCarrier_val
            firstCode).symm
      subst otherCode
      apply Subtype.ext
      simpa only [output, orderedPairLCarrier_val] using
        (isKuratowskiPairOf_lCarrier_iff
          other arity code).mp hotherPair
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      leastTextbookDfPairFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall relation output : LCarrier.{u},
      GraphValue LMem graph relation output <->
        relation.1 ∈ domain.1 /\
          FOFormula.Satisfies LMem leastTextbookDfPairFormula
            (snoc (snoc params relation) output) := by
    intro relation output
    constructor
    · rintro ⟨pair, hpairGraph, hpairRO⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨relation', hrelation', output', houtput', hpairEq⟩
      have hpairROEq :=
        (isKuratowskiPairOf_lCarrier_iff
          pair relation output).mp hpairRO
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairROEq)
      have hrelationEq : relation' = relation :=
        Subtype.ext hcoordinates.1
      have houtputEq : output' = output :=
        Subtype.ext hcoordinates.2
      subst relation'
      subst output'
      exact ⟨hrelation', houtput'⟩
    · rintro ⟨hrelation, houtput⟩
      let pair := orderedPairLCarrier relation output
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨relation, hrelation, output, houtput, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair relation output).mpr rfl
  let product : LCarrier.{u} :=
    prodLCarrier (omegaLCarrier : LCarrier.{u}) omegaLCarrier
  have hbetween : IsGraphBetween LMem graph domain product := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨relation, hrelation, output, houtput, hpairEq⟩
    have houtput' := houtput
    rw [leastTextbookDfPair_relation_assignment] at houtput'
    rcases (satisfies_leastTextbookDfPairFormula
      a omegaLCarrier relation output).mp houtput' with
      ⟨arity, code, harity, hcode, houtputPair⟩
    have harityOmega :=
      (satisfies_leastTextbookDfArityFormula
        a omegaLCarrier relation arity).mp harity |>.1
    have hcodeOmega :=
      (satisfies_leastTextbookECodeFormula
        a arity omegaLCarrier relation code).mp hcode |>.1
    have houtputProduct : output.1 ∈ product.1 := by
      change output.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1
      rw [(isKuratowskiPairOf_lCarrier_iff
        output arity code).mp houtputPair, ZFSet.pair_mem_prod]
      exact ⟨harityOmega, hcodeOmega⟩
    exact ⟨relation, hrelation, output, houtputProduct,
      (isKuratowskiPairOf_lCarrier_iff
        pair relation output).mpr hpairEq⟩
  have hinjectsProduct : Injects LMem domain product := by
    refine ⟨graph, hbetween, ?_, ?_⟩
    · intro relation hrelation
      rcases hfun relation hrelation with
        ⟨output, houtput, houtputUnique⟩
      have houtput' := houtput
      rw [leastTextbookDfPair_relation_assignment] at houtput'
      rcases (satisfies_leastTextbookDfPairFormula
        a omegaLCarrier relation output).mp houtput' with
        ⟨arity, code, harity, hcode, houtputPair⟩
      have harityOmega :=
        (satisfies_leastTextbookDfArityFormula
          a omegaLCarrier relation arity).mp harity |>.1
      have hcodeOmega :=
        (satisfies_leastTextbookECodeFormula
          a arity omegaLCarrier relation code).mp hcode |>.1
      have houtputProduct : output.1 ∈ product.1 := by
        change output.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1
        rw [(isKuratowskiPairOf_lCarrier_iff
          output arity code).mp houtputPair, ZFSet.pair_mem_prod]
        exact ⟨harityOmega, hcodeOmega⟩
      refine ⟨output, houtputProduct,
        (hvalue relation output).mpr ⟨hrelation, houtput⟩, ?_⟩
      intro other _hotherProduct hrelationOther
      apply houtputUnique other
      exact (hvalue relation other).mp hrelationOther |>.2
    · intro output _houtputProduct relation hrelation hrelationOutput
        other hother hotherOutput
      have hrelationFormula :=
        (hvalue relation output).mp hrelationOutput |>.2
      have hotherFormula :=
        (hvalue other output).mp hotherOutput |>.2
      rw [leastTextbookDfPair_relation_assignment] at hrelationFormula hotherFormula
      rcases (satisfies_leastTextbookDfPairFormula
        a omegaLCarrier relation output).mp hrelationFormula with
        ⟨arity, code, _harity, hcode, houtputPair⟩
      rcases (satisfies_leastTextbookDfPairFormula
        a omegaLCarrier other output).mp hotherFormula with
        ⟨otherArity, otherCode, _hotherArity, hotherCode,
          hotherOutputPair⟩
      have hpair :=
        (isKuratowskiPairOf_lCarrier_iff
          output arity code).mp houtputPair
      have hotherPair :=
        (isKuratowskiPairOf_lCarrier_iff
          output otherArity otherCode).mp hotherOutputPair
      have hcoordinates := ZFSet.pair_inj.mp (hpair.symm.trans hotherPair)
      have harityEq : otherArity = arity :=
        Subtype.ext hcoordinates.1.symm
      have hcodeEq : otherCode = code :=
        Subtype.ext hcoordinates.2.symm
      subst otherArity
      subst otherCode
      have hrelationE :=
        (satisfies_leastTextbookECodeFormula
          a arity omegaLCarrier relation code).mp hcode |>.2.1
      have hotherE :=
        (satisfies_leastTextbookECodeFormula
          a arity omegaLCarrier other code).mp hotherCode |>.2.1
      have hrelationValue :=
        (satisfies_textbookEZFFormula_lCarrier_iff
          a arity code relation).mp hrelationE |>.2
      have hotherValue :=
        (satisfies_textbookEZFFormula_lCarrier_iff
          a arity code other).mp hotherE |>.2
      apply Subtype.ext
      exact hotherValue.trans hrelationValue.symm
  exact hinjectsProduct.trans_lCarrier
    injects_omegaProduct_omega_lCarrier

end

end Constructible.ContinuumFormula
