/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalArithmeticLCarrier

/-!
# The internally represented injection from omega squared into omega

The graph sends the pair of natural codes `(i,j)` to Wang's prime-power code
`2^i * 3^j`.  The arithmetic is evaluated by the previously verified pure
membership-language formula, and Separation turns that fixed formula into an
actual Kuratowski graph in `L`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF
open Constructible.TextbookNatFormula

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Formula and exact relation -/

def OmegaPairCodeRel (input output : LCarrier.{u}) : Prop :=
  exists left right : LCarrier.{u},
    IsKuratowskiPairOf LMem input left right /\
      FOFormula.Satisfies LMem textbookECodeFormula
        ![omegaLCarrier, left, right, textbookNatCodeLCarrier 0, output]

/-- Layout `(omega,zero,domain,input,output)`; the two witnesses are the
decoded input coordinates. -/
def omegaPairCodeFormula : FOFormula 5 :=
  .ex (.ex
    (.conj
      (.mem (3 : Fin 7) (2 : Fin 7))
      (.conj
        (kuratowskiPairAt (3 : Fin 7) (5 : Fin 7) (6 : Fin 7))
        (textbookECodeFormulaAt
          (0 : Fin 7) (5 : Fin 7) (6 : Fin 7)
          (1 : Fin 7) (4 : Fin 7)))))

private theorem omegaPairCode_assignment
    (omega zero domain input output left right : LCarrier.{u}) :
    snoc (snoc ![omega, zero, domain, input, output] left) right =
      ![omega, zero, domain, input, output, left, right] := by
  funext i
  fin_cases i <;> rfl

private theorem omegaPairCode_code_assignment
    (omega zero domain input output left right : LCarrier.{u}) :
    ![![omega, zero, domain, input, output, left, right] 0,
      ![omega, zero, domain, input, output, left, right] 5,
      ![omega, zero, domain, input, output, left, right] 6,
      ![omega, zero, domain, input, output, left, right] 1,
      ![omega, zero, domain, input, output, left, right] 4] =
      ![omega, left, right, zero, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_omegaPairCodeFormula
    (omega zero domain input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem omegaPairCodeFormula
        ![omega, zero, domain, input, output] <->
      input.1 ∈ domain.1 /\
        exists left right : LCarrier.{u},
          IsKuratowskiPairOf LMem input left right /\
            FOFormula.Satisfies LMem textbookECodeFormula
              ![omega, left, right, zero, output] := by
  simp only [omegaPairCodeFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨left, right, hinput, hpair, hcode⟩
    rw [omegaPairCode_assignment] at hinput hpair hcode
    change input.1 ∈ domain.1 at hinput
    rw [satisfies_kuratowskiPairAt] at hpair
    rw [satisfies_textbookECodeFormulaAt,
      omegaPairCode_code_assignment] at hcode
    exact ⟨hinput, left, right, hpair, hcode⟩
  · rintro ⟨hinput, left, right, hpair, hcode⟩
    refine ⟨left, right, ?_, ?_, ?_⟩
    · rw [omegaPairCode_assignment]
      exact hinput
    · rw [omegaPairCode_assignment, satisfies_kuratowskiPairAt]
      exact hpair
    · rw [omegaPairCode_assignment,
        satisfies_textbookECodeFormulaAt,
        omegaPairCode_code_assignment]
      exact hcode

private theorem omegaPairCode_relation_assignment
    (omega zero domain input output : LCarrier.{u}) :
    snoc (snoc ![omega, zero, domain] input) output =
      ![omega, zero, domain, input, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_omegaPairCodeRelation
    (omega zero domain input output : LCarrier.{u}) :
    FOFormula.Satisfies LMem omegaPairCodeFormula
        (snoc (snoc ![omega, zero, domain] input) output) <->
      input.1 ∈ domain.1 /\
        exists left right : LCarrier.{u},
          IsKuratowskiPairOf LMem input left right /\
            FOFormula.Satisfies LMem textbookECodeFormula
              ![omega, left, right, zero, output] := by
  rw [omegaPairCode_relation_assignment,
    satisfies_omegaPairCodeFormula]

/-- On the product domain, the formula has exactly the advertised numerical
semantics. -/
theorem OmegaPairCodeRel.exact_of_mem
    {input output : LCarrier.{u}}
    (hinput : input.1 ∈ (prodLCarrier omegaLCarrier omegaLCarrier).1)
    (hrel : OmegaPairCodeRel input output) :
    exists i j : Nat,
      input = orderedPairLCarrier
        (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j) /\
      output = textbookNatCodeLCarrier (textbookECode i j 0) := by
  rcases hrel with ⟨left, right, hpair, hformula⟩
  have hpairRaw :=
    (isKuratowskiPairOf_lCarrier_iff input left right).mp hpair
  have hcoordinates :
      left.1 ∈ omegaLCarrier.1 /\ right.1 ∈ omegaLCarrier.1 := by
    change input.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1 at hinput
    rw [hpairRaw, ZFSet.pair_mem_prod] at hinput
    exact hinput
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode left.1).mp
      hcoordinates.1 with ⟨i, hi⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode right.1).mp
      hcoordinates.2 with ⟨j, hj⟩
  have hleft : left = textbookNatCodeLCarrier i := Subtype.ext hi
  have hright : right = textbookNatCodeLCarrier j := Subtype.ext hj
  subst left
  subst right
  have houtputRaw : output.1 = natCode (textbookECode i j 0) :=
    (satisfies_textbookECodeFormula_lCarrier_natCode_iff
      i j 0 output).mp hformula
  refine ⟨i, j, ?_, Subtype.ext houtputRaw⟩
  apply Subtype.ext
  exact hpairRaw

/-! ## The internal injection -/

/-- The textbook prime-power pairing is represented by an actual internal
injection `omega x omega -> omega`. -/
theorem injects_omegaProduct_omega_lCarrier :
    Injects LMem
      (prodLCarrier (omegaLCarrier : LCarrier.{u}) omegaLCarrier)
      omegaLCarrier := by
  let domain : LCarrier.{u} := prodLCarrier omegaLCarrier omegaLCarrier
  let zero : LCarrier.{u} := textbookNatCodeLCarrier 0
  let support : LCarrier.{u} := unionLCarrier domain omegaLCarrier
  rcases Constructible.Model.exists_definableRelationGraph_with_support
      omegaPairCodeFormula ![omegaLCarrier, zero, domain] support with
    ⟨graph, hsupport, hrelation⟩
  have hvalue : forall input output : LCarrier.{u},
      GraphValue LMem graph input output <->
        input.1 ∈ domain.1 /\ OmegaPairCodeRel input output := by
    intro input output
    rw [graphValue_lCarrier_iff_graphRel, hrelation]
    constructor
    · rintro ⟨_hinputSupport, _houtputSupport, hformula⟩
      have hsemantic := (satisfies_omegaPairCodeRelation
        omegaLCarrier zero domain input output).mp hformula
      exact ⟨hsemantic.1, hsemantic.2⟩
    · rintro ⟨hinput, hrel⟩
      rcases hrel.exact_of_mem hinput with ⟨i, j, _hinputEq, houtputEq⟩
      have houtputOmega : output.1 ∈ omegaLCarrier.1 := by
        rw [houtputEq]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (textbookECode i j 0))).mpr
            ⟨textbookECode i j 0, rfl⟩
      refine ⟨(mem_unionLCarrier_iff domain omegaLCarrier input).mpr
          (Or.inl hinput),
        (mem_unionLCarrier_iff domain omegaLCarrier output).mpr
          (Or.inr houtputOmega), ?_⟩
      exact (satisfies_omegaPairCodeRelation
        omegaLCarrier zero domain input output).mpr ⟨hinput, hrel⟩
  have hbetween : IsGraphBetween LMem graph domain omegaLCarrier := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨input, output, _hinputSupport, _houtputSupport,
        hpairEq, hformula⟩
    have hsemantic := (satisfies_omegaPairCodeRelation
      omegaLCarrier zero domain input output).mp hformula
    have hinput : input.1 ∈ domain.1 := hsemantic.1
    have hrel : OmegaPairCodeRel input output := hsemantic.2
    rcases hrel.exact_of_mem hinput with ⟨i, j, _hinputEq, houtputEq⟩
    have houtput : output.1 ∈ omegaLCarrier.1 := by
      rw [houtputEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨textbookECode i j 0, rfl⟩
    exact ⟨input, hinput, output, houtput,
      (isKuratowskiPairOf_lCarrier_iff pair input output).mpr hpairEq⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro input hinput
    change input.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1 at hinput
    rcases ZFSet.mem_prod.mp hinput with
      ⟨leftRaw, hleft, rightRaw, hright, hinputRaw⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode leftRaw).mp
      hleft with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode rightRaw).mp
      hright with ⟨j, hj⟩
    let output := textbookNatCodeLCarrier (textbookECode i j 0)
    have houtput : output.1 ∈ omegaLCarrier.1 :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨textbookECode i j 0, rfl⟩
    have hinputEq : input = orderedPairLCarrier
        (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j) := by
      apply Subtype.ext
      simpa only [hi, hj, orderedPairLCarrier_val,
        textbookNatCodeLCarrier_val] using hinputRaw
    have hrel : OmegaPairCodeRel input output := by
      refine ⟨textbookNatCodeLCarrier i, textbookNatCodeLCarrier j, ?_, ?_⟩
      · apply (isKuratowskiPairOf_lCarrier_iff input
          (textbookNatCodeLCarrier i) (textbookNatCodeLCarrier j)).mpr
        rw [hinputEq]
        rfl
      · exact (satisfies_textbookECodeFormula_lCarrier_natCode_iff
          i j 0 output).mpr rfl
    refine ⟨output, houtput, (hvalue input output).mpr ⟨hinput, hrel⟩, ?_⟩
    intro other _hother hotherValue
    rcases ((hvalue input other).mp hotherValue).2.exact_of_mem hinput with
      ⟨i', j', hinputEq', hotherEq⟩
    have hpairs := ZFSet.pair_inj.mp
      (congrArg Subtype.val (hinputEq.symm.trans hinputEq'))
    have hiEq : i = i' := natCode_injective hpairs.1
    have hjEq : j = j' := natCode_injective hpairs.2
    subst i'
    subst j'
    exact hotherEq.trans rfl
  · intro output houtput input hinput hinputValue
      other hother hotherValue
    rcases ((hvalue input output).mp hinputValue).2.exact_of_mem hinput with
      ⟨i, j, hinputEq, houtputEq⟩
    rcases ((hvalue other output).mp hotherValue).2.exact_of_mem hother with
      ⟨i', j', hotherEq, houtputEq'⟩
    have hcodesRaw := congrArg Subtype.val
      (houtputEq.symm.trans houtputEq')
    have hcodes : textbookECode i j 0 = textbookECode i' j' 0 :=
      natCode_injective hcodesRaw
    have hfields := textbookECode_injective_fields hcodes
    apply hotherEq.trans
    rw [← hfields.1, ← hfields.2.1]
    exact hinputEq.symm

end

end Constructible.ContinuumFormula
