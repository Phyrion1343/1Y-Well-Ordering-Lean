/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalTextbookDfInjection

/-!
# The internal family of all finite-arity textbook Df sets

Replacement over the genuine internal omega collects the fixed-arity sets
`textbookDfZF a n` into an actual member of `L`.  Its union is consequently
the genuine internal set of all finite-arity definable relations over `a`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

private theorem textbookDfFamily_assignment
    (a index output : LCarrier.{u}) :
    snoc (snoc ![a] index) output = ![a, index, output] := by
  funext i
  fin_cases i <;> rfl

/-- Replacement produces the actual family of all fixed-arity Df sets. -/
theorem exists_internalTextbookDfFamily (a : LCarrier.{u}) :
    exists family : LCarrier.{u}, forall output : LCarrier.{u},
      output.1 ∈ family.1 <->
        exists n : Nat, output = textbookDfZFLCarrier a n := by
  let params : Tuple LCarrier.{u} 1 := ![a]
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        ExistsUnique fun output : LCarrier.{u} =>
          FOFormula.Satisfies LMem
            TextbookDfFormula.textbookDfZFFormula
            (snoc (snoc params index) output) := by
    intro index hindex
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    refine ⟨textbookDfZFLCarrier a n, ?_, ?_⟩
    · change FOFormula.Satisfies LMem
        TextbookDfFormula.textbookDfZFFormula
          (snoc (snoc params
            (TextbookNatFormula.textbookNatCodeLCarrier n))
            (textbookDfZFLCarrier a n))
      rw [show snoc (snoc params
          (TextbookNatFormula.textbookNatCodeLCarrier n))
          (textbookDfZFLCarrier a n) =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            textbookDfZFLCarrier a n] by
        simpa only [params] using textbookDfFamily_assignment a
          (TextbookNatFormula.textbookNatCodeLCarrier n)
          (textbookDfZFLCarrier a n)]
      exact (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
        a (textbookDfZFLCarrier a n) n).mpr rfl
    · intro other hother
      apply Subtype.ext
      apply (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
        a other n).mp
      rw [← textbookDfFamily_assignment]
      simpa only [params] using hother
  rcases Constructible.Model.exists_replacementLCarrier
      TextbookDfFormula.textbookDfZFFormula params omegaLCarrier hfun with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro output
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexValue⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexValue
    subst index
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
      a output n).mp
    rw [← textbookDfFamily_assignment]
    simpa only [params] using hformula
  · rintro ⟨n, rfl⟩
    let index : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier n
    refine ⟨index, ?_, ?_⟩
    · change (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · rw [show snoc (snoc params index) (textbookDfZFLCarrier a n) =
          ![a, index, textbookDfZFLCarrier a n] by
        simpa only [params] using textbookDfFamily_assignment
          a index (textbookDfZFLCarrier a n)]
      simpa only [index] using
        (satisfies_textbookDfZFFormula_lCarrier_natCode_iff
          a (textbookDfZFLCarrier a n) n).mpr rfl

/-- A canonical choice of the Replacement family. -/
noncomputable def internalTextbookDfFamily (a : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose (exists_internalTextbookDfFamily a)

@[simp]
theorem mem_internalTextbookDfFamily_iff
    (a output : LCarrier.{u}) :
    output.1 ∈ (internalTextbookDfFamily a).1 <->
      exists n : Nat, output = textbookDfZFLCarrier a n :=
  Classical.choose_spec (exists_internalTextbookDfFamily a) output

/-- The actual internal union of all finite-arity definable relations. -/
noncomputable def internalTextbookDfRelations (a : LCarrier.{u}) :
    LCarrier.{u} :=
  sUnionLCarrier (internalTextbookDfFamily a)

@[simp]
theorem mem_internalTextbookDfRelations_iff
    (a relation : LCarrier.{u}) :
    relation.1 ∈ (internalTextbookDfRelations a).1 <->
      exists n : Nat, relation.1 ∈ textbookDfZF a.1 n := by
  rw [internalTextbookDfRelations, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨fixedArity, hfixedFamily, hrelation⟩
    rcases (mem_internalTextbookDfFamily_iff
      a fixedArity).mp hfixedFamily with ⟨n, rfl⟩
    exact ⟨n, hrelation⟩
  · rintro ⟨n, hrelation⟩
    exact ⟨textbookDfZFLCarrier a n,
      (mem_internalTextbookDfFamily_iff
        a (textbookDfZFLCarrier a n)).mpr ⟨n, rfl⟩,
      hrelation⟩

end

end Constructible.ContinuumFormula
