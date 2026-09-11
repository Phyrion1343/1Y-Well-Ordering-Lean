/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPositiveFormulaEnumeration

/-!
# Full Tarski--Vaught closure through the textbook E enumeration

The textbook operation `E(U,n,m)` enumerates every positive-arity relation in
`Df(U,n)`.  `TextbookPositiveFormulaEnumeration` proves, without appealing to
an object-language truth predicate, that the relation of every formula with
at least one free coordinate occurs in this enumeration.

This file packages the corresponding full Tarski--Vaught criterion.  If a
subset of `U` contains witnesses for every relation `E(U,n+1,m)` and every
parameter tuple from the subset, then it is closed for every existential
subformula of every first-order formula.  Hence satisfaction is absolute for
all formulas, not merely for a finite fragment.

`ClosesUnderTextbookEWitnesses` is still an external semantic predicate.  No
claim is made here that a small subset satisfying it has already been
constructed inside `L`.  The remaining construction must internally
enumerate the pairs `(n,m)`, uniformly define the canonical witness step, and
collect its omega iteration by Replacement.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

section ZFC

/-- Closure under witnesses for every relation in the textbook `E`
enumeration.  A relation has arity `n + 1`; its final coordinate is the
candidate witness and the first `n` coordinates are parameters. -/
def ClosesUnderTextbookEWitnesses
    (small : Set ZFSet.{u}) (U : ZFSet.{u}) : Prop :=
  ∀ {n : Nat} (code : Nat) (params : Tuple (ZFCarrier U) n),
    (∀ i, (params i).1 ∈ small) ->
      (∃ x : ZFCarrier U,
        textbookTupleGraph (snoc params x) ∈
          textbookEZF U (natCode (n + 1)) (natCode code)) ->
      ∃ x : ZFCarrier U,
        x.1 ∈ small ∧
          textbookTupleGraph (snoc params x) ∈
            textbookEZF U (natCode (n + 1)) (natCode code)

/-- Closure under all textbook `E` witness relations supplies full recursive
Tarski--Vaught closure for every first-order formula. -/
theorem closesWithinAll_of_closesUnderTextbookEWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderTextbookEWitnesses small U) :
    ClosesWithinAll small (U : Set ZFSet.{u}) := by
  intro n formula
  induction formula with
  | mem i j => trivial
  | eq i j => trivial
  | neg formula ih => exact ih
  | conj formula psi ihFormula ihPsi =>
      exact ⟨ihFormula, ihPsi⟩
  | @ex m matrix ih =>
      refine ⟨ih, ?_⟩
      intro params hparams hexists
      rcases hexists with ⟨x, hxU, hxMatrix⟩
      let paramsU : Tuple (ZFCarrier U) m :=
        fun i => ⟨params i, hsubset (hparams i)⟩
      let xU : ZFCarrier U := ⟨x, hxU⟩
      have hxCarrier :
          FOFormula.Satisfies (zfCarrierMem U) matrix
            (snoc paramsU xU) := by
        apply (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) matrix (snoc paramsU xU)).mpr
        simpa only [Model.subtypeVal_snoc, paramsU, xU] using hxMatrix
      rcases exists_textbookECode_for_positiveFormula U matrix with
        ⟨code, hcode⟩
      have hxRelation :
          textbookTupleGraph (snoc paramsU xU) ∈
            textbookEZF U (natCode (m + 1)) (natCode code) :=
        (hcode (snoc paramsU xU)).mpr hxCarrier
      rcases hclose code paramsU
          (fun i => by simpa only [paramsU] using hparams i)
          ⟨xU, hxRelation⟩ with
        ⟨w, hwSmall, hwRelation⟩
      refine ⟨w.1, hwSmall, ?_⟩
      have hwCarrier :
          FOFormula.Satisfies (zfCarrierMem U) matrix
            (snoc paramsU w) :=
        (hcode (snoc paramsU w)).mp hwRelation
      have hwRaw :=
        (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) matrix (snoc paramsU w)).mp hwCarrier
      simpa only [Model.subtypeVal_snoc, paramsU] using hwRaw

/-- The same criterion stated as full satisfaction absoluteness. -/
theorem satisfactionAbsolute_of_closesUnderTextbookEWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderTextbookEWitnesses small U) :
    SatisfactionAbsolute small (U : Set ZFSet.{u}) :=
  satisfactionAbsolute_of_closesWithinAll hsubset
    (closesWithinAll_of_closesUnderTextbookEWitnesses hsubset hclose)

end ZFC

end Constructible
