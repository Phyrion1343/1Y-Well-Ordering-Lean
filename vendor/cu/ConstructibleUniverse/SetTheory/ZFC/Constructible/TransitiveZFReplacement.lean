/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFSeparation

/-!
# Replacement inside a transitive ZF set model

For a formula that is functional on an internal set, the Replacement scheme
first supplies its exact range as an element of the model.  Transitivity and
the formula-syntax bridge then identify that witness with the corresponding
ambient extensional description.

The ambient `ZFSet.sep` below is used only after the internal witness has been
obtained.  It does not replace the model's own Replacement axiom, and this file
does not yet construct an internally represented function graph.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- Taking raw values commutes with appending an input and an output. -/
theorem zfCarrierTupleVal_finSnoc_finSnoc {M : ZFSet.{u}} {n : Nat}
    (params : Tuple (ZFCarrier M) n) (x y : ZFCarrier M) :
    zfCarrierTupleVal (Fin.snoc (Fin.snoc params x) y) =
      snoc (snoc (zfCarrierTupleVal params) x.1) y.1 := by
  rw [zfCarrierTupleVal_finSnoc, zfCarrierTupleVal_finSnoc]

/-- Scheme realization for a functional formula agrees with raw restricted
satisfaction after appending its input and output. -/
theorem realize_toSchemeFormula_finSnoc_finSnoc_iff_satisfiesIn
    {M : ZFSet.{u}} {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (x y : ZFCarrier M) :
    letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
      FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
    (toSchemeFormula phi).Realize (Fin.snoc (Fin.snoc params x) y) <->
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (snoc (zfCarrierTupleVal params) x.1) y.1) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  calc
    (toSchemeFormula phi).Realize (Fin.snoc (Fin.snoc params x) y) <->
        FOFormula.Satisfies (zfCarrierMem M) phi
          (Fin.snoc (Fin.snoc params x) y) :=
      realize_toSchemeFormula (zfCarrierMem M) phi
        (Fin.snoc (Fin.snoc params x) y)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (zfCarrierTupleVal (Fin.snoc (Fin.snoc params x) y)) :=
      satisfies_zfCarrier_iff_satisfiesIn M phi
        (Fin.snoc (Fin.snoc params x) y)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1) := by
      rw [zfCarrierTupleVal_finSnoc_finSnoc]

/-- Functional Replacement supplies an internal set whose raw members are
exactly the values, still explicitly restricted to the model carrier. -/
theorem exists_zfCarrier_satisfiesIn_replacementRange
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (hfun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1)) :
    Exists fun b : ZFCarrier M => forall y : ZFSet.{u},
      y ∈ b.1 <-> y ∈ M ∧ exists x : ZFSet.{u}, x ∈ a.1 ∧
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x) y) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  have hSchemeFun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        (toSchemeFormula phi).Realize
          (Fin.snoc (Fin.snoc params x) y) := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    refine ⟨y, ?_, ?_⟩
    · exact (realize_toSchemeFormula_finSnoc_finSnoc_iff_satisfiesIn
        phi params x y).mpr hy
    · intro z hz
      apply hyUnique z
      exact (realize_toSchemeFormula_finSnoc_finSnoc_iff_satisfiesIn
        phi params x z).mp hz
  have hReplacement := FirstOrder.SetTheory.ZFAxiom.toProp_of_model
    (M := ZFCarrier M)
    (.replacement n (toSchemeFormula phi))
  rcases hReplacement params a hSchemeFun with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro y
  constructor
  · intro hyb
    have hyM : y ∈ M := hM.1.mem_trans hyb b.2
    let yM : ZFCarrier M := ⟨y, hyM⟩
    rcases (hb yM).mp hyb with ⟨xM, hxa, hphi⟩
    refine ⟨hyM, xM.1, hxa, ?_⟩
    exact (realize_toSchemeFormula_finSnoc_finSnoc_iff_satisfiesIn
      phi params xM yM).mp hphi
  · rintro ⟨hyM, x, hxa, hphi⟩
    have hxM : x ∈ M := hM.1.mem_trans hxa a.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    let yM : ZFCarrier M := ⟨y, hyM⟩
    apply (hb yM).mpr
    refine ⟨xM, hxa, ?_⟩
    exact (realize_toSchemeFormula_finSnoc_finSnoc_iff_satisfiesIn
      phi params xM yM).mpr hphi

/-- The internal Replacement witness is extensionally the ambient separation
of the model carrier by the exact-range predicate. -/
theorem exists_zfCarrier_eq_satisfiesIn_replacementRange
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (hfun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1)) :
    Exists fun b : ZFCarrier M =>
      b.1 = M.sep fun y => exists x : ZFSet.{u}, x ∈ a.1 ∧
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x) y) := by
  rcases exists_zfCarrier_satisfiesIn_replacementRange
      hM phi params a hfun with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_sep, hb]

/-- The exact range described by restricted satisfaction belongs to the model
because it is equal to the model's own Replacement witness. -/
theorem satisfiesIn_replacementRange_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M)
    (hfun : forall x : ZFCarrier M, x.1 ∈ a.1 ->
      ExistsUnique fun y : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (snoc (zfCarrierTupleVal params) x.1) y.1)) :
    (M.sep fun y => exists x : ZFSet.{u}, x ∈ a.1 ∧
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (snoc (zfCarrierTupleVal params) x) y)) ∈ M := by
  rcases exists_zfCarrier_eq_satisfiesIn_replacementRange
      hM phi params a hfun with ⟨b, hb⟩
  simpa only [← hb] using b.2

end

end Constructible.Model
