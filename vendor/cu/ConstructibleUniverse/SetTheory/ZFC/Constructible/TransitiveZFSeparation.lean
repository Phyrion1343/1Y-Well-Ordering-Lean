/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSchemeBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFClosure

/-!
# Separation inside a transitive ZF set model

For an `FOFormula`, parameters from a transitive ZF set model `M`, and an
internal set `a`, the Separation scheme first supplies an internal result.
The formula-syntax bridges and transitivity then identify that result with the
ambient `ZFSet.sep` whose predicate is restricted satisfaction in `M`.

Thus `ZFSet.sep` occurs only as an extensional description of an object already
obtained from the model's own Separation axiom.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The raw tuple underlying a tuple of members of an internal set. -/
def zfCarrierTupleVal {M : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier M) n) : Tuple ZFSet.{u} n :=
  fun i => (s i).1

/-- Taking values commutes with appending one member to a subtype tuple. -/
theorem zfCarrierTupleVal_finSnoc {M : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier M) n) (x : ZFCarrier M) :
    zfCarrierTupleVal (Fin.snoc s x) =
      snoc (zfCarrierTupleVal s) x.1 := by
  rw [← snoc_eq_finSnoc]
  exact subtypeVal_snoc s x

/-- A formula in scheme-variable form has exactly the expected raw restricted
semantics after appending one candidate element. -/
theorem realize_toSchemeFormula_finSnoc_iff_satisfiesIn
    {M : ZFSet.{u}} {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (x : ZFCarrier M) :
    letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
      FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
    (toSchemeFormula phi).Realize (Fin.snoc params x) <->
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (zfCarrierTupleVal params) x.1) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  calc
    (toSchemeFormula phi).Realize (Fin.snoc params x) <->
        FOFormula.Satisfies (zfCarrierMem M) phi
          (Fin.snoc params x) :=
      realize_toSchemeFormula (zfCarrierMem M) phi (Fin.snoc params x)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (zfCarrierTupleVal (Fin.snoc params x)) :=
      satisfies_zfCarrier_iff_satisfiesIn M phi (Fin.snoc params x)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (zfCarrierTupleVal params) x.1) := by
      rw [zfCarrierTupleVal_finSnoc]

/-- The internal witness supplied by Separation is extensionally the ambient
restricted-satisfaction separation of `a`. -/
theorem exists_zfCarrier_eq_satisfiesIn_sep
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M) :
    Exists fun b : ZFCarrier M =>
      b.1 = a.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (zfCarrierTupleVal params) x) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  have hSeparation := FirstOrder.SetTheory.ZFAxiom.toProp_of_model
    (M := ZFCarrier M)
    (.separation n (toSchemeFormula phi))
  rcases hSeparation params a with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hxb
    have hxM : x ∈ M := hM.1.mem_trans hxb b.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    have hInternal := (hb xM).mp hxb
    change x ∈ a.1 ∧
      (toSchemeFormula phi).Realize (Fin.snoc params xM) at hInternal
    exact ⟨hInternal.1,
      (realize_toSchemeFormula_finSnoc_iff_satisfiesIn
        phi params xM).mp hInternal.2⟩
  · rintro ⟨hxa, hphi⟩
    have hxM : x ∈ M := hM.1.mem_trans hxa a.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    apply (hb xM).mpr
    change x ∈ a.1 ∧
      (toSchemeFormula phi).Realize (Fin.snoc params xM)
    exact ⟨hxa,
      (realize_toSchemeFormula_finSnoc_iff_satisfiesIn
        phi params xM).mpr hphi⟩

/-- The ambient set described by restricted satisfaction belongs to `M`
because it is equal to the model's own Separation witness. -/
theorem satisfiesIn_sep_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M) :
    (a.1.sep fun x =>
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (zfCarrierTupleVal params) x)) ∈ M := by
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM phi params a with
    ⟨b, hb⟩
  simpa only [hb] using b.2

end

end Constructible.Model
