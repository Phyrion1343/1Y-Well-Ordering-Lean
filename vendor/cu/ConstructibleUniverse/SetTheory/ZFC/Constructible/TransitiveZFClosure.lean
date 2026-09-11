/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFModel

/-!
# Basic closure of transitive set models of ZF

This file proves the elementary closure facts used in Section 6.2 of Wang
Fangting, *Axiomatic Set Theory*.  Each object is first obtained from the
corresponding axiom inside a set model `M`.  Transitivity then shows that the
internal object is extensionally equal to the ambient `ZFSet` construction.

No ambient separation or replacement operation is used as a substitute for
an internal object.  Power set is deliberately absent: an internal power set
of `x` need not be the ambient `x.powerset`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The empty-set axiom in a transitive ZF model produces the ambient empty
set, not merely an object with no members from the model. -/
theorem exists_zfCarrier_eq_empty {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) :
    Exists fun e : ZFCarrier M => e.1 = (∅ : ZFSet.{u}) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .emptySet with ⟨e, he⟩
  refine ⟨e, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hze
    have hzM : z ∈ M := hM.1.mem_trans hze e.2
    have hzNot : z ∉ e.1 := by
      have hzNotInternal := he ⟨z, hzM⟩
      change z ∉ e.1 at hzNotInternal
      exact hzNotInternal
    exact (hzNot hze).elim
  · intro hzEmpty
    exact (ZFSet.notMem_empty z hzEmpty).elim

/-- A transitive ZF model contains the ambient empty set. -/
theorem empty_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) :
    (∅ : ZFSet.{u}) ∈ M := by
  rcases exists_zfCarrier_eq_empty hM with ⟨e, he⟩
  simpa only [he] using e.2

/-- The Pairing axiom in a transitive ZF model produces the ambient unordered
pair of its two arguments. -/
theorem exists_zfCarrier_eq_unorderedPair {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    Exists fun p : ZFCarrier M => p.1 = ({x, y} : ZFSet.{u}) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  let yM : ZFCarrier M := ⟨y, hy⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .pairing xM yM with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hzp
    have hzM : z ∈ M := hM.1.mem_trans hzp p.2
    let zM : ZFCarrier M := ⟨z, hzM⟩
    have hzPair := (hp zM).mp hzp
    rcases hzPair with hzx | hzy
    · exact ZFSet.mem_pair.mpr (Or.inl (congrArg Subtype.val hzx))
    · exact ZFSet.mem_pair.mpr (Or.inr (congrArg Subtype.val hzy))
  · intro hzPair
    rcases ZFSet.mem_pair.mp hzPair with hzx | hzy
    · subst z
      exact (hp xM).mpr (Or.inl rfl)
    · subst z
      exact (hp yM).mpr (Or.inr rfl)

/-- A transitive ZF model is closed under ambient unordered pairing. -/
theorem unorderedPair_mem_of_isTransitiveZFModel {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    ({x, y} : ZFSet.{u}) ∈ M := by
  rcases exists_zfCarrier_eq_unorderedPair hM hx hy with ⟨p, hp⟩
  simpa only [hp] using p.2

/-- A transitive ZF model is closed under ambient singletons. -/
theorem singleton_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ({x} : ZFSet.{u}) ∈ M := by
  rw [← ZFSet.pair_eq_singleton x]
  exact unorderedPair_mem_of_isTransitiveZFModel hM hx hx

/-- The Union axiom in a transitive ZF model produces the ambient union of
the argument. -/
theorem exists_zfCarrier_eq_sUnion {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    Exists fun union : ZFCarrier M => union.1 = ZFSet.sUnion x := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .union xM with ⟨union, hunion⟩
  refine ⟨union, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hzUnion
    have hzM : z ∈ M := hM.1.mem_trans hzUnion union.2
    rcases (hunion ⟨z, hzM⟩).mp hzUnion with ⟨yM, hyx, hzy⟩
    exact ZFSet.mem_sUnion.mpr ⟨yM.1, hyx, hzy⟩
  · intro hzUnion
    rcases ZFSet.mem_sUnion.mp hzUnion with ⟨y, hyx, hzy⟩
    have hyM : y ∈ M := hM.1.mem_trans hyx hx
    have hzM : z ∈ M := hM.1.mem_trans hzy hyM
    exact (hunion ⟨z, hzM⟩).mpr ⟨⟨y, hyM⟩, hyx, hzy⟩

/-- A transitive ZF model is closed under ambient union. -/
theorem sUnion_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ZFSet.sUnion x ∈ M := by
  rcases exists_zfCarrier_eq_sUnion hM hx with ⟨union, hunion⟩
  simpa only [hunion] using union.2

/-- A transitive ZF model is closed under the ambient Kuratowski ordered-pair
coding used throughout the constructible-universe development. -/
theorem kuratowskiPair_mem_of_isTransitiveZFModel {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    ZFSet.pair x y ∈ M := by
  have hSingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hPair : ({x, y} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hx hy
  simpa only [ZFSet.pair] using
    unorderedPair_mem_of_isTransitiveZFModel hM hSingleton hPair

end

end Constructible.Model
