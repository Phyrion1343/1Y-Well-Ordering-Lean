/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.HartogsSuccessor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.PowerSet
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# Reduction of GCH in the constructible universe

This file discharges the elementary part of the GCH semantics for
`Model.LCarrier`.  It identifies the standard constructible `omega` with the
least internally inductive set, proves that it is an internal cardinal, and
reduces GCH to the substantive upper-bound theorem for constructible power
sets.

The reduction theorem deliberately keeps that upper bound as an explicit
hypothesis.  In particular, no condensation or small-stage theorem is assumed
implicitly here.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The internal natural numbers -/

private theorem isInductiveSet_lCarrier_iff_model
    (w : Constructible.Model.LCarrier.{u}) :
    IsInductiveSet LMem w ↔ Constructible.Model.IsInductiveSet w := by
  constructor
  · rintro ⟨⟨empty, hempty, hemptyMem⟩, hsuccessor⟩
    have hemptyEq : empty = emptyLCarrier := by
      apply lCarrier_extensionality
      intro z
      constructor
      · intro hz
        exact (hempty z hz).elim
      · intro hz
        exact (not_mem_emptyLCarrier z hz).elim
    constructor
    · simpa only [hemptyEq] using hemptyMem
    · intro x hx
      rcases hsuccessor x hx with ⟨successor, hsuccessorEq, hsuccessorMem⟩
      have hsuccessorCarrierEq : successor = successorLCarrier x := by
        apply lCarrier_extensionality
        intro z
        have hz := hsuccessorEq z
        change z.1 ∈ successor.1 ↔ z.1 ∈ x.1 ∨ z = x at hz
        change z.1 ∈ successor.1 ↔ z.1 ∈ (successorLCarrier x).1
        rw [hz, successorLCarrier_val,
          ZFSet.mem_insert_iff]
        simp only [Subtype.ext_iff, or_comm]
      simpa only [hsuccessorCarrierEq] using hsuccessorMem
  · rintro ⟨hempty, hsuccessor⟩
    constructor
    · refine ⟨emptyLCarrier, ?_, hempty⟩
      exact not_mem_emptyLCarrier
    · intro x hx
      refine ⟨successorLCarrier x, ?_, hsuccessor x hx⟩
      intro z
      change z.1 ∈ (successorLCarrier x).1 ↔ z.1 ∈ x.1 ∨ z = x
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      simp only [Subtype.ext_iff, or_comm]

/-- The standard constructible `omega` is the least internally inductive set
in the relation-parametric semantics used by the GCH sentence. -/
theorem omegaLCarrier_isOmega :
    IsOmega LMem (omegaLCarrier : Constructible.Model.LCarrier.{u}) := by
  constructor
  · exact (isInductiveSet_lCarrier_iff_model omegaLCarrier).2
      omegaLCarrier_isInductiveSet
  · intro w hw x hx
    exact omegaLCarrier_subset_of_isInductiveSet
      ((isInductiveSet_lCarrier_iff_model w).1 hw) x hx

/-! ## Finiteness of the ordinals below `omega` -/

private noncomputable def finiteOrdinalMemberIndex (n : Nat) :
    RelationCarrier LMem
      (ordinalLCarrier (n : Ordinal.{u})) → Fin n :=
  fun x => by
    have hxraw : x.1.1 ∈
        (ordinalLCarrier (n : Ordinal.{u})).1 := x.2
    have hx : x.1.1 ∈
        Constructible.FiniteSequenceZF.natCode n := by
      simpa only [ordinalLCarrier_val,
        Constructible.FiniteSequenceZF.natCode] using hxraw
    let k := Classical.choose
      (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
        x.1.1 n |>.mp hx)
    exact ⟨k, (Classical.choose_spec
      (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
        x.1.1 n |>.mp hx)).1⟩

private theorem finiteOrdinalMemberIndex_spec (n : Nat)
    (x : RelationCarrier LMem
      (ordinalLCarrier (n : Ordinal.{u}))) :
    x.1.1 = Constructible.FiniteSequenceZF.natCode
      (finiteOrdinalMemberIndex n x).1 := by
  have hxraw : x.1.1 ∈
      (ordinalLCarrier (n : Ordinal.{u})).1 := x.2
  rw [finiteOrdinalMemberIndex]
  exact (Classical.choose_spec
    (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
      x.1.1 n |>.mp (by
        simpa only [ordinalLCarrier_val,
          Constructible.FiniteSequenceZF.natCode] using hxraw))).2

private theorem finiteOrdinalMemberIndex_injective (n : Nat) :
    Function.Injective (finiteOrdinalMemberIndex.{u} n) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  calc
    x.1.1 = Constructible.FiniteSequenceZF.natCode
        (finiteOrdinalMemberIndex n x).1 :=
      finiteOrdinalMemberIndex_spec n x
    _ = Constructible.FiniteSequenceZF.natCode
        (finiteOrdinalMemberIndex n y).1 := by
      rw [congrArg Fin.val hxy]
    _ = y.1.1 := (finiteOrdinalMemberIndex_spec n y).symm

private noncomputable def omegaNaturalMember (n : Nat) :
    RelationCarrier LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u}) :=
  ⟨ordinalLCarrier (n : Ordinal.{u}), by
    change (n : Ordinal.{u}).toZFSet ∈ Ordinal.omega0.toZFSet
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)⟩

private theorem omegaNaturalMember_injective :
    Function.Injective (omegaNaturalMember.{u}) := by
  intro m n hmn
  have hraw :
      (m : Ordinal.{u}).toZFSet = (n : Ordinal.{u}).toZFSet :=
    congrArg (fun x => x.1.1) hmn
  exact_mod_cast Ordinal.toZFSet_injective hraw

private theorem not_injects_omega_finiteOrdinal (n : Nat) :
    ¬Injects LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u})
      (ordinalLCarrier (n : Ordinal.{u})) := by
  rintro ⟨graph, hgraph⟩
  let index := finiteOrdinalMemberIndex.{u} n
  let f : Nat → Fin n := fun k => index (hgraph.toFun (omegaNaturalMember k))
  have hf : Function.Injective f :=
    finiteOrdinalMemberIndex_injective n |>.comp
      (hgraph.toFun_injective.comp omegaNaturalMember_injective)
  exact (not_injective_infinite_finite f) hf

/-- The standard constructible `omega` is an internal initial ordinal.

The conclusion uses the set-coded `Equinumerous` relation.  To exclude a
bijection with a finite ordinal, the proof reverses its internally coded graph
and applies the ordinary finite pigeonhole principle to the induced function;
it does not compare ambient `ZFSet.card`s.
-/
theorem omegaLCarrier_isCardinal :
    IsCardinal LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u}) := by
  constructor
  · apply (isVonNeumannOrdinal_lCarrier_iff omegaLCarrier).2
    exact ZFSet.isOrdinal_toZFSet Ordinal.omega0
  · intro alpha halpha hequinumerous
    have halphaRaw : alpha.1 ∈ Ordinal.omega0.toZFSet := by
      simpa only [omegaLCarrier] using halpha
    rcases Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode
        alpha.1 |>.mp halphaRaw with ⟨n, hn⟩
    have halphaEq :
        alpha = ordinalLCarrier (n : Ordinal.{u}) := by
      apply Subtype.ext
      simpa only [ordinalLCarrier_val,
        Constructible.FiniteSequenceZF.natCode] using hn
    subst alpha
    exact not_injects_omega_finiteOrdinal n
      ((Equinumerous.symm_lCarrier hequinumerous).injects)

/-! ## The exact remaining GCH obligation -/

/-- The internal powerset witness supplied by the powerset axiom, expressed
using the relation-parametric predicate occurring in `ModelsGCH`. -/
theorem exists_powerSetOf_lCarrier
    (base : Constructible.Model.LCarrier.{u}) :
    ∃ power : Constructible.Model.LCarrier.{u},
      IsPowerSetOf LMem base power := by
  rcases Constructible.Model.exists_powerSetLCarrier base with
    ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  intro x
  change x.1 ∈ power.1 ↔ IsSubsetOf LMem x base
  rw [hpower x]
  constructor
  · intro hsubset z hz
    exact hsubset hz
  · intro hsubset z hz
    exact hsubset ⟨z, Constructible.mem_L_of_mem hz x.2⟩ hz

/-- GCH in `LCarrier` follows once every internal infinite cardinal's
internal powerset is internally equinumerous with its Hartogs successor.

This is only a reduction: constructing that bijection is the genuine
condensation/small-stage part of the proof and remains visible as `hpower`.
-/
theorem modelsGCH_lCarrier_of_powerSet_equinumerous_hartogs
    (hpower :
      ∀ (kappa power : Constructible.Model.LCarrier.{u}),
        IsCardinal LMem kappa →
        IsSubsetOf LMem omegaLCarrier kappa →
        IsPowerSetOf LMem kappa power →
        Equinumerous LMem power (internalHartogsLCarrier kappa)) :
    ModelsGCH (A := Constructible.Model.LCarrier.{u}) LMem := by
  refine ⟨omegaLCarrier, omegaLCarrier_isOmega,
    omegaLCarrier_isCardinal, ?_⟩
  intro kappa hkappa
  rcases exists_powerSetOf_lCarrier kappa with ⟨power, hpowerSet⟩
  refine ⟨internalHartogsLCarrier kappa, power,
    internalHartogsLCarrier_isSuccessorCardinal kappa hkappa.1,
    hpowerSet, ?_⟩
  exact hpower kappa power hkappa.1 hkappa.2 hpowerSet

end Constructible.ContinuumFormula
