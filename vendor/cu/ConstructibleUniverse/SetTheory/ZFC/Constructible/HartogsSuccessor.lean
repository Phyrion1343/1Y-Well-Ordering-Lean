/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalSchroederBernstein

/-!
# Hartogs numbers as successor cardinals

This file isolates the one use of the internal Cantor--Schroeder--Bernstein
theorem needed to identify the Hartogs number of an internal cardinal with
its successor cardinal.  Until an unconditional internal CSB construction is
available, the relevant antisymmetry property is kept as an explicit
hypothesis.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-- The internal Cantor--Schroeder--Bernstein principle for a membership
structure.

The conclusion requires a bijection whose graph is itself constructible; an
ambient Lean equivalence is therefore not sufficient.
-/
def InternalInjectionAntisymm {A : Type u} (E : A -> A -> Prop) : Prop :=
  forall {x y : A},
    Injects E x y -> Injects E y x -> Equinumerous E x y

/-- An internal cardinal cannot internally inject into a smaller ordinal.

The inclusion of the smaller ordinal into the cardinal is internally
represented by the identity graph.  Internal CSB would turn injections in
both directions into the forbidden bijection.
-/
theorem IsCardinal.not_injects_of_mem_lCarrier
    {smaller cardinal : Constructible.Model.LCarrier.{u}}
    (hcardinal : IsCardinal Constructible.Model.lCarrierMem cardinal)
    (hsmaller : Constructible.Model.lCarrierMem smaller cardinal)
    (hantisymm : InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem) :
    Not (Injects Constructible.Model.lCarrierMem cardinal smaller) := by
  intro hback
  have hforward :
      Injects Constructible.Model.lCarrierMem smaller cardinal :=
    injects_of_subset_lCarrier (fun z hz =>
      hcardinal.1.1 smaller hsmaller z hz)
  exact hcardinal.2 smaller hsmaller (hantisymm hforward hback)

/-- A cardinal belongs to its internal Hartogs number. -/
theorem IsHartogsNumber.base_mem_lCarrier
    {base hartogs : Constructible.Model.LCarrier.{u}}
    (hhartogs : IsHartogsNumber Constructible.Model.lCarrierMem base hartogs)
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    Constructible.Model.lCarrierMem base hartogs := by
  obtain ⟨alpha, rfl⟩ :=
    exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal base hbase.1
  obtain ⟨beta, rfl⟩ :=
    exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal hartogs hhartogs.1
  change
    (Constructible.Model.ordinalLCarrier alpha).1 ∈
      (Constructible.Model.ordinalLCarrier beta).1
  rw [Constructible.Model.ordinalLCarrier_mem_ordinalLCarrier_iff]
  by_contra hnotlt
  have hle : beta <= alpha := le_of_not_gt hnotlt
  apply hhartogs.2.1
  apply injects_of_subset_lCarrier
  intro z hz
  obtain ⟨gamma, hgamma, hvalue⟩ := Ordinal.mem_toZFSet_iff.mp hz
  apply Ordinal.mem_toZFSet_iff.mpr
  exact ⟨gamma, lt_of_lt_of_le hgamma hle, hvalue⟩

/-- Conditional identification of the internal Hartogs number with the
successor cardinal of `base`.

All graph operations except Cantor--Schroeder--Bernstein have already been
constructed inside `L`; consequently CSB is the only explicit hypothesis.
-/
theorem internalHartogsLCarrier_isSuccessorCardinal_of
    (base : Constructible.Model.LCarrier.{u})
    (hbase : IsCardinal Constructible.Model.lCarrierMem base)
    (hantisymm : InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem) :
    IsSuccessorCardinal Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) := by
  let hartogs := internalHartogsLCarrier base
  have hhartogs :
      IsHartogsNumber Constructible.Model.lCarrierMem base hartogs :=
    internalHartogsLCarrier_isHartogsNumber base
  refine ⟨hbase, internalHartogsLCarrier_isCardinal base,
    hhartogs.base_mem_lCarrier hbase, ?_⟩
  rintro ⟨intermediate, hintermediate, hbaseIntermediate,
    hintermediateHartogs⟩
  exact (hintermediate.not_injects_of_mem_lCarrier
      hbaseIntermediate hantisymm)
    (hhartogs.2.2 intermediate hintermediateHartogs)

/-- Under internal CSB, every internal cardinal has a successor cardinal,
with the canonical internal Hartogs number as witness. -/
theorem exists_internalSuccessorCardinal_of
    (hantisymm : InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem)
    {base : Constructible.Model.LCarrier.{u}}
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    exists next : Constructible.Model.LCarrier.{u},
      IsSuccessorCardinal Constructible.Model.lCarrierMem base next :=
  ⟨internalHartogsLCarrier base,
    internalHartogsLCarrier_isSuccessorCardinal_of
      base hbase hantisymm⟩

/-! ## Unconditional specialization to `LCarrier` -/

/-- The internally constructed Cantor--Schroeder--Bernstein bijection
discharges the antisymmetry interface used above. -/
theorem internalInjectionAntisymm_lCarrier :
    InternalInjectionAntisymm
      (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem := by
  intro x y hxy hyx
  exact injects_antisymm_lCarrier hxy hyx

/-- The internal Hartogs number of a cardinal is its successor cardinal. -/
theorem internalHartogsLCarrier_isSuccessorCardinal
    (base : Constructible.Model.LCarrier.{u})
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    IsSuccessorCardinal Constructible.Model.lCarrierMem base
      (internalHartogsLCarrier base) :=
  internalHartogsLCarrier_isSuccessorCardinal_of
    base hbase internalInjectionAntisymm_lCarrier

/-- Every internal cardinal has a successor cardinal, canonically supplied
by its internal Hartogs number. -/
theorem exists_internalSuccessorCardinal
    {base : Constructible.Model.LCarrier.{u}}
    (hbase : IsCardinal Constructible.Model.lCarrierMem base) :
    ∃ next : Constructible.Model.LCarrier.{u},
      IsSuccessorCardinal Constructible.Model.lCarrierMem base next :=
  ⟨internalHartogsLCarrier base,
    internalHartogsLCarrier_isSuccessorCardinal base hbase⟩

end Constructible.ContinuumFormula
