/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.HartogsSuccessor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInfiniteCardinalAbsorption

/-!
# The Hartogs ordinal of an internally infinite cardinal is a limit

The proof is the standard successor-shift argument.  A cardinal base belongs
to its Hartogs ordinal, excluding zero.  If the Hartogs ordinal were
`alpha + 1`, its defining property would provide an internal injection
`alpha -> kappa`; finite absorption then extends this to
`alpha + 1 -> kappa`, contradicting the Hartogs obstruction.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The internal Hartogs ordinal of an internal cardinal is nonzero. -/
theorem internalHartogsOrdinal_ne_zero_of_isCardinal
    (kappa : LCarrier.{u})
    (hkappa : IsCardinal LMem kappa) :
    internalHartogsOrdinal kappa ≠ 0 := by
  intro hzero
  have hkappaMem : kappa.1 ∈ (internalHartogsLCarrier kappa).1 :=
    (internalHartogsLCarrier_isHartogsNumber kappa).base_mem_lCarrier
      hkappa
  have hhartogsEmpty :
      internalHartogsLCarrier kappa = emptyLCarrier := by
    simp only [internalHartogsLCarrier, hzero, ordinalLCarrier_zero]
  rw [hhartogsEmpty] at hkappaMem
  exact not_mem_emptyLCarrier kappa hkappaMem

/-- If `kappa` contains omega, its internal Hartogs ordinal cannot be a
successor. -/
theorem internalHartogsOrdinal_ne_successor_of_omega_subset
    (kappa : LCarrier.{u})
    (homega : IsSubsetOf LMem omegaLCarrier kappa)
    (alpha : Ordinal.{u}) :
    internalHartogsOrdinal kappa ≠ Order.succ alpha := by
  intro hsuccessor
  have hhartogs := internalHartogsLCarrier_isHartogsNumber kappa
  have halphaMem :
      (ordinalLCarrier alpha).1 ∈
        (internalHartogsLCarrier kappa).1 := by
    change (ordinalLCarrier alpha).1 ∈
      (ordinalLCarrier (internalHartogsOrdinal kappa)).1
    apply (ordinalLCarrier_mem_ordinalLCarrier_iff
      (internalHartogsOrdinal kappa) alpha).mpr
    rw [hsuccessor]
    exact Order.lt_succ alpha
  have halphaInjects :
      Injects LMem (ordinalLCarrier alpha) kappa :=
    hhartogs.2.2 (ordinalLCarrier alpha) halphaMem
  have hsuccessorInjects :
      Injects LMem (ordinalLCarrier (Order.succ alpha)) kappa :=
    injects_successorOrdinal_of_omega_subset_lCarrier
      homega halphaInjects
  apply hhartogs.2.1
  simpa only [internalHartogsLCarrier, hsuccessor] using
    hsuccessorInjects

/-- The internal Hartogs ordinal of an internally infinite cardinal is a
nonzero limit ordinal. -/
theorem internalHartogsOrdinal_isSuccLimit
    (kappa : LCarrier.{u})
    (hkappa : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem omegaLCarrier kappa) :
    Order.IsSuccLimit (internalHartogsOrdinal kappa) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit
      (internalHartogsOrdinal kappa) with
    hzero | ⟨alpha, hsuccessor⟩ | hlimit
  · exact (internalHartogsOrdinal_ne_zero_of_isCardinal
      kappa hkappa hzero).elim
  · exact (internalHartogsOrdinal_ne_successor_of_omega_subset
      kappa homega alpha hsuccessor.symm).elim
  · exact hlimit

end

end Constructible.ContinuumFormula
