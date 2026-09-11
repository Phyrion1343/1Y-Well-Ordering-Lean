/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaRestrictionLCarrier

/-!
# Textbook function-graph formulas over L

This file gives the exact `LCarrier` semantics of the graph-value and
function-on-domain formulas used in the textbook local recursion predicate.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_graphValueFormulaAt_lCarrier_iff {m : Nat}
    (graph input value : Fin m) (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (graphValueFormulaAt graph input value) s ↔
      ZFSet.pair (s input).1 (s value).1 ∈ (s graph).1 := by
  rw [graphValueFormulaAt]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨pair, hpairEq, hpairGraph⟩
    have hpair :=
      (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last m) input.castSucc value.castSucc (snoc s pair)).mp
        hpairEq
    have hpairRaw : pair.1 = ZFSet.pair (s input).1 (s value).1 := by
      simpa only [snoc_last, snoc_castSucc] using hpair
    simp only [snoc_last, snoc_castSucc] at hpairGraph
    change pair.1 ∈ (s graph).1 at hpairGraph
    simpa only [hpairRaw] using hpairGraph
  · intro hpairGraph
    let pair : LCarrier.{u} :=
      ⟨ZFSet.pair (s input).1 (s value).1,
        mem_L_of_mem hpairGraph (s graph).2⟩
    refine ⟨pair, ?_, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last m) input.castSucc value.castSucc (snoc s pair)).mpr
      simp only [snoc_last, snoc_castSucc, pair]
    · simp only [snoc_last, snoc_castSucc]
      change pair.1 ∈ (s graph).1
      simpa only [pair] using hpairGraph

@[simp]
theorem satisfies_functionGraphOnFormulaAt_lCarrier_iff {m : Nat}
    (graph domain : Fin m) (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (functionGraphOnFormulaAt graph domain) s ↔
      ((∀ input : LCarrier.{u}, input.1 ∈ (s domain).1 →
          ∃ value : LCarrier.{u},
            ZFSet.pair input.1 value.1 ∈ (s graph).1 ∧
              ∀ other : LCarrier.{u},
                ZFSet.pair input.1 other.1 ∈ (s graph).1 →
                  other = value) ∧
        ∀ pair : LCarrier.{u}, pair.1 ∈ (s graph).1 →
          ∃ input : LCarrier.{u}, input.1 ∈ (s domain).1 ∧
            ∃ value : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 value.1) := by
  simp only [functionGraphOnFormulaAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_all,
    FOFormula.satisfies_imp,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_kuratowskiPairEqAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

end

end Constructible.Model
