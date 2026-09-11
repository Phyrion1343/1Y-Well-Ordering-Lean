/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFFunctionGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph

/-!
# Replacement function graphs in the constructible universe

Given a formula with one unique `LCarrier` output on an internal domain,
Replacement is applied to the formula which outputs the Kuratowski pair of
the input and value.  The result is an actual member of `L` whose elements
are exactly those graph pairs.  No external `ZFSet.range` is used.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Exact semantics of the pair-output formula -/

@[simp]
theorem satisfies_replacementGraphFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (x q : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementGraphFormula phi)
        (snoc (snoc params x) q) ↔
      ∃ y : LCarrier.{u},
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y) ∧
          q.1 = ZFSet.pair x.1 y.1 := by
  simp only [replacementGraphFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    comp_replacementGraphPredicateRename,
    replacementGraphPairIndex, replacementGraphInputIndex,
    replacementGraphValueIndex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro _hy
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [snoc_last, snoc_castSucc]

/-! ## The actual Replacement graph -/

/-- Formula-functional Replacement on `LCarrier` produces the actual
Kuratowski graph, with an exact raw-membership specification. -/
theorem exists_replacementFunctionGraphLCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u})
    (hfun : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
      ExistsUnique fun y : LCarrier.{u} =>
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y)) :
    ∃ graph : LCarrier.{u}, ∀ q : ZFSet.{u},
      q ∈ graph.1 ↔
        ∃ x : LCarrier.{u}, x.1 ∈ domain.1 ∧
          ∃ y : LCarrier.{u},
            FOFormula.Satisfies LMem phi
              (snoc (snoc params x) y) ∧
            q = ZFSet.pair x.1 y.1 := by
  have hpairFun : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
      ExistsUnique fun q : LCarrier.{u} =>
        FOFormula.Satisfies LMem (replacementGraphFormula phi)
          (snoc (snoc params x) q) := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    let q : LCarrier.{u} := orderedPairLCarrier x y
    refine ⟨q, ?_, ?_⟩
    · apply (satisfies_replacementGraphFormula_lCarrier
        phi params x q).mpr
      exact ⟨y, hy, rfl⟩
    · intro q' hq'
      rcases (satisfies_replacementGraphFormula_lCarrier
          phi params x q').mp hq' with
        ⟨y', hy', hq'⟩
      have hyy' : y' = y := hyUnique y' hy'
      apply Subtype.ext
      rw [hq', hyy']
      rfl
  rcases exists_replacementLCarrier
      (replacementGraphFormula phi) params domain hpairFun with
    ⟨graph, hgraph⟩
  refine ⟨graph, ?_⟩
  intro q
  constructor
  · intro hq
    let qL : LCarrier.{u} := ⟨q, mem_L_of_mem hq graph.2⟩
    rcases (hgraph qL).mp hq with ⟨x, hx, hpairFormula⟩
    rcases (satisfies_replacementGraphFormula_lCarrier
        phi params x qL).mp hpairFormula with
      ⟨y, hy, hqPair⟩
    exact ⟨x, hx, y, hy, hqPair⟩
  · rintro ⟨x, hx, y, hy, hqPair⟩
    have hqL : q ∈ L := by
      rw [hqPair]
      exact orderedPair_mem_L x.2 y.2
    let qL : LCarrier.{u} := ⟨q, hqL⟩
    apply (hgraph qL).mpr
    refine ⟨x, hx, ?_⟩
    apply (satisfies_replacementGraphFormula_lCarrier
      phi params x qL).mpr
    exact ⟨y, hy, hqPair⟩

end

end Constructible.Model
