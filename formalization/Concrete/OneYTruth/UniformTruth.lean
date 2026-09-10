import OneYTruth.TowerReducts
import OneYTruth.Auxiliary

/-!
# An actual external set for the finite auxiliary predicate W

The set below collects the truth pairs from all blocks and all stages
strictly below the fixed bound. Its interpretation realizes the previously
defined finite auxiliary language. This does not place W in any specified
constructible level or establish a Skolem club.
-/

namespace OneYTruth.ExternalTower

open FirstOrder FirstOrder.Language Constructible FormulaCode
open Constructible.FiniteSequenceZF

universe u v

abbrev OpenStage (κ : Ordinal.{u}) := Nat × {η : Ordinal.{u} // η < κ}

def closeStage {κ : Ordinal.{u}} (s : OpenStage κ) : Stage κ :=
  (s.1, ⟨s.2.val, s.2.property.le⟩)

abbrev UniformWitness {κ : Ordinal.{u}} (U : ZFSet.{u}) :=
  Σ s : OpenStage κ, ZFCarrier (truth U (closeStage s))

/-- A single actual set, indexed by the block and ordinal stage. -/
noncomputable def uniformSet {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : @UniformWitness κ U =>
    ZFSet.pair (stageCode (closeStage w.1)) w.2.val)

theorem mem_uniformSet_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) (b ξ p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair b ξ) p ∈ @uniformSet κ U ↔
    ∃ k : Nat, b = natCode k ∧ ∃ η : {η : Ordinal.{u} // η < κ},
      ξ = η.val.toZFSet ∧ p ∈ truth U (k, ⟨η.val, η.property.le⟩) := by
  constructor
  · intro h
    obtain ⟨⟨⟨k, η⟩, ⟨q, hq⟩⟩, heq⟩ := ZFSet.mem_range.mp h
    obtain ⟨hindex, hpair⟩ := ZFSet.pair_inj.mp heq
    obtain ⟨hb, hξ⟩ := ZFSet.pair_inj.mp hindex
    refine ⟨k, hb.symm, η, hξ.symm, ?_⟩
    change q = p at hpair
    subst q
    exact hq
  · rintro ⟨k, rfl, η, rfl, hp⟩
    exact ZFSet.mem_range_self (f := fun w : @UniformWitness κ U =>
      ZFSet.pair (stageCode (closeStage w.1)) w.2.val) ⟨(k, η), ⟨p, hp⟩⟩

/-- Fixing a block gives exactly its uniform diagonal. -/
theorem mem_uniformSet_at_block_iff {κ : Ordinal.{u}} (U : ZFSet.{u})
    (k : Nat) (ξ p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natCode k) ξ) p ∈ @uniformSet κ U ↔
    ∃ η : {η : Ordinal.{u} // η < κ},
      ξ = η.val.toZFSet ∧ p ∈ truth U (k, ⟨η.val, η.property.le⟩) := by
  rw [mem_uniformSet_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    have hkj : k = j := natCode_injective hj
    simpa only [hkj] using h
  · intro h
    exact ⟨k, rfl, h⟩

/-- The intended interpretation of the fixed finite auxiliary language. -/
noncomputable def auxiliaryInterpretation {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    Auxiliary.Interpretation (ZFCarrier U) where
  mem a b := a.val ∈ b.val
  truth b ξ e a := ZFSet.pair (ZFSet.pair b.val ξ.val) (ZFSet.pair e.val a.val) ∈
    @uniformSet κ U

/-- Actual natural-number and ordinal parameters recover the canonical local tower. -/
theorem auxiliaryReduct_interpretation {κ : Ordinal.{u}} (U : ZFSet.{u}) (k : Nat)
    {η : Ordinal.{u}} (hηκ : η ≤ κ)
    (block : Fin (k + 1) → ZFCarrier U)
    (hblock : ∀ j, (block j).val = natCode j.val)
    (index : {ξ : Ordinal.{u} // ξ < η} → ZFCarrier U)
    (hindex : ∀ ξ, (index ξ).val = ξ.val.toZFSet) :
    Auxiliary.reduct (@auxiliaryInterpretation κ U) block index =
      interpretation U (k, ⟨η, hηκ⟩) := by
  change Interpretation.mk _ _ _ = Interpretation.mk _ _ _
  congr 1
  · funext j ξ e a
    apply propext
    change ZFSet.pair (ZFSet.pair (block j.castSucc).val ξ.val)
      (ZFSet.pair e.val a.val) ∈ @uniformSet κ U ↔ _
    rw [hblock, mem_uniformSet_at_block_iff]
    rfl
  · funext ξ e a
    apply propext
    change ZFSet.pair (ZFSet.pair (block (Fin.last k)).val (index ξ).val)
      (ZFSet.pair e.val a.val) ∈ @uniformSet κ U ↔
      ZFSet.pair e.val a.val ∈ truth U (k, ⟨ξ.val, le_trans ξ.property.le hηκ⟩)
    rw [hblock, hindex, mem_uniformSet_at_block_iff]
    constructor
    · rintro ⟨δ, hδ, ht⟩
      have heq : δ.val = ξ.val := Ordinal.toZFSet_injective hδ.symm
      simpa only [heq, Fin.val_last] using ht
    · intro ht
      exact ⟨⟨ξ.val, lt_of_lt_of_le ξ.property hηκ⟩, rfl, ht⟩

/-- The finite auxiliary translation is correct for the actual external tower. -/
theorem realize_auxiliaryTranslate_interpretation {κ : Ordinal.{u}} (U : ZFSet.{u})
    (k : Nat) {η : Ordinal.{u}} (hηκ : η ≤ κ)
    (block : Fin (k + 1) → ZFCarrier U)
    (hblock : ∀ j, (block j).val = natCode j.val)
    (index : {ξ : Ordinal.{u} // ξ < η} → ZFCarrier U)
    (hindex : ∀ ξ, (index ξ).val = ξ.val.toZFSet) {α : Type v} {n : Nat}
    (φ : (language k {ξ : Ordinal.{u} // ξ < η}).BoundedFormula α n)
    (v : α → ZFCarrier U) (xs : Fin n → ZFCarrier U) :
    Auxiliary.realize (@auxiliaryInterpretation κ U) (Auxiliary.translate φ)
      (Sum.elim v (Sum.elim block index)) xs ↔
    OneYTruth.realize (interpretation U (k, ⟨η, hηκ⟩)) φ v xs := by
  rw [Auxiliary.realize_translate,
    auxiliaryReduct_interpretation U k hηκ block hblock index hindex]

end OneYTruth.ExternalTower
