import OneYTruth.ExternalTower
import OneYTruth.Translation

/-!
# The external tower has the required mixed reducts

These are equalities of the concrete interpretations constructed by the
bounded external recursion. In the cross-block equality the source index
codes must be actual elements of the common set domain. No elementary
submodel or reflection hypothesis is used.
-/

namespace OneYTruth.ExternalTower

open FirstOrder FirstOrder.Language Constructible FormulaCode

universe u v

/-- Increasing the stage only adds independently named symbols. -/
theorem restrictNames_interpretation {κ : Ordinal.{u}} (U : ZFSet.{u}) (k : Nat)
    {η ζ : Ordinal.{u}} (hηζ : η ≤ ζ) (hζκ : ζ ≤ κ) :
    (interpretation U (k, ⟨ζ, hζκ⟩)).restrictNames
      (fun ξ : {ξ : Ordinal.{u} // ξ < η} => ⟨ξ.val, lt_of_lt_of_le ξ.property hηζ⟩) =
    interpretation U (k, ⟨η, le_trans hηζ hζκ⟩) := rfl

/-- Named predicates in a lower block are the matching slices of its diagonal. -/
theorem diagonalReduct_interpretation {κ : Ordinal.{u}} (U : ZFSet.{u})
    {k K : Nat} (h : k < K) {η ζ : Ordinal.{u}} (hηκ : η ≤ κ) (hζκ : ζ ≤ κ)
    (code : {ξ : Ordinal.{u} // ξ < η} → ZFCarrier U)
    (hcode : ∀ ξ, (code ξ).val = ξ.val.toZFSet) :
    OneYTruth.diagonalReduct h (interpretation U (K, ⟨ζ, hζκ⟩)) code =
      interpretation U (k, ⟨η, hηκ⟩) := by
  change Interpretation.mk _ _ _ = Interpretation.mk _ _ _
  congr 1
  funext ξ e a
  apply propext
  change (∃ δ : {δ : Ordinal.{u} // δ < κ},
    (code ξ).val = δ.val.toZFSet ∧ ZFSet.pair e.val a.val ∈
      truth U (k, ⟨δ.val, δ.property.le⟩)) ↔
    ZFSet.pair e.val a.val ∈ truth U (k, ⟨ξ.val, le_trans ξ.property.le hηκ⟩)
  constructor
  · rintro ⟨δ, hδ, ht⟩
    have heq : δ.val = ξ.val := Ordinal.toZFSet_injective (hδ.symm.trans (hcode ξ))
    simpa only [heq] using ht
  · intro ht
    exact ⟨⟨ξ.val, lt_of_lt_of_le ξ.property hηκ⟩, hcode ξ, ht⟩

/-- The general translation theorem now applies to the canonical truth structures. -/
theorem realize_diagonalTranslate_interpretation {κ : Ordinal.{u}} (U : ZFSet.{u})
    {k K : Nat} (h : k < K) {η ζ : Ordinal.{u}} (hηκ : η ≤ κ) (hζκ : ζ ≤ κ)
    (code : {ξ : Ordinal.{u} // ξ < η} → ZFCarrier U)
    (hcode : ∀ ξ, (code ξ).val = ξ.val.toZFSet) {α : Type v} {n : Nat}
    (φ : (language k {ξ : Ordinal.{u} // ξ < η}).BoundedFormula α n)
    (v : α → ZFCarrier U) (xs : Fin n → ZFCarrier U) :
    OneYTruth.realize (interpretation U (K, ⟨ζ, hζκ⟩)) (diagonalTranslate h φ)
      (Sum.elim v code) xs ↔
    OneYTruth.realize (interpretation U (k, ⟨η, hηκ⟩)) φ v xs := by
  rw [realize_diagonalTranslate, diagonalReduct_interpretation U h hηκ hζκ code hcode]

end OneYTruth.ExternalTower
