import OneYTruth.DeltaZeroBridge
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Model

/-! Pure first-order translation without initial-model dependencies. -/
namespace OneYTruth
open Constructible Constructible.Model FirstOrder FirstOrder.Language
universe u v

def ofConstructibleFO (k : Nat) (I : Type v) : {n : Nat} →
    FOFormula n → (language k I).BoundedFormula Empty n
  | _, .mem i j => .rel .mem ![.var (.inr i), .var (.inr j)]
  | _, .eq i j => .equal (.var (.inr i)) (.var (.inr j))
  | _, .neg φ => (ofConstructibleFO k I φ).not
  | _, .conj φ ψ => ofConstructibleFO k I φ ⊓ ofConstructibleFO k I ψ
  | _, .ex φ => (ofConstructibleFO k I φ).ex

theorem realize_ofConstructibleFO {k : Nat} {I : Type v} {A : Type u}
    (N : Interpretation k I A) {n : Nat} (φ : FOFormula n) (xs : Fin n → A) :
    OneYTruth.realize N (ofConstructibleFO k I φ) Empty.elim xs ↔
      FOFormula.Satisfies N.mem φ xs := by
  classical
  induction φ with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => exact not_congr (ih xs)
  | conj φ ψ ihφ ihψ =>
    change (¬ (OneYTruth.realize N (ofConstructibleFO k I φ) Empty.elim xs →
      ¬ OneYTruth.realize N (ofConstructibleFO k I ψ) Empty.elim xs)) ↔ _
    rw [ihφ, ihψ]
    simp only [Classical.not_imp, not_not, FOFormula.Satisfies]
  | ex φ ih =>
    letI := N.structure
    change (BoundedFormula.ex _).Realize Empty.elim xs ↔ _
    rw [BoundedFormula.realize_ex]
    change (∃ a, OneYTruth.realize N (ofConstructibleFO k I φ) Empty.elim (Fin.snoc xs a)) ↔ _
    simp only [ih, FOFormula.Satisfies, constructible_snoc_eq]

end OneYTruth
