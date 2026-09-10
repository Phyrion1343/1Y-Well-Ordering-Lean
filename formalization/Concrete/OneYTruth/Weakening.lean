import OneYTruth.Complexity
import OneYTruth.FiniteSupport

/-!
# Syntactic weakening of Σ₁-preserving maps

The relation below is defined by actual formula realization. No existence
of such maps, no internal truth certificate, and no initial club are assumed.
This module proves how any such map behaves under the concrete translations.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w z

/-- Preservation of the stated Σ₁ fragment, allowing free parameter families.
Each tested formula is finite; the whole family is not an internal model element. -/
def SigmaOneMap {k : Nat} {I : Type u} {A : Type v} {B : Type w}
    (M : Interpretation k I A) (N : Interpretation k I B) (f : A → B) : Prop :=
  ∀ {α : Type u} {n : Nat} (φ : (language k I).BoundedFormula α n),
    IsSigmaOne φ → ∀ (v : α → A) (xs : Fin n → A),
      realize N φ (f ∘ v) (f ∘ xs) ↔ realize M φ v xs

/-- Same-stage weakening is an actual reduct theorem. -/
theorem SigmaOneMap.restrictNames {k : Nat} {I J : Type u} {A : Type v} {B : Type w}
    {M : Interpretation k J A} {N : Interpretation k J B} {f : A → B}
    (hf : SigmaOneMap M N f) (g : I → J) :
    SigmaOneMap (M.restrictNames g) (N.restrictNames g) f := by
  intro α n φ hφ v xs
  rw [← realize_namedMap, ← realize_namedMap]
  exact hf _ (hφ.namedMap g) v xs

/-- Lower-block weakening, with the index parameters transported by the map. -/
theorem SigmaOneMap.diagonalReduct {k K : Nat} {I J : Type u} {A : Type v} {B : Type w}
    {M : Interpretation K J A} {N : Interpretation K J B} {f : A → B}
    (hf : SigmaOneMap M N f) (h : k < K) (codeA : I → A) (codeB : I → B)
    (hc : ∀ i, f (codeA i) = codeB i) :
    SigmaOneMap (diagonalReduct h M codeA) (diagonalReduct h N codeB) f := by
  intro α n φ hφ v xs
  rw [← realize_diagonalTranslate, ← realize_diagonalTranslate]
  have hv : f ∘ Sum.elim v codeA = Sum.elim (f ∘ v) codeB := by
    funext i
    cases i with
    | inl => rfl
    | inr i => exact hc i
  simpa only [hv] using hf (diagonalTranslate h φ) (hφ.diagonalTranslate h)
    (Sum.elim v codeA) xs

/-- For one formula, only finitely many index parameters must commute. -/
theorem SigmaOneMap.diagonal_formula_of_support
    {k K : Nat} {I J : Type u} [DecidableEq I] {A : Type v} {B : Type w}
    {M : Interpretation K J A} {N : Interpretation K J B} {f : A → B}
    (hf : SigmaOneMap M N f) (h : k < K) (codeA : I → A) (codeB : I → B)
    {α : Type u} {n : Nat} (φ : (language k I).BoundedFormula α n)
    (hφ : IsSigmaOne φ) (hc : ∀ i ∈ namedSupport φ, f (codeA i) = codeB i)
    (v : α → A) (xs : Fin n → A) :
    realize (OneYTruth.diagonalReduct h N codeB) φ (f ∘ v) (f ∘ xs) ↔
      realize (OneYTruth.diagonalReduct h M codeA) φ v xs := by
  have heq := realize_eq_of_namedSupport (OneYTruth.diagonalReduct h N codeB)
    (OneYTruth.diagonalReduct h N (f ∘ codeA)) φ rfl rfl
    (fun i hi => by simp only [OneYTruth.diagonalReduct, Function.comp_apply, hc i hi])
    (f ∘ v) (f ∘ xs)
  exact heq.trans ((hf.diagonalReduct h codeA (f ∘ codeA) (fun _ => rfl)) φ hφ v xs)

end OneYTruth
