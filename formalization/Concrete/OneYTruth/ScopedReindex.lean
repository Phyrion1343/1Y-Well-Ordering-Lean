import OneYTruth.Language

/-!
# Arbitrary reindexing of the current finite variable scope

This uses Mathlib's existing conversion to a free-variable formula and
relabeling back into a finite scope. The semantics is proved explicitly.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

def reindexScoped {k : Nat} {I : Type u} {n m : Nat} (f : Fin n → Fin m)
    (φ : (language k I).BoundedFormula Empty n) : (language k I).BoundedFormula Empty m :=
  BoundedFormula.relabel (Sum.elim Empty.elim (fun i => Sum.inr (f i))) φ.toFormula

theorem realize_reindexScoped {k : Nat} {I : Type u} {A : Type v} {n m : Nat}
    (M : Interpretation k I A) (f : Fin n → Fin m)
    (φ : (language k I).BoundedFormula Empty n) (xs : Fin m → A) :
    OneYTruth.realize M (reindexScoped f φ) Empty.elim xs ↔
      OneYTruth.realize M φ Empty.elim (xs ∘ f) := by
  letI := M.structure
  change (BoundedFormula.relabel _ φ.toFormula).Realize Empty.elim xs ↔ _
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Empty.elim : Empty → A) (xs ∘ Fin.castAdd 0) ∘
      Sum.elim Empty.elim (fun i => Sum.inr (f i)) = Sum.elim Empty.elim (xs ∘ f) := by
    funext i
    cases i with
    | inl e => exact e.elim
    | inr => rfl
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  rfl

end OneYTruth
