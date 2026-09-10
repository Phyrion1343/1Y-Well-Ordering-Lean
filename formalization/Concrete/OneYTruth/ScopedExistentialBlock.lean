import OneYTruth.ScopeSyntax
import OneYTruth.UniformUnionFormula

/-! Literal finite existential prefixes in the mixed language. -/

namespace OneYTruth.ScopedExistentialBlock

open FirstOrder FirstOrder.Language

universe u v

def bind {k : Nat} {I : Type u} (n : Nat) : (m : Nat) →
    (language k I).BoundedFormula Empty (n + m) → (language k I).BoundedFormula Empty n
  | 0, φ => φ
  | m + 1, φ => bind n m φ.ex

theorem isSigmaOne_bind {k : Nat} {I : Type u} (n m : Nat)
    (φ : (language k I).BoundedFormula Empty (n + m)) (h : IsSigmaOne φ) :
    IsSigmaOne (bind n m φ) := by
  induction m with
  | zero => exact h
  | succ m ih => exact ih φ.ex (.ex h)

theorem realize_bind {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) (n m : Nat)
    (φ : (language k I).BoundedFormula Empty (n + m)) (p : Fin n → A) :
    realize M (bind n m φ) Empty.elim p ↔
      ∃ w : Fin m → A, realize M φ Empty.elim (Fin.append p w) := by
  induction m with
  | zero =>
    simp only [bind]
    constructor
    · intro h
      exact ⟨Fin.elim0, by simpa [Fin.append_elim0] using h⟩
    · rintro ⟨w,h⟩
      have hw : w = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simpa [hw,Fin.append_elim0] using h
  | succ m ih =>
    rw [bind, ih]
    simp only [realize_scoped_ex]
    constructor
    · rintro ⟨w,a,h⟩
      refine ⟨Fin.snoc w a, ?_⟩
      rw [Fin.append_snoc]
      exact h
    · rintro ⟨w,h⟩
      refine ⟨Fin.init w,w (Fin.last m), ?_⟩
      rw [← Fin.append_snoc, Fin.snoc_init_self]
      exact h

end OneYTruth.ScopedExistentialBlock
