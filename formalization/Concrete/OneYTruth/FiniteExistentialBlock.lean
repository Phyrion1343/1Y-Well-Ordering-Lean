import OneYTruth.UniformUnionFormula

/-! Finite existential blocks in the actual pure set-theoretic syntax. -/

namespace OneYTruth.FiniteExistentialBlock

open Constructible

universe u

def bind (n : Nat) : (m : Nat) → FOFormula (n + m) → FOFormula n
  | 0, φ => φ
  | m + 1, φ => bind n m (.ex φ)

theorem satisfies_bind {A : Type u} (E : A → A → Prop) (n m : Nat)
    (φ : FOFormula (n + m)) (p : Tuple A n) :
    FOFormula.Satisfies E (bind n m φ) p ↔
      ∃ w : Tuple A m, FOFormula.Satisfies E φ (Fin.append p w) := by
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
    change (∃ w : Tuple A m, ∃ a : A, FOFormula.Satisfies E φ (snoc (Fin.append p w) a)) ↔ _
    constructor
    · rintro ⟨w,a,h⟩
      refine ⟨Fin.snoc w a, ?_⟩
      rw [Fin.append_snoc, ← constructible_snoc_eq]
      exact h
    · rintro ⟨w,h⟩
      refine ⟨Fin.init w,w (Fin.last m), ?_⟩
      rw [constructible_snoc_eq, ← Fin.append_snoc, Fin.snoc_init_self]
      exact h

end OneYTruth.FiniteExistentialBlock

