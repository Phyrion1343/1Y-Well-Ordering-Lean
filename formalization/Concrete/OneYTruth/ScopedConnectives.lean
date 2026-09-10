import OneYTruth.ScopedReindex

/-! Convenient scope-only semantic rules; the formula syntax remains Mathlib's. -/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

def memAt (k : Nat) (I : Type u) {n : Nat} (i j : Fin n) :
    (language k I).BoundedFormula Empty n := .rel .mem ![.var (.inr i), .var (.inr j)]

def eqAt (k : Nat) (I : Type u) {n : Nat} (i j : Fin n) :
    (language k I).BoundedFormula Empty n := .equal (.var (.inr i)) (.var (.inr j))

theorem realize_memAt {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (i j : Fin n) (s : Fin n → A) :
    realize M (memAt k I i j) Empty.elim s ↔ M.mem (s i) (s j) := Iff.rfl

theorem realize_eqAt {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (i j : Fin n) (s : Fin n → A) :
    realize M (eqAt k I i j) Empty.elim s ↔ s i = s j := Iff.rfl

theorem realize_scoped_imp {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (φ ψ : (language k I).BoundedFormula Empty n) (s : Fin n → A) :
    realize M (φ.imp ψ) Empty.elim s ↔ (realize M φ Empty.elim s → realize M ψ Empty.elim s) := Iff.rfl

theorem realize_scoped_all {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (φ : (language k I).BoundedFormula Empty (n + 1)) (s : Fin n → A) :
    realize M φ.all Empty.elim s ↔ ∀ a : A, realize M φ Empty.elim (Fin.snoc s a) := Iff.rfl

theorem realize_scoped_ex {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (φ : (language k I).BoundedFormula Empty (n + 1)) (s : Fin n → A) :
    realize M φ.ex Empty.elim s ↔ ∃ a : A, realize M φ Empty.elim (Fin.snoc s a) := by
  letI := M.structure
  exact BoundedFormula.realize_ex

theorem realize_scoped_inf {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (φ ψ : (language k I).BoundedFormula Empty n) (s : Fin n → A) :
    realize M (φ ⊓ ψ) Empty.elim s ↔ (realize M φ Empty.elim s ∧ realize M ψ Empty.elim s) := by
  letI := M.structure
  exact BoundedFormula.realize_inf

theorem realize_scoped_sup {k : Nat} {I : Type u} {A : Type v} {n : Nat}
    (M : Interpretation k I A) (φ ψ : (language k I).BoundedFormula Empty n) (s : Fin n → A) :
    realize M (φ ⊔ ψ) Empty.elim s ↔ (realize M φ Empty.elim s ∨ realize M ψ Empty.elim s) := by
  letI := M.structure
  exact BoundedFormula.realize_sup

end OneYTruth
