import OneYTruth.SigmaFiniteConjunction

/-! A finite indexed family of actual Sigma-one checks, in one Sigma-one
formula with exact conjunct-by-conjunct semantics. -/

namespace OneYTruth.FiniteSigmaChecks

open FirstOrder FirstOrder.Language

universe u v

noncomputable def formula {K : Nat} {J : Type u} {n m : Nat}
    (checks : Fin m → (language K J).BoundedFormula Empty n)
    (h : ∀ i, IsSigmaOne (checks i)) : (language K J).BoundedFormula Empty n :=
  (exists_sigmaConjunction.{u,v} (List.ofFn checks) (by
    intro φ hφ
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hφ
    exact h i)).choose

theorem formula_isSigmaOne {K : Nat} {J : Type u} {n m : Nat}
    (checks : Fin m → (language K J).BoundedFormula Empty n)
    (h : ∀ i, IsSigmaOne (checks i)) : IsSigmaOne (formula.{u,v} checks h) :=
  (exists_sigmaConjunction.{u,v} (List.ofFn checks) (by
    intro φ hφ
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hφ
    exact h i)).choose_spec.1

theorem realize_formula {K : Nat} {J : Type u} {n m : Nat}
    (checks : Fin m → (language K J).BoundedFormula Empty n)
    (h : ∀ i, IsSigmaOne (checks i)) {A : Type v}
    (N : Interpretation K J A) (p : Fin n → A) :
    realize N (formula.{u,v} checks h) Empty.elim p ↔
      ∀ i, realize N (checks i) Empty.elim p := by
  have he := (exists_sigmaConjunction.{u,v} (List.ofFn checks) (by
    intro φ hφ
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hφ
    exact h i)).choose_spec.2 A N p
  change realize N (formula.{u,v} checks h) Empty.elim p ↔
    ∀ φ ∈ List.ofFn checks, realize N φ Empty.elim p at he
  simpa [List.mem_ofFn] using he

end OneYTruth.FiniteSigmaChecks
