import OneYTruth.ScopeSyntax

/-! Finite conjunctions are explicitly put back into the genuine Sigma-one
fragment. No unrestricted closure of the syntactic fragment is assumed. -/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

theorem IsDeltaZero.inf {k : Nat} {I : Type u} {n : Nat}
    {φ ψ : (language k I).BoundedFormula Empty n} (hφ : IsDeltaZero φ) (hψ : IsDeltaZero ψ) :
    IsDeltaZero (φ ⊓ ψ) := .imp (.imp hφ (.imp hψ .falsum)) .falsum

theorem exists_delta_sigmaConj {k : Nat} {I : Type u} {n : Nat}
    (φ ψ : (language k I).BoundedFormula Empty n) (hφ : IsDeltaZero φ) (hψ : IsSigmaOne ψ) :
    ∃ χ : (language k I).BoundedFormula Empty n, IsSigmaOne χ ∧
      ∀ (A : Type v) (M : Interpretation k I A) (s : Fin n → A),
        realize M χ Empty.elim s ↔ realize M φ Empty.elim s ∧ realize M ψ Empty.elim s := by
  induction hψ with
  | deltaZero hψ =>
      exact ⟨φ ⊓ _, .deltaZero (hφ.inf hψ), fun A M s => realize_scoped_inf M _ _ s⟩
  | @ex n ψ hψ ih =>
      obtain ⟨χ, hχ, hc⟩ := ih (renameScope Fin.castSucc φ) (hφ.renameScope Fin.castSucc)
      refine ⟨χ.ex, .ex hχ, ?_⟩
      intro A M s
      rw [realize_scoped_ex, realize_scoped_ex]
      have hs (a : A) : Fin.snoc s a ∘ Fin.castSucc = s := by funext i; simp
      simp only [hc A M, realize_renameScope, hs]
      constructor
      · rintro ⟨a, hφa, hψa⟩
        exact ⟨hφa, a, hψa⟩
      · rintro ⟨hφa, a, hψa⟩
        exact ⟨a, hφa, hψa⟩

theorem exists_sigmaConj {k : Nat} {I : Type u} {n : Nat}
    (φ ψ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ) (hψ : IsSigmaOne ψ) :
    ∃ χ : (language k I).BoundedFormula Empty n, IsSigmaOne χ ∧
      ∀ (A : Type v) (M : Interpretation k I A) (s : Fin n → A),
        realize M χ Empty.elim s ↔ realize M φ Empty.elim s ∧ realize M ψ Empty.elim s := by
  induction hφ with
  | deltaZero hφ => exact exists_delta_sigmaConj _ _ hφ hψ
  | @ex n φ hφ ih =>
      obtain ⟨χ, hχ, hc⟩ := ih (renameScope Fin.castSucc ψ) (hψ.renameScope Fin.castSucc)
      refine ⟨χ.ex, .ex hχ, ?_⟩
      intro A M s
      rw [realize_scoped_ex, realize_scoped_ex]
      have hs (a : A) : Fin.snoc s a ∘ Fin.castSucc = s := by funext i; simp
      simp only [hc A M, realize_renameScope, hs]
      constructor
      · rintro ⟨a, hφa, hψa⟩
        exact ⟨⟨a, hφa⟩, hψa⟩
      · rintro ⟨⟨a, hφa⟩, hψa⟩
        exact ⟨a, hφa, hψa⟩

theorem exists_sigmaConjunction {k : Nat} {I : Type u} {n : Nat}
    (Γ : List ((language k I).BoundedFormula Empty n))
    (hΓ : ∀ φ ∈ Γ, IsSigmaOne φ) :
    ∃ χ : (language k I).BoundedFormula Empty n, IsSigmaOne χ ∧
      ∀ (A : Type v) (M : Interpretation k I A) (s : Fin n → A),
        realize M χ Empty.elim s ↔ ∀ φ ∈ Γ, realize M φ Empty.elim s := by
  induction Γ with
  | nil =>
      refine ⟨.imp .falsum .falsum, .deltaZero (.imp .falsum .falsum), ?_⟩
      intro A M s
      simp only [List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (fun h => h)
  | cons φ Γ ih =>
      obtain ⟨ψ, hψ, hp⟩ := ih (fun θ hθ => hΓ θ (List.mem_cons_of_mem φ hθ))
      obtain ⟨χ, hχ, hc⟩ := exists_sigmaConj φ ψ (hΓ φ List.mem_cons_self) hψ
      refine ⟨χ, hχ, ?_⟩
      intro A M s
      rw [hc A M s, hp A M s]
      simp only [List.forall_mem_cons]

noncomputable def sigmaConjFormula {k : Nat} {I : Type u} {n : Nat}
    (φ ψ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ) (hψ : IsSigmaOne ψ) :
    (language k I).BoundedFormula Empty n :=
  (exists_sigmaConj.{u, v} φ ψ hφ hψ).choose

theorem sigmaConjFormula_isSigmaOne {k : Nat} {I : Type u} {n : Nat}
    (φ ψ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ) (hψ : IsSigmaOne ψ) :
    IsSigmaOne (sigmaConjFormula.{u, v} φ ψ hφ hψ) :=
  (exists_sigmaConj.{u, v} φ ψ hφ hψ).choose_spec.1

theorem realize_sigmaConjFormula {k : Nat} {I : Type u} {n : Nat}
    (φ ψ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ) (hψ : IsSigmaOne ψ)
    {A : Type v} (M : Interpretation k I A) (s : Fin n → A) :
    realize M (sigmaConjFormula.{u, v} φ ψ hφ hψ) Empty.elim s ↔
      realize M φ Empty.elim s ∧ realize M ψ Empty.elim s :=
  (exists_sigmaConj.{u, v} φ ψ hφ hψ).choose_spec.2 A M s

end OneYTruth
