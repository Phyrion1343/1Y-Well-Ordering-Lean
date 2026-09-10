import OneYTruth.Auxiliary
import Mathlib.ModelTheory.Skolem

/-!
# Countable Skolem hulls in the actual auxiliary language

The membership-plus-W language has two symbols. Its Skolem closure of any
countable seed is an actual countable elementary substructure. This is an
external construction; it does not assert that a hull is constructible or
that the expanded ambient structure satisfies Separation or Collection.
-/

namespace OneYTruth.Auxiliary

open FirstOrder FirstOrder.Language

universe u

instance : language.IsRelational := fun _ => inferInstance

private def relationTag : (Σ n, language.Relations n) → Bool
  | ⟨_, .mem⟩ => false
  | ⟨_, .truth⟩ => true

private theorem relationTag_injective : Function.Injective relationTag := by
  rintro ⟨_, r⟩ ⟨_, s⟩ h
  cases r <;> cases s <;> simp_all [relationTag]

instance : Countable (Σ n, language.Relations n) :=
  Function.Injective.countable relationTag_injective

instance : Countable (Σ n, language.Functions n) := by
  have : IsEmpty (Σ n, language.Functions n) := ⟨fun ⟨_, e⟩ => nomatch e⟩
  infer_instance

instance : Countable language.Symbols := by
  change Countable ((Σ n, language.Functions n) ⊕ (Σ n, language.Relations n))
  infer_instance

instance : Countable (Σ n, (language.sum language.skolem₁).Functions n) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact FirstOrder.Language.card_functions_sum_skolem₁_le.trans
    (max_le le_rfl Cardinal.mk_le_aleph0)

section Hull

variable {A : Type u} [Nonempty A] (M : Interpretation A)

/-- Closure under the genuine Mathlib Skolem functions for M. -/
noncomputable def skolemHull (seed : Set A) :
    @language.ElementarySubstructure A M.structure := by
  letI := M.structure
  exact (Substructure.closure (language.sum language.skolem₁) seed).elementarySkolem₁Reduct

theorem subset_skolemHull (seed : Set A) : seed ⊆ skolemHull M seed := by
  letI := M.structure
  exact Substructure.subset_closure

theorem skolemHull_mono {seed target : Set A} (h : seed ⊆ target) :
    (skolemHull M seed : Set A) ⊆ skolemHull M target := by
  letI := M.structure
  exact Substructure.closure_mono h

theorem countable_skolemHull {seed : Set A} (h : seed.Countable) :
    (skolemHull M seed : Set A).Countable := by
  letI := M.structure
  exact @Set.Countable.substructure_closure
    (language.sum language.skolem₁) A _ seed _ h

/-- The actual hull, not an assumed elementary substructure, supplies witnesses. -/
theorem witness_mem_skolemHull {seed : Set A} {n : Nat}
    (φ : language.BoundedFormula Empty (n + 1)) (xs : Fin n → A)
    (hxs : ∀ i, xs i ∈ seed) (a : A)
    (ha : realize M φ default (Fin.snoc xs a)) :
    ∃ b : A, b ∈ skolemHull M seed ∧ realize M φ default (Fin.snoc xs b) := by
  letI := M.structure
  let S := Substructure.closure (language.sum language.skolem₁) seed
  let f : (language.sum language.skolem₁).Functions n := .inr φ
  let b : A := FirstOrder.Language.Structure.funMap f xs
  refine ⟨b, ?_, ?_⟩
  · exact S.fun_mem f xs (fun i => Substructure.subset_closure (hxs i))
  · exact Classical.epsilon_spec (p := fun b => φ.Realize default (Fin.snoc xs b)) ⟨a, ha⟩

end Hull

end OneYTruth.Auxiliary
