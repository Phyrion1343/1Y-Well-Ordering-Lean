import OneYTruth.SigmaFiniteConjunction
import OneYTruth.ClosedSigmaMaps

/-! Exact reflection of finitely many jointly specified witnesses, keeping
the displayed prefix parameters fixed. The actual diagram matrix must
still be supplied; this lemma does not assume a reflected representation. -/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w

def existsSuffix {k : Nat} {I : Type u} {n : Nat} :
    (m : Nat) → (language k I).BoundedFormula Empty (n+m) → (language k I).BoundedFormula Empty n
  | 0, φ => φ
  | m+1, φ => existsSuffix m φ.ex

theorem existsSuffix_isSigmaOne {k : Nat} {I : Type u} {n m : Nat}
    (φ : (language k I).BoundedFormula Empty (n+m)) (hφ : IsSigmaOne φ) :
    IsSigmaOne (existsSuffix m φ) := by
  induction m with
  | zero => exact hφ
  | succ m ih => exact ih φ.ex (.ex hφ)

theorem realize_existsSuffix {k : Nat} {I : Type u} {A : Type v} {n m : Nat}
    (M : Interpretation k I A) (φ : (language k I).BoundedFormula Empty (n+m)) (p : Fin n → A) :
    realize M (existsSuffix m φ) Empty.elim p ↔
      ∃ xs : Fin m → A, realize M φ Empty.elim (Fin.append p xs) := by
  induction m with
  | zero =>
      change realize M φ Empty.elim p ↔ ∃ xs : Fin 0 → A, realize M φ Empty.elim (Fin.append p xs)
      simp only [Fin.append_right_nil]
      exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ m ih =>
      change realize M (existsSuffix m φ.ex) Empty.elim p ↔ _
      rw [ih]
      simp only [realize_scoped_ex]
      constructor
      · rintro ⟨xs, a, h⟩
        exact ⟨Fin.snoc xs a, by rwa [Fin.append_snoc]⟩
      · rintro ⟨xs, h⟩
        refine ⟨Fin.init xs, xs (Fin.last m), ?_⟩
        rwa [← Fin.append_snoc, Fin.snoc_init_self]

theorem ClosedSigmaOneMap.reflect_finiteWitnesses
    {k : Nat} {I : Type u} {A : Type v} {B : Type w}
    {M : Interpretation k I A} {N : Interpretation k I B} {f : A → B}
    (hf : ClosedSigmaOneMap M N f) {n m : Nat}
    (φ : (language k I).BoundedFormula Empty (n+m)) (hφ : IsSigmaOne φ)
    (p : Fin n → A)
    (h : ∃ xs : Fin m → B, realize N φ Empty.elim (Fin.append (f ∘ p) xs)) :
    ∃ xs : Fin m → A, realize M φ Empty.elim (Fin.append p xs) := by
  apply (realize_existsSuffix M φ p).mp
  apply (hf n (existsSuffix m φ) (existsSuffix_isSigmaOne φ hφ) p).mp
  exact (realize_existsSuffix N φ (f ∘ p)).mpr h

theorem SigmaOneMap.reflect_finiteWitnesses
    {k : Nat} {I : Type u} {A : Type v} {B : Type w} [Nonempty A]
    {M : Interpretation k I A} {N : Interpretation k I B} {f : A → B}
    (hf : SigmaOneMap M N f) {n m : Nat}
    (φ : (language k I).BoundedFormula Empty (n+m)) (hφ : IsSigmaOne φ)
    (p : Fin n → A)
    (h : ∃ xs : Fin m → B, realize N φ Empty.elim (Fin.append (f ∘ p) xs)) :
    ∃ xs : Fin m → A, realize M φ Empty.elim (Fin.append p xs) :=
  ((sigmaOneMap_iff_closed M N f).mp hf).reflect_finiteWitnesses φ hφ p h

end OneYTruth
