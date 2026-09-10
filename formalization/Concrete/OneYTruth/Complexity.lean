import OneYTruth.Translation

/-!
# Set-theoretic bounded quantifiers and their translation

Mathlib's `BoundedFormula` bounds the number of variables in scope; it does
not mean a set-theoretic Δ₀ formula. The separate predicates below express
the latter notion and a finite existential prefix over it.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

/-- The genuine set-theoretic bounded universal quantifier `∀ x ∈ t, φ`. -/
def boundedAll {k : Nat} {I : Type u} {α : Type v} {n : Nat}
    (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) :
    (language k I).BoundedFormula α n :=
  .all (.imp (.rel .mem ![.var (.inr (Fin.last n)),
    renameTerm (Sum.map id Fin.castSucc) t]) φ)

/-- Δ₀ in the expanded relational language, with bounded membership quantifiers. -/
inductive IsDeltaZero {k : Nat} {I : Type u} {α : Type v} :
    {n : Nat} → (language k I).BoundedFormula α n → Prop
  | falsum {n} : IsDeltaZero (.falsum : (language k I).BoundedFormula α n)
  | equal {n} (t s : (language k I).Term (α ⊕ Fin n)) : IsDeltaZero (.equal t s)
  | rel {n m} (r : Relation k I m) (ts : Fin m → (language k I).Term (α ⊕ Fin n)) :
      IsDeltaZero (.rel r ts)
  | imp {n} {φ ψ : (language k I).BoundedFormula α n} :
      IsDeltaZero φ → IsDeltaZero ψ → IsDeltaZero (.imp φ ψ)
  | boundedAll {n} (t : (language k I).Term (α ⊕ Fin n))
      {φ : (language k I).BoundedFormula α (n + 1)} :
      IsDeltaZero φ → IsDeltaZero (OneYTruth.boundedAll t φ)

/-- A finite existential prefix followed by an expanded-language Δ₀ matrix. -/
inductive IsSigmaOne {k : Nat} {I : Type u} {α : Type v} :
    {n : Nat} → (language k I).BoundedFormula α n → Prop
  | deltaZero {n} {φ : (language k I).BoundedFormula α n} :
      IsDeltaZero φ → IsSigmaOne φ
  | ex {n} {φ : (language k I).BoundedFormula α (n + 1)} :
      IsSigmaOne φ → IsSigmaOne φ.ex

theorem diagonalTranslate_boundedAll {k K : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} (h : k < K)
    (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) :
    diagonalTranslate (J := J) h (boundedAll t φ) =
      boundedAll (renameTerm (Sum.map Sum.inl id) t) (diagonalTranslate h φ) := by
  simp only [boundedAll, diagonalTranslate]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    cases t with
    | var a => cases a <;> rfl
    | func e => nomatch e

@[simp]
theorem diagonalTranslate_ex {k K : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} (h : k < K)
    (φ : (language k I).BoundedFormula α (n + 1)) :
    diagonalTranslate (J := J) h φ.ex = (diagonalTranslate h φ).ex := rfl

/-- The parameter translation preserves set-theoretic bounded complexity. -/
theorem IsDeltaZero.diagonalTranslate {k K : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsDeltaZero φ) (h : k < K) :
    IsDeltaZero (diagonalTranslate (J := J) h φ) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t s => exact .equal _ _
  | rel r ts => cases r <;> exact .rel _ _
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ
  | boundedAll t _ ih =>
    rw [diagonalTranslate_boundedAll]
    exact .boundedAll _ ih

/-- In particular, no unbounded quantifier is added to the Σ₁ reflection formula. -/
theorem IsSigmaOne.diagonalTranslate {k K : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsSigmaOne φ) (h : k < K) :
    IsSigmaOne (diagonalTranslate (J := J) h φ) := by
  induction hφ with
  | deltaZero hφ => exact .deltaZero (hφ.diagonalTranslate h)
  | ex _ ih => exact .ex ih

theorem namedMap_boundedAll {k : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} (f : I → J)
    (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) :
    (namedMap f).onBoundedFormula (boundedAll t φ) =
      boundedAll ((namedMap f).onTerm t) ((namedMap f).onBoundedFormula φ) := by
  simp only [boundedAll, LHom.onBoundedFormula]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    cases t with
    | var a => cases a <;> rfl
    | func e => nomatch e

/-- Extending the named language also preserves actual Δ₀ complexity. -/
theorem IsDeltaZero.namedMap {k : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsDeltaZero φ) (f : I → J) :
    IsDeltaZero ((OneYTruth.namedMap f).onBoundedFormula φ) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t s => exact .equal _ _
  | rel r ts => exact .rel _ _
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ
  | boundedAll t _ ih =>
    rw [namedMap_boundedAll]
    exact .boundedAll _ ih

theorem IsSigmaOne.namedMap {k : Nat} {I : Type u} {J : Type v}
    {α : Type*} {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsSigmaOne φ) (f : I → J) :
    IsSigmaOne ((OneYTruth.namedMap f).onBoundedFormula φ) := by
  induction hφ with
  | deltaZero hφ => exact .deltaZero (hφ.namedMap f)
  | ex _ ih => exact .ex ih

@[simp]
theorem elim_snoc_raise {A α : Type*} {n : Nat} (v : α → A)
    (xs : Fin n → A) (a : A) :
    Sum.elim v (Fin.snoc xs a) ∘ Sum.map id Fin.castSucc = Sum.elim v xs := by
  funext i
  cases i with
  | inl => rfl
  | inr => simp

/-- The new syntax really realizes `∀ a ∈ value(t), φ(a)`. -/
theorem realize_boundedAll {k : Nat} {I : Type u} {A : Type v}
    {α : Type*} {n : Nat} (M : Interpretation k I A)
    (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) (v : α → A) (xs : Fin n → A) :
    realize M (boundedAll t φ) v xs ↔
      ∀ a : A, M.mem a (@Term.realize _ A M.structure _ (Sum.elim v xs) t) →
        realize M φ v (Fin.snoc xs a) := by
  change (∀ a : A, M.mem ((Fin.snoc xs a : Fin (n + 1) → A) (Fin.last n))
    (@Term.realize _ A M.structure _ (Sum.elim v (Fin.snoc xs a))
      (renameTerm (Sum.map id Fin.castSucc) t)) → realize M φ v (Fin.snoc xs a)) ↔ _
  simp only [Fin.snoc_last, realize_renameTerm M M, elim_snoc_raise]

end OneYTruth
