import OneYTruth.Language

/-!
# Replacing separately named predicates by diagonal predicates

The translation sends `S_i(e,s)` to `U_k(c_i,e,s)`, where `c_i` is a
new free parameter. Existing lower diagonal predicates and membership are
preserved. It introduces no quantifiers and commutes with the connectives.

`diagonalReduct` defines the source interpretation from a target structure,
so the semantic theorem does not postulate truth or reflection principles.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w

/-- Relational languages have only variable terms. -/
def renameTerm {k K : Nat} {I : Type u} {J : Type v} {α β : Type*}
    (f : α → β) : (language k I).Term α → (language K J).Term β
  | .var a => .var (f a)
  | .func e _ => nomatch e

theorem realize_renameTerm {k K : Nat} {I : Type u} {J : Type v} {A : Type w}
    {α β : Type*} (M : Interpretation k I A) (N : Interpretation K J A)
    (f : α → β) (t : (language k I).Term α) (v : β → A) :
    @Term.realize (language K J) A N.structure β v (renameTerm f t) =
      @Term.realize (language k I) A M.structure α (v ∘ f) t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- Interpret the source named predicates by one specified lower diagonal. -/
def diagonalReduct {k K : Nat} {I : Type u} {J : Type v} {A : Type w}
    (h : k < K) (M : Interpretation K J A) (code : I → A) :
    Interpretation k I A where
  mem := M.mem
  diagonal j := M.diagonal (j.castLE h.le)
  named i := M.diagonal ⟨k, h⟩ (code i)

@[simp]
theorem elim_parameter_rename {I A α β : Type*} (v : α → A) (code : I → A)
    (xs : β → A) :
    Sum.elim (Sum.elim v code) xs ∘ Sum.map Sum.inl id = Sum.elim v xs := by
  funext a
  cases a <;> rfl

/-- Translate named truth to diagonal truth, adding its indices as free parameters. -/
def diagonalTranslate {k K : Nat} {I : Type u} {J : Type v} {α : Type*}
    (h : k < K) : {n : Nat} → (language k I).BoundedFormula α n →
      (language K J).BoundedFormula (α ⊕ I) n
  | _, .falsum => .falsum
  | _, .equal t s => .equal
      (renameTerm (Sum.map Sum.inl id) t) (renameTerm (Sum.map Sum.inl id) s)
  | _, .rel (.mem) ts => .rel .mem (fun i => renameTerm (Sum.map Sum.inl id) (ts i))
  | _, .rel (.diagonal j) ts => .rel (.diagonal (j.castLE h.le))
      (fun i => renameTerm (Sum.map Sum.inl id) (ts i))
  | _, .rel (.named i) ts => .rel (.diagonal ⟨k, h⟩)
      ![.var (.inl (.inr i)), renameTerm (Sum.map Sum.inl id) (ts 0),
        renameTerm (Sum.map Sum.inl id) (ts 1)]
  | _, .imp φ ψ => .imp (diagonalTranslate h φ) (diagonalTranslate h ψ)
  | _, .all φ => .all (diagonalTranslate h φ)

/-- Semantic correctness of the actual parameter translation. -/
theorem realize_diagonalTranslate {k K : Nat} {I : Type u} {J : Type v} {A : Type w}
    {α : Type*} {n : Nat} (h : k < K) (M : Interpretation K J A) (code : I → A)
    (φ : (language k I).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M (diagonalTranslate h φ) (Sum.elim v code) xs ↔
      realize (diagonalReduct h M code) φ v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [diagonalTranslate, realize, BoundedFormula.Realize]
    rw [realize_renameTerm (diagonalReduct h M code) M,
      realize_renameTerm (diagonalReduct h M code) M]
    rw [elim_parameter_rename]
  | rel r ts =>
    cases r with
    | mem =>
      dsimp [diagonalTranslate, realize, BoundedFormula.Realize]
      simp only [realize_renameTerm (diagonalReduct h M code) M, elim_parameter_rename]
      rfl
    | diagonal j =>
      dsimp [diagonalTranslate, realize, BoundedFormula.Realize]
      simp only [realize_renameTerm (diagonalReduct h M code) M, elim_parameter_rename]
      rfl
    | named i =>
      change M.diagonal ⟨k, h⟩ (code i)
        (@Term.realize (language K J) A M.structure _ (Sum.elim (Sum.elim v code) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 0)))
        (@Term.realize (language K J) A M.structure _ (Sum.elim (Sum.elim v code) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 1))) ↔
        M.diagonal ⟨k, h⟩ (code i)
          (@Term.realize (language k I) A (diagonalReduct h M code).structure _
            (Sum.elim v xs) (ts 0))
          (@Term.realize (language k I) A (diagonalReduct h M code).structure _
            (Sum.elim v xs) (ts 1))
      rw [realize_renameTerm (diagonalReduct h M code) M,
        realize_renameTerm (diagonalReduct h M code) M, elim_parameter_rename]
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih =>
    exact forall_congr' (fun a => ih (xs := Fin.snoc xs a))

end OneYTruth
