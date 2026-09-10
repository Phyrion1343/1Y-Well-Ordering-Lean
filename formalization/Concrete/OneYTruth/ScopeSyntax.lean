import OneYTruth.ScopedConnectives
import OneYTruth.Complexity
import Mathlib.Tactic.FinCases

/-! A direct capture-avoiding map of finite scopes, with syntactic bounded
complexity preserved. This supports prenex assembly of genuine certificates. -/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

def extendScope {n m : Nat} (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.lastCases (Fin.last m) (fun i => (ρ i).castSucc)

@[simp] theorem extendScope_last {n m : Nat} (ρ : Fin n → Fin m) :
    extendScope ρ (Fin.last n) = Fin.last m := by simp [extendScope]

@[simp] theorem extendScope_castSucc {n m : Nat} (ρ : Fin n → Fin m) (i : Fin n) :
    extendScope ρ i.castSucc = (ρ i).castSucc := by simp [extendScope]

def renameScopeTerm {k : Nat} {I : Type u} {n m : Nat} (ρ : Fin n → Fin m)
    (t : (language k I).Term (Empty ⊕ Fin n)) : (language k I).Term (Empty ⊕ Fin m) :=
  renameTerm (K := k) (J := I) (Sum.map id ρ) t

def renameScope {k : Nat} {I : Type u} : {n m : Nat} → (Fin n → Fin m) →
    (language k I).BoundedFormula Empty n → (language k I).BoundedFormula Empty m
  | _, _, _, .falsum => .falsum
  | _, _, ρ, .equal t s => .equal (renameScopeTerm ρ t) (renameScopeTerm ρ s)
  | _, _, ρ, .rel r ts => .rel r (fun i => renameScopeTerm ρ (ts i))
  | _, _, ρ, .imp φ ψ => .imp (renameScope ρ φ) (renameScope ρ ψ)
  | _, _, ρ, .all φ => .all (renameScope (extendScope ρ) φ)

theorem realize_renameScopeTerm {k : Nat} {I : Type u} {A : Type v} {n m : Nat}
    (M : Interpretation k I A) (ρ : Fin n → Fin m)
    (t : (language k I).Term (Empty ⊕ Fin n)) (xs : Fin m → A) :
    @Term.realize _ A M.structure _ (Sum.elim Empty.elim xs) (renameScopeTerm ρ t) =
      @Term.realize _ A M.structure _ (Sum.elim Empty.elim (xs ∘ ρ)) t := by
  cases t with
  | func e => nomatch e
  | var i => cases i with
    | inl e => exact e.elim
    | inr i => rfl

theorem snoc_comp_extendScope {A : Type v} {n m : Nat} (ρ : Fin n → Fin m)
    (xs : Fin m → A) (a : A) :
    Fin.snoc xs a ∘ extendScope ρ = Fin.snoc (xs ∘ ρ) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem realize_renameScope {k : Nat} {I : Type u} {A : Type v} {n m : Nat}
    (M : Interpretation k I A) (ρ : Fin n → Fin m)
    (φ : (language k I).BoundedFormula Empty n) (xs : Fin m → A) :
    realize M (renameScope ρ φ) Empty.elim xs ↔ realize M φ Empty.elim (xs ∘ ρ) := by
  letI := M.structure
  induction φ generalizing m with
  | falsum => exact Iff.rfl
  | equal t s =>
      change (_ = _) ↔ (_ = _)
      rw [realize_renameScopeTerm, realize_renameScopeTerm]
  | rel r ts =>
      change M.structure.RelMap r (fun i => Term.realize (Sum.elim Empty.elim xs) (renameScopeTerm ρ (ts i))) ↔ _
      simp only [realize_renameScopeTerm]
      rfl
  | imp φ ψ ihφ ihψ =>
      change (realize M (renameScope ρ φ) Empty.elim xs → realize M (renameScope ρ ψ) Empty.elim xs) ↔ _
      exact imp_congr (ihφ ρ xs) (ihψ ρ xs)
  | all φ ih =>
      change (∀ a : A, realize M (renameScope (extendScope ρ) φ) Empty.elim (Fin.snoc xs a)) ↔ _
      simp only [ih, snoc_comp_extendScope]
      rfl

theorem renameScope_boundedAll {k : Nat} {I : Type u} {n m : Nat}
    (ρ : Fin n → Fin m) (t : (language k I).Term (Empty ⊕ Fin n))
    (φ : (language k I).BoundedFormula Empty (n+1)) :
    renameScope ρ (boundedAll t φ) =
      boundedAll (renameScopeTerm ρ t) (renameScope (extendScope ρ) φ) := by
  simp only [boundedAll, renameScope]
  congr 3
  congr 1
  funext i
  fin_cases i
  · simp [renameScopeTerm, renameTerm]
  · cases t with
    | func e => nomatch e
    | var j => cases j with
      | inl e => exact e.elim
      | inr j => simp [renameScopeTerm, renameTerm]

theorem IsDeltaZero.renameScope {k : Nat} {I : Type u} {n m : Nat}
    {φ : (language k I).BoundedFormula Empty n} (hφ : IsDeltaZero φ) (ρ : Fin n → Fin m) :
    IsDeltaZero (OneYTruth.renameScope ρ φ) := by
  induction hφ generalizing m with
  | falsum => exact .falsum
  | equal => exact .equal _ _
  | rel => exact .rel _ _
  | imp _ _ ihφ ihψ => exact .imp (ihφ ρ) (ihψ ρ)
  | boundedAll t _ ih =>
      rw [renameScope_boundedAll]
      exact .boundedAll _ (ih (extendScope ρ))

@[simp] theorem renameScope_ex {k : Nat} {I : Type u} {n m : Nat}
    (ρ : Fin n → Fin m) (φ : (language k I).BoundedFormula Empty (n+1)) :
    renameScope ρ φ.ex = (renameScope (extendScope ρ) φ).ex := rfl

theorem IsSigmaOne.renameScope {k : Nat} {I : Type u} {n m : Nat}
    {φ : (language k I).BoundedFormula Empty n} (hφ : IsSigmaOne φ) (ρ : Fin n → Fin m) :
    IsSigmaOne (OneYTruth.renameScope ρ φ) := by
  induction hφ generalizing m with
  | deltaZero h => exact .deltaZero (h.renameScope ρ)
  | ex _ ih =>
      rw [renameScope_ex]
      exact .ex (ih (extendScope ρ))

end OneYTruth
