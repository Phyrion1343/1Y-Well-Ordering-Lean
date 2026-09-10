import OneYTruth.Complexity

/-! Capturing finitely many free parameters preserves the genuine Sigma-one fragment. -/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w

theorem relabel_raiseTerm {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n m : Nat} (g : α → β ⊕ Fin m) (t : (language k I).Term (α ⊕ Fin n)) :
    (renameTerm (K := k) (J := I) (Sum.map id Fin.castSucc) t).relabel
      (BoundedFormula.relabelAux g (n + 1)) =
      renameTerm (K := k) (J := I) (Sum.map id Fin.castSucc)
        (t.relabel (BoundedFormula.relabelAux g n)) := by
  cases t with
  | func e => nomatch e
  | var i =>
      cases i with
      | inl a =>
          cases hg : g a <;> simp [renameTerm, Term.relabel, BoundedFormula.relabelAux, hg] <;> rfl
      | inr i => simp [renameTerm, Term.relabel, BoundedFormula.relabelAux]

theorem relabel_boundedAll {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n m : Nat} (g : α → β ⊕ Fin m) (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) :
    (boundedAll t φ).relabel g =
      boundedAll (t.relabel (BoundedFormula.relabelAux g n)) (φ.relabel g) := by
  simp only [boundedAll, BoundedFormula.relabel_all, BoundedFormula.relabel_imp]
  congr 3
  change BoundedFormula.rel (L := language k I) .mem
    (fun i => Term.relabel (BoundedFormula.relabelAux g (n + 1))
      (![.var (.inr (Fin.last n)), renameTerm (Sum.map id Fin.castSucc) t] i)) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Term.relabel, BoundedFormula.relabelAux]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact relabel_raiseTerm g t

theorem IsDeltaZero.relabel {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n m : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsDeltaZero φ) (g : α → β ⊕ Fin m) : IsDeltaZero (φ.relabel g) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t s => exact .equal _ _
  | rel r ts => exact .rel _ _
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ
  | boundedAll t _ ih =>
      rw [relabel_boundedAll]
      exact .boundedAll _ ih

theorem IsSigmaOne.relabel {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n m : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsSigmaOne φ) (g : α → β ⊕ Fin m) : IsSigmaOne (φ.relabel g) := by
  induction hφ with
  | deltaZero hφ => exact .deltaZero (hφ.relabel g)
  | ex _ ih =>
      rw [BoundedFormula.relabel_ex]
      exact .ex ih

theorem relabelEquiv_boundedAll {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n : Nat} (g : α ≃ β) (t : (language k I).Term (α ⊕ Fin n))
    (φ : (language k I).BoundedFormula α (n + 1)) :
    BoundedFormula.relabelEquiv g (boundedAll t φ) =
      boundedAll (t.relabel (Sum.map g id)) (BoundedFormula.relabelEquiv g φ) := by
  simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv_apply,
    boundedAll, BoundedFormula.mapTermRel, Term.relabelEquiv_apply]
  congr 3
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    cases t with
    | func e => nomatch e
    | var a => cases a <;> rfl

theorem IsDeltaZero.relabelEquiv {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsDeltaZero φ) (g : α ≃ β) : IsDeltaZero (BoundedFormula.relabelEquiv g φ) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t s => exact .equal _ _
  | rel r ts => exact .rel _ _
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ
  | boundedAll t _ ih =>
      rw [relabelEquiv_boundedAll]
      exact .boundedAll _ ih

theorem IsSigmaOne.relabelEquiv {k : Nat} {I : Type u} {α : Type v} {β : Type w}
    {n : Nat} {φ : (language k I).BoundedFormula α n}
    (hφ : IsSigmaOne φ) (g : α ≃ β) : IsSigmaOne (BoundedFormula.relabelEquiv g φ) := by
  induction hφ with
  | deltaZero hφ => exact .deltaZero (hφ.relabelEquiv g)
  | ex _ ih => exact .ex ih

end OneYTruth
