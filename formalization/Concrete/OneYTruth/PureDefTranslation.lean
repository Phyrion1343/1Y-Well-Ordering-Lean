import OneYTruth.PureFOSchemas
import OneYTruth.ScopedConnectives

/-! Both directions between the actual zero-block empty-name language and
the constructible library's pure FO syntax. This identifies the real Def operator. -/

namespace OneYTruth.PureDefTranslation

open Constructible FirstOrder FirstOrder.Language

universe u

def termIndex {n : Nat} : (language 0 Empty).Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => nomatch e
  | .var (.inr i) => i
  | .func e _ => nomatch e

def toFO : {n : Nat} → (language 0 Empty).BoundedFormula Empty n → FOFormula n
  | n, .falsum => .ex (.neg (.eq (Fin.last n) (Fin.last n)))
  | _, .equal t s => .eq (termIndex t) (termIndex s)
  | _, .rel .mem ts => .mem (termIndex (ts 0)) (termIndex (ts 1))
  | _, .rel (.diagonal j) _ => nomatch j
  | _, .rel (.named i) _ => nomatch i
  | _, .imp φ ψ => .imp (toFO φ) (toFO ψ)
  | _, .all φ => .all (toFO φ)

theorem realize_termIndex {A : Type u} {n : Nat} (N : Interpretation 0 Empty A)
    (t : (language 0 Empty).Term (Empty ⊕ Fin n)) (xs : Fin n → A) :
    @Term.realize _ A N.structure _ (Sum.elim Empty.elim xs) t = xs (termIndex t) := by
  cases t with
  | func e => nomatch e
  | var i => cases i with
    | inl e => exact e.elim
    | inr => rfl

theorem satisfies_toFO {A : Type u} {n : Nat} (N : Interpretation 0 Empty A)
    (φ : (language 0 Empty).BoundedFormula Empty n) (xs : Fin n → A) :
    FOFormula.Satisfies N.mem (toFO φ) xs ↔ realize N φ Empty.elim xs := by
  induction φ with
  | falsum => simp [toFO, FOFormula.Satisfies, realize, BoundedFormula.Realize]
  | equal t s =>
      change (xs (termIndex t) = xs (termIndex s)) ↔ _
      rw [← realize_termIndex N t xs, ← realize_termIndex N s xs]
      rfl
  | rel r ts =>
      cases r with
      | mem =>
          change N.mem (xs (termIndex (ts 0))) (xs (termIndex (ts 1))) ↔ _
          rw [← realize_termIndex N (ts 0) xs, ← realize_termIndex N (ts 1) xs]
          rfl
      | diagonal j => nomatch j
      | named i => nomatch i
  | imp φ ψ ihφ ihψ =>
      rw [toFO, FOFormula.satisfies_imp]
      exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih =>
      rw [toFO, FOFormula.satisfies_all]
      change (∀ a : A, FOFormula.Satisfies N.mem (toFO φ) (snoc xs a)) ↔ _
      simp only [ih, constructible_snoc_eq]
      rfl

theorem mem_DefZF_iff_mixed {U z : ZFSet.{u}}
    (N : Interpretation 0 Empty (ZFCarrier U)) (hmem : N.mem = zfCarrierMem U) :
    z ∈ DefZF U ↔ z ⊆ U ∧
      ∃ n : Nat, ∃ s : Fin n → ZFCarrier U,
        ∃ φ : (language 0 Empty).BoundedFormula Empty (n+1),
          ∀ x : ZFCarrier U, x.val ∈ z ↔ realize N φ Empty.elim (Fin.snoc s x) := by
  rw [mem_DefZF_iff_exists_satisfies]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨n, s, φ, hφ⟩
    refine ⟨n, s, ofConstructibleFO 0 Empty φ, ?_⟩
    intro x
    rw [realize_ofConstructibleFO, hmem, ← constructible_snoc_eq]
    exact hφ x
  · rintro ⟨n, s, φ, hφ⟩
    refine ⟨n, s, toFO φ, ?_⟩
    intro x
    rw [← hmem, satisfies_toFO, constructible_snoc_eq]
    exact hφ x

end OneYTruth.PureDefTranslation
