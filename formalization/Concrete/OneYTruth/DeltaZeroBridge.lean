import OneYTruth.Complexity
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0

/-!
# Importing actual bounded set-theoretic formulas

This compiler brings the constructible library's intrinsically bounded
set-theoretic syntax into the mixed language. It preserves both its actual
semantics and the separately defined `IsDeltaZero` complexity. Thus existing
and future coded-set formulas can be used without simply postulating that
their English descriptions are bounded.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language Constructible

universe u v

/-- Translate the existing pure bounded syntax, with no extra predicates. -/
def ofConstructibleDeltaZero (k : Nat) (I : Type u) : {n : Nat} →
    Constructible.Delta0Formula n → (language k I).BoundedFormula Empty n
  | _, .mem i j => .rel .mem ![.var (.inr i), .var (.inr j)]
  | _, .eq i j => .equal (.var (.inr i)) (.var (.inr j))
  | _, .neg φ => (ofConstructibleDeltaZero k I φ).not
  | _, .conj φ ψ => ofConstructibleDeltaZero k I φ ⊓ ofConstructibleDeltaZero k I ψ
  | _, .boundedEx i φ =>
    (OneYTruth.boundedAll (.var (.inr i)) (ofConstructibleDeltaZero k I φ).not).not

theorem ofConstructibleDeltaZero_isDeltaZero (k : Nat) (I : Type u) {n : Nat}
    (φ : Constructible.Delta0Formula n) : IsDeltaZero (ofConstructibleDeltaZero k I φ) := by
  induction φ with
  | mem i j => exact .rel _ _
  | eq i j => exact .equal _ _
  | neg φ ih => exact .imp ih .falsum
  | conj φ ψ ihφ ihψ => exact .imp (.imp ihφ (.imp ihψ .falsum)) .falsum
  | boundedEx i φ ih => exact .imp (.boundedAll _ (.imp ih .falsum)) .falsum

theorem constructible_snoc_eq {A : Type v} {n : Nat} (s : Fin n → A) (a : A) :
    Constructible.snoc s a = Fin.snoc s a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Constructible.snoc_last, Fin.snoc_last]
  · simp only [Constructible.snoc_castSucc, Fin.snoc_castSucc]

/-- The compiler agrees with the library semantics over any membership interpretation. -/
theorem realize_ofConstructibleDeltaZero {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) {n : Nat} (φ : Constructible.Delta0Formula n)
    (xs : Fin n → A) :
    OneYTruth.realize M (ofConstructibleDeltaZero k I φ) Empty.elim xs ↔
      Constructible.Delta0Formula.Satisfies M.mem φ xs := by
  classical
  induction φ with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => exact not_congr (ih xs)
  | conj φ ψ ihφ ihψ =>
    change (¬ (OneYTruth.realize M (ofConstructibleDeltaZero k I φ) Empty.elim xs →
      ¬ OneYTruth.realize M (ofConstructibleDeltaZero k I ψ) Empty.elim xs)) ↔ _
    rw [ihφ, ihψ]
    simp only [Classical.not_imp, not_not, Constructible.Delta0Formula.Satisfies]
  | boundedEx i φ ih =>
    change (¬ OneYTruth.realize M
      (OneYTruth.boundedAll (.var (.inr i)) (ofConstructibleDeltaZero k I φ).not)
      Empty.elim xs) ↔ _
    rw [realize_boundedAll]
    change (¬ ∀ a : A, M.mem a (xs i) →
      ¬ OneYTruth.realize M (ofConstructibleDeltaZero k I φ) Empty.elim (Fin.snoc xs a)) ↔ _
    simp only [ih, not_forall, not_not, exists_prop,
      Constructible.Delta0Formula.Satisfies, constructible_snoc_eq]

/-- Pure bounded formulas retain the existing transitive-set absoluteness theorem. -/
theorem realize_ofConstructibleDeltaZero_absolute {k : Nat} {I : Type u}
    {U : ZFSet.{v}} (hU : U.IsTransitive) (M : Interpretation k I (ZFCarrier U))
    (hmem : M.mem = Constructible.zfCarrierMem U) {n : Nat}
    (φ : Constructible.Delta0Formula n) (xs : Fin n → ZFCarrier U) :
    OneYTruth.realize M (ofConstructibleDeltaZero k I φ) Empty.elim xs ↔
      Constructible.Delta0Formula.Satisfies (fun x y : ZFSet.{v} => x ∈ y) φ
        (Constructible.Delta0Formula.val xs) := by
  rw [realize_ofConstructibleDeltaZero, hmem]
  exact Constructible.Delta0Formula.satisfies_absolute hU φ xs

end OneYTruth
