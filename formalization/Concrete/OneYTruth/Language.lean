import Mathlib.ModelTheory.Semantics

/-!
# The mixed language used by the 1-Y truth construction

`language k I` has membership, `k` ternary diagonal predicates, and one
separately named binary predicate for every `i : I`. In the ordinal-stage
application `I` will be `{ξ // ξ < η}`. There is deliberately no ternary
predicate that uniformly indexes the current-stage named predicates.

This file defines actual Mathlib first-order languages and reduct maps. It
does not assume or assert that any of their interpretations are truth towers.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w

/-- Arity distinguishes the diagonal predicates from separately named truth. -/
inductive Relation (k : Nat) (I : Type u) : Nat → Type u
  | mem : Relation k I 2
  | diagonal (j : Fin k) : Relation k I 3
  | named (i : I) : Relation k I 2

/-- Membership, lower diagonal truth predicates, and independent named predicates. -/
abbrev language (k : Nat) (I : Type u) : FirstOrder.Language where
  Functions _ := Empty
  Relations := Relation k I

instance (k : Nat) (I : Type u) : (language k I).IsRelational :=
  fun _ => by dsimp [language]; infer_instance

/-- Extend the available independently named predicates. No index is added as a term. -/
def namedMap {k : Nat} {I : Type u} {J : Type v} (f : I → J) :
    language k I →ᴸ language k J where
  onFunction := fun {_} e => nomatch e
  onRelation := fun {_} r => match r with
    | .mem => .mem
    | .diagonal j => .diagonal j
    | .named i => .named (f i)

/-- Interpretations remain ordinary predicate data, not unproved reflection axioms. -/
structure Interpretation (k : Nat) (I : Type u) (A : Type v) where
  mem : A → A → Prop
  diagonal : Fin k → A → A → A → Prop
  named : I → A → A → Prop

/-- The genuine first-order structure associated to an interpretation. -/
@[instance_reducible]
def Interpretation.structure {k : Nat} {I : Type u} {A : Type v}
    (M : Interpretation k I A) : (language k I).Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r xs => match r with
    | .mem => M.mem (xs 0) (xs 1)
    | .diagonal j => M.diagonal j (xs 0) (xs 1) (xs 2)
    | .named i => M.named i (xs 0) (xs 1)

/-- The reduct along a map of the named symbols. -/
def Interpretation.restrictNames {k : Nat} {I : Type u} {J : Type v} {A : Type w}
    (M : Interpretation k J A) (f : I → J) : Interpretation k I A where
  mem := M.mem
  diagonal := M.diagonal
  named i := M.named (f i)

theorem restrictNames_structure {k : Nat} {I : Type u} {J : Type v} {A : Type w}
    (M : Interpretation k J A) (f : I → J) :
    (M.restrictNames f).structure =
      @LHom.reduct (language k I) (language k J) (namedMap f) A M.structure := by
  apply FirstOrder.Language.Structure.ext
  · funext n e
    nomatch e
  · funext n r xs
    cases r <;> rfl

/-- Formula realization with the interpretation made explicit. -/
def realize {k : Nat} {I : Type u} {A : Type v} {α : Type w} {n : Nat}
    (M : Interpretation k I A) (φ : (language k I).BoundedFormula α n)
    (v : α → A) (xs : Fin n → A) : Prop :=
  @BoundedFormula.Realize (language k I) A M.structure α n φ v xs

/-- The actual syntactic map to a larger named language has exactly reduct semantics. -/
theorem realize_namedMap {k : Nat} {I : Type u} {J : Type v} {A : Type w}
    {α : Type*} {n : Nat} (M : Interpretation k J A) (f : I → J)
    (φ : (language k I).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M ((namedMap f).onBoundedFormula φ) v xs ↔
      realize (M.restrictNames f) φ v xs := by
  letI := M.structure
  letI := (namedMap (k := k) f).reduct A
  change ((namedMap f).onBoundedFormula φ).Realize v xs ↔
    @BoundedFormula.Realize (language k I) A (M.restrictNames f).structure α n φ v xs
  rw [restrictNames_structure]
  exact (namedMap f).realize_onBoundedFormula φ

end OneYTruth
