import OneYTruth.FiniteSupport

/-!
# The fixed finite auxiliary language

The initial hull construction uses membership and ONE four-argument
predicate `W(k,ξ,e,s)`. This language is deliberately separate from every
control language. The finite formula translation is proved here; neither
the existence of the intended `W` nor a Skolem club is asserted.
-/

namespace OneYTruth.Auxiliary

open FirstOrder FirstOrder.Language

universe u v w

inductive Relation : Nat → Type
  | mem : Relation 2
  | truth : Relation 4

/-- Exactly two relation symbols; there are no hidden families of symbols. -/
abbrev language : FirstOrder.Language where
  Functions _ := Empty
  Relations := Relation

structure Interpretation (A : Type u) where
  mem : A → A → Prop
  truth : A → A → A → A → Prop

@[instance_reducible]
def Interpretation.structure {A : Type u} (M : Interpretation A) : language.Structure A where
  funMap := fun {_} e => nomatch e
  RelMap := fun {_} r xs => match r with
    | .mem => M.mem (xs 0) (xs 1)
    | .truth => M.truth (xs 0) (xs 1) (xs 2) (xs 3)

def realize {A : Type u} {α : Type v} {n : Nat} (M : Interpretation A)
    (φ : language.BoundedFormula α n) (v : α → A) (xs : Fin n → A) : Prop :=
  @BoundedFormula.Realize language A M.structure α n φ v xs

def renameTerm {k : Nat} {I : Type u} {α β : Type*} (f : α → β) :
    (OneYTruth.language k I).Term α → language.Term β
  | .var a => .var (f a)
  | .func e _ => nomatch e

theorem realize_renameTerm {k : Nat} {I : Type u} {A : Type v} {α β : Type*}
    (M : OneYTruth.Interpretation k I A) (N : Interpretation A)
    (f : α → β) (t : (OneYTruth.language k I).Term α) (v : β → A) :
    @Term.realize language A N.structure β v (renameTerm f t) =
      @Term.realize (OneYTruth.language k I) A M.structure α (v ∘ f) t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- Read all lower diagonals and current named predicates from W. -/
def reduct {k : Nat} {I : Type u} {A : Type v} (M : Interpretation A)
    (block : Fin (k + 1) → A) (index : I → A) : OneYTruth.Interpretation k I A where
  mem := M.mem
  diagonal j := M.truth (block j.castSucc)
  named i := M.truth (block (Fin.last k)) (index i)

/-- Block parameters are finite, and named parameters will be restricted to finite support. -/
def translate {k : Nat} {I : Type u} {α : Type v} : {n : Nat} →
    (OneYTruth.language k I).BoundedFormula α n →
      language.BoundedFormula (α ⊕ (Fin (k + 1) ⊕ I)) n
  | _, .falsum => .falsum
  | _, .equal t s => .equal
      (renameTerm (Sum.map Sum.inl id) t) (renameTerm (Sum.map Sum.inl id) s)
  | _, .rel (.mem) ts => .rel .mem (fun i => renameTerm (Sum.map Sum.inl id) (ts i))
  | _, .rel (.diagonal j) ts => .rel .truth
      ![.var (.inl (.inr (.inl j.castSucc))), renameTerm (Sum.map Sum.inl id) (ts 0),
        renameTerm (Sum.map Sum.inl id) (ts 1), renameTerm (Sum.map Sum.inl id) (ts 2)]
  | _, .rel (.named i) ts => .rel .truth
      ![.var (.inl (.inr (.inl (Fin.last k)))), .var (.inl (.inr (.inr i))),
        renameTerm (Sum.map Sum.inl id) (ts 0), renameTerm (Sum.map Sum.inl id) (ts 1)]
  | _, .imp φ ψ => .imp (translate φ) (translate ψ)
  | _, .all φ => .all (translate φ)

/-- Correctness of translating any finite local formula to the one-W language. -/
theorem realize_translate {k : Nat} {I : Type u} {A : Type v} {α : Type w} {n : Nat}
    (M : Interpretation A) (block : Fin (k + 1) → A) (index : I → A)
    (φ : (OneYTruth.language k I).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M (translate φ) (Sum.elim v (Sum.elim block index)) xs ↔
      OneYTruth.realize (reduct M block index) φ v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [translate, realize, OneYTruth.realize, BoundedFormula.Realize]
    rw [realize_renameTerm (reduct M block index) M,
      realize_renameTerm (reduct M block index) M, elim_parameter_rename]
  | rel r ts =>
    cases r with
    | mem =>
      dsimp [translate, realize, OneYTruth.realize, BoundedFormula.Realize]
      simp only [realize_renameTerm (reduct M block index) M, elim_parameter_rename]
      rfl
    | diagonal j =>
      change M.truth (block j.castSucc)
        (@Term.realize language A M.structure _ (Sum.elim (Sum.elim v (Sum.elim block index)) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 0)))
        (@Term.realize language A M.structure _ (Sum.elim (Sum.elim v (Sum.elim block index)) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 1)))
        (@Term.realize language A M.structure _ (Sum.elim (Sum.elim v (Sum.elim block index)) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 2))) ↔
        M.truth (block j.castSucc)
          (@Term.realize _ A (reduct M block index).structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A (reduct M block index).structure _ (Sum.elim v xs) (ts 1))
          (@Term.realize _ A (reduct M block index).structure _ (Sum.elim v xs) (ts 2))
      simp only [realize_renameTerm (reduct M block index) M, elim_parameter_rename]
    | named i =>
      change M.truth (block (Fin.last k)) (index i)
        (@Term.realize language A M.structure _ (Sum.elim (Sum.elim v (Sum.elim block index)) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 0)))
        (@Term.realize language A M.structure _ (Sum.elim (Sum.elim v (Sum.elim block index)) xs)
          (renameTerm (Sum.map Sum.inl id) (ts 1))) ↔
        M.truth (block (Fin.last k)) (index i)
          (@Term.realize _ A (reduct M block index).structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A (reduct M block index).structure _ (Sum.elim v xs) (ts 1))
      simp only [realize_renameTerm (reduct M block index) M, elim_parameter_rename]
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih => exact forall_congr' (fun a => ih (xs := Fin.snoc xs a))

/-- The auxiliary translation with exactly a finite type of additional named parameters. -/
def finiteTranslate {k : Nat} {I : Type u} [DecidableEq I] {α : Type v} {n : Nat}
    (φ : (OneYTruth.language k I).BoundedFormula α n) :
    language.BoundedFormula (α ⊕ (Fin (k + 1) ⊕ {i // i ∈ namedSupport φ})) n :=
  translate (restrictFormula (namedSupport φ) φ (fun _ h => h))

/-- The finite-parameter version has the same truth value as the original local formula. -/
theorem realize_finiteTranslate {k : Nat} {I : Type u} [DecidableEq I]
    {A : Type v} {α : Type w} {n : Nat}
    (M : Interpretation A) (block : Fin (k + 1) → A) (index : I → A)
    (φ : (OneYTruth.language k I).BoundedFormula α n) (v : α → A) (xs : Fin n → A) :
    realize M (finiteTranslate φ)
      (Sum.elim v (Sum.elim block (fun i : {i // i ∈ namedSupport φ} => index i.val))) xs ↔
      OneYTruth.realize (reduct M block index) φ v xs := by
  rw [finiteTranslate, realize_translate]
  have heq := OneYTruth.realize_namedMap (reduct M block index)
    (Subtype.val : {i // i ∈ namedSupport φ} → I)
    (restrictFormula (namedSupport φ) φ (fun _ h => h)) v xs
  rw [namedMap_restrictFormula] at heq
  exact heq.symm

end OneYTruth.Auxiliary
