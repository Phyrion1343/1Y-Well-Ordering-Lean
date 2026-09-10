import OneYTruth.Translation

/-!
# Finite support of the named truth predicates

This is a support theorem for genuine finite first-order formulas, not an
assumption that the entire stage language belongs to a smaller model.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w

variable {k : Nat} {I : Type u} [DecidableEq I]

/-- The separately named index, if a relation has one. -/
def relationSupport : {n : Nat} → Relation k I n → Finset I
  | _, .mem => ∅
  | _, .diagonal _ => ∅
  | _, .named i => {i}

/-- All named predicate indices actually occurring in a formula. -/
def namedSupport {α : Type v} : {n : Nat} →
    (language k I).BoundedFormula α n → Finset I
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel r _ => relationSupport r
  | _, .imp φ ψ => namedSupport φ ∪ namedSupport ψ
  | _, .all φ => namedSupport φ

omit [DecidableEq I] in
/-- In a relational language a term's value is independent of predicates. -/
theorem term_realize_irrel {A : Type w} {α : Type v}
    (M N : Interpretation k I A) (t : (language k I).Term α) (v : α → A) :
    @Term.realize (language k I) A M.structure α v t =
      @Term.realize (language k I) A N.structure α v t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- Only the finitely many named predicates in `namedSupport` affect truth. -/
theorem realize_eq_of_namedSupport {A : Type w} {α : Type v} {n : Nat}
    (M N : Interpretation k I A) (φ : (language k I).BoundedFormula α n)
    (hmem : M.mem = N.mem) (hdiag : M.diagonal = N.diagonal)
    (hs : ∀ i ∈ namedSupport φ, M.named i = N.named i)
    (v : α → A) (xs : Fin n → A) :
    realize M φ v xs ↔ realize N φ v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [realize, BoundedFormula.Realize]
    rw [term_realize_irrel M N t, term_realize_irrel M N s]
  | rel r ts =>
    cases r with
    | mem =>
      change M.mem
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1)) ↔
        N.mem (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
      rw [hmem, term_realize_irrel M N, term_realize_irrel M N]
    | diagonal j =>
      change M.diagonal j
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 2)) ↔
        N.diagonal j (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 2))
      rw [hdiag, term_realize_irrel M N, term_realize_irrel M N,
        term_realize_irrel M N]
    | named i =>
      have hi := hs i (by simp [namedSupport, relationSupport])
      change M.named i
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 0))
        (@Term.realize _ A M.structure _ (Sum.elim v xs) (ts 1)) ↔
        N.named i (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 0))
          (@Term.realize _ A N.structure _ (Sum.elim v xs) (ts 1))
      rw [hi, term_realize_irrel M N, term_realize_irrel M N]
  | imp φ ψ ihφ ihψ =>
    apply imp_congr
    · exact ihφ (fun i hi => hs i (Finset.mem_union_left _ hi)) xs
    · exact ihψ (fun i hi => hs i (Finset.mem_union_right _ hi)) xs
  | all φ ih =>
    exact forall_congr' (fun a => ih hs (xs := Fin.snoc xs a))

/-- The introduced parameter family is used only at the finite named support. -/
theorem realize_diagonalTranslate_eqOn {K : Nat} {J : Type v} {A : Type w}
    {α : Type*} {n : Nat} (h : k < K) (M : Interpretation K J A)
    (code₁ code₂ : I → A) (φ : (language k I).BoundedFormula α n)
    (hs : ∀ i ∈ namedSupport φ, code₁ i = code₂ i)
    (v : α → A) (xs : Fin n → A) :
    realize M (diagonalTranslate h φ) (Sum.elim v code₁) xs ↔
      realize M (diagonalTranslate h φ) (Sum.elim v code₂) xs := by
  rw [realize_diagonalTranslate, realize_diagonalTranslate]
  refine realize_eq_of_namedSupport (diagonalReduct h M code₁)
    (diagonalReduct h M code₂) φ rfl rfl ?_ v xs
  intro i hi
  simp only [diagonalReduct, hs i hi]

/-- Re-express a formula in any finite named sublanguage containing its support. -/
def restrictFormula {α : Type v} (S : Finset I) : {n : Nat} →
    (φ : (language k I).BoundedFormula α n) → namedSupport φ ⊆ S →
      (language k {i // i ∈ S}).BoundedFormula α n
  | _, .falsum, _ => .falsum
  | _, .equal t s, _ => .equal (renameTerm id t) (renameTerm id s)
  | _, .rel (.mem) ts, _ => .rel .mem (fun i => renameTerm id (ts i))
  | _, .rel (.diagonal j) ts, _ => .rel (.diagonal j) (fun i => renameTerm id (ts i))
  | _, .rel (.named i) ts, hs => .rel (.named ⟨i, hs (by simp [namedSupport, relationSupport])⟩)
      (fun i => renameTerm id (ts i))
  | _, .imp φ ψ, hs => .imp
      (restrictFormula S φ (fun _ hi => hs (Finset.mem_union_left _ hi)))
      (restrictFormula S ψ (fun _ hi => hs (Finset.mem_union_right _ hi)))
  | _, .all φ, hs => .all (restrictFormula S φ hs)

omit [DecidableEq I] in
theorem namedMap_renameTerm {J : Type v} {α : Type w} (f : J → I)
    (t : (language k I).Term α) :
    (namedMap f).onTerm (renameTerm (k := k) (I := I) (K := k) (J := J) id t) = t := by
  cases t with
  | var => rfl
  | func e => nomatch e

/-- The finite-language formula maps back to the original formula exactly. -/
theorem namedMap_restrictFormula {α : Type v} {n : Nat} (S : Finset I)
    (φ : (language k I).BoundedFormula α n) (hs : namedSupport φ ⊆ S) :
    (namedMap (Subtype.val : {i // i ∈ S} → I)).onBoundedFormula
      (restrictFormula S φ hs) = φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [restrictFormula, LHom.onBoundedFormula, namedMap_renameTerm, Term.bdEqual]
  | rel r ts =>
    cases r <;>
      simp only [restrictFormula, LHom.onBoundedFormula,
        Relations.boundedFormula, Function.comp_def, namedMap_renameTerm] <;> rfl
  | imp φ ψ ihφ ihψ =>
    simp only [restrictFormula, LHom.onBoundedFormula, ihφ, ihψ]
  | all φ ih =>
    exact congrArg BoundedFormula.all (ih hs)

/-- Every formula factors through an explicitly finite set of named symbols. -/
theorem exists_finite_named_fragment {α : Type v} {n : Nat}
    (φ : (language k I).BoundedFormula α n) :
    ∃ (S : Finset I) (ψ : (language k {i // i ∈ S}).BoundedFormula α n),
      (namedMap (Subtype.val : {i // i ∈ S} → I)).onBoundedFormula ψ = φ :=
  ⟨namedSupport φ, restrictFormula (namedSupport φ) φ (fun _ h => h),
    namedMap_restrictFormula _ _ _⟩

end OneYTruth
