import OneYTruth.SatisfactionSet

/-!
# Correctness and uniqueness of a Tarski recursion certificate

Candidates are actual sets of coded formula/assignment pairs. A proved
small set of all well-scoped pairs rules out junk. The remaining clauses
are the precise recursion on falsum, equality, relations, implication,
and universal quantification.

This file proves the mathematical certificate correct and constructs its
canonical witness. It does NOT yet compile the certificate into an
internal bounded set-theoretic formula: the clauses still quantify over
Lean syntax and use the given external interpretation at atomic formulas.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language Constructible FormulaCode

universe u v

abbrev ScopedAssignment {k : Nat} (I : Type v) (U : ZFSet.{u}) :=
  Σ φ : Packed k I, Fin φ.1 → ZFCarrier U

/-- The genuine set of well-scoped formula/assignment pairs. -/
noncomputable def scopedPairs {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : ScopedAssignment (k := k) I U =>
    ZFSet.pair (packedCode indexCode w.1) (assignmentCode w.2))

/-- A candidate's claim about a particular scoped formula and assignment. -/
noncomputable def CodedHolds {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (S : ZFSet.{u}) {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U) : Prop :=
  ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode v) ∈ S

/-- Semantic recursion clauses, stated about actual candidate sets. -/
structure IsTarskiSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u}) : Prop where
  noJunk : S ⊆ scopedPairs (k := k) U indexCode
  falsum : ∀ {n : Nat} (v : Fin n → ZFCarrier U),
    ¬ CodedHolds indexCode S (.falsum : (language k I).BoundedFormula Empty n) v
  equal : ∀ {n : Nat} (t s : (language k I).Term (Empty ⊕ Fin n))
    (v : Fin n → ZFCarrier U),
    CodedHolds indexCode S (.equal t s) v ↔ OneYTruth.realize M (.equal t s) Empty.elim v
  rel : ∀ {n m : Nat} (r : Relation k I m)
    (ts : Fin m → (language k I).Term (Empty ⊕ Fin n)) (v : Fin n → ZFCarrier U),
    CodedHolds indexCode S (.rel r ts) v ↔ OneYTruth.realize M (.rel r ts) Empty.elim v
  imp : ∀ {n : Nat} (φ ψ : (language k I).BoundedFormula Empty n)
    (v : Fin n → ZFCarrier U),
    CodedHolds indexCode S (.imp φ ψ) v ↔
      (CodedHolds indexCode S φ v → CodedHolds indexCode S ψ v)
  all : ∀ {n : Nat} (φ : (language k I).BoundedFormula Empty (n + 1))
    (v : Fin n → ZFCarrier U),
    CodedHolds indexCode S (.all φ) v ↔
      ∀ a : ZFCarrier U, CodedHolds indexCode S φ (Fin.snoc v a)

/-- Every recursion certificate computes the actual semantics, by syntax induction. -/
theorem IsTarskiSet.correct {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} {M : Interpretation k I (ZFCarrier U)} {S : ZFSet.{u}}
    (h : IsTarskiSet indexCode M S) {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U) :
    CodedHolds indexCode S φ v ↔ OneYTruth.realize M φ Empty.elim v := by
  induction φ with
  | falsum => exact iff_false_intro (h.falsum v)
  | equal t s => exact h.equal t s v
  | rel r ts => exact h.rel r ts v
  | imp φ ψ ihφ ihψ =>
    rw [h.imp]
    exact imp_congr (ihφ v) (ihψ v)
  | all φ ih =>
    rw [h.all]
    exact forall_congr' (fun a => ih (Fin.snoc v a))

/-- The previously constructed satisfaction set supplies all certificate clauses. -/
theorem satisfactionSet_isTarskiSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) :
    IsTarskiSet indexCode M (satisfactionSet indexCode M) := by
  have hc {n : Nat} (φ : (language k I).BoundedFormula Empty n)
      (v : Fin n → ZFCarrier U) :
      CodedHolds indexCode (satisfactionSet indexCode M) φ v ↔
        OneYTruth.realize M φ Empty.elim v := mem_satisfactionSet_iff hi M φ v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨⟨φ, ⟨v, hv⟩⟩, h⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_range.mpr ⟨⟨φ, v⟩, h⟩
  · intro n v
    rw [hc]
    exact not_false
  · intro n t s v
    exact hc (.equal t s) v
  · intro n m r ts v
    exact hc (.rel r ts) v
  · intro n φ ψ v
    rw [hc, hc, hc]
    rfl
  · intro n φ v
    simp only [hc]
    rfl

/-- No junk plus the recursive semantics uniquely determines the entire set. -/
theorem IsTarskiSet.eq_satisfactionSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    {M : Interpretation k I (ZFCarrier U)} {S : ZFSet.{u}}
    (h : IsTarskiSet indexCode M S) : S = satisfactionSet indexCode M := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨⟨φ, v⟩, heq⟩ := ZFSet.mem_range.mp (h.noJunk hz)
    subst z
    exact (mem_satisfactionSet_iff hi M φ.2 v).mpr ((h.correct φ.2 v).mp hz)
  · intro hz
    obtain ⟨⟨φ, ⟨v, hv⟩⟩, heq⟩ := ZFSet.mem_range.mp hz
    subst z
    exact (h.correct φ.2 v).mpr hv

/-- Existence and uniqueness have a concrete witness and require no truth-set axiom. -/
theorem existsUnique_tarskiSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) :
    ∃! S : ZFSet.{u}, IsTarskiSet indexCode M S :=
  ⟨satisfactionSet indexCode M, satisfactionSet_isTarskiSet hi M,
    fun _ h => h.eq_satisfactionSet hi⟩

end OneYTruth
