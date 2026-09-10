import OneYTruth.SmallSyntax

/-!
# The external full satisfaction relation is a genuine ZFSet

The set is constructed with `ZFSet.range` over a proved-small type of true
formula/assignment pairs. This is an external set-existence result. It does
NOT assert membership of this set in the model whose truth it represents,
or in a particular constructible level.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language Constructible Constructible.FiniteSequenceZF FormulaCode

universe u v

/-- Finite assignments are stored in reverse variable order. Extending the
scope by `Fin.snoc` therefore adds one pair at the front of the payload. -/
noncomputable def assignmentCode {U : ZFSet.{u}} {n : Nat} (v : Fin n → ZFCarrier U) :
    ZFSet.{u} := sequenceCode (List.ofFn (fun i => (v i).val)).reverse

theorem assignmentCode_injective {U : ZFSet.{u}} {n : Nat} :
    Function.Injective (assignmentCode : (Fin n → ZFCarrier U) → ZFSet.{u}) := by
  intro v w h
  have hvw := List.ofFn_injective (List.reverse_injective (sequenceCode_injective h))
  funext i
  exact Subtype.ext (congrFun hvw i)

/-- The assignment must actually satisfy the packed formula. -/
abbrev TrueAssignment {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) (φ : Packed k I) :=
  {v : Fin φ.1 → ZFCarrier U // OneYTruth.realize M φ.2 Empty.elim v}

/-- A small family of all true formula/assignment pairs. -/
abbrev SatisfactionWitness {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (M : Interpretation k I (ZFCarrier U)) := Σ φ : Packed k I, TrueAssignment M φ

/-- Actual external full satisfaction, including arbitrary finite arities. -/
noncomputable def satisfactionSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) : ZFSet.{u} :=
  ZFSet.range (fun w : SatisfactionWitness M =>
    ZFSet.pair (packedCode indexCode w.1) (assignmentCode w.2.val))

/-- Correctness on every actual formula code and assignment code. -/
theorem mem_satisfactionSet_iff {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U) :
    ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode v) ∈ satisfactionSet indexCode M ↔
      OneYTruth.realize M φ Empty.elim v := by
  constructor
  · intro h
    obtain ⟨⟨p, ⟨w, hw⟩⟩, heq⟩ := ZFSet.mem_range.mp h
    obtain ⟨hφ, hv⟩ := ZFSet.pair_inj.mp heq
    have hp : p = ⟨n, φ⟩ := packedCode_injective hi hφ
    subst p
    have hwv : w = v := assignmentCode_injective hv
    subst w
    exact hw
  · intro h
    exact ZFSet.mem_range_self (f := fun w : SatisfactionWitness M =>
      ZFSet.pair (packedCode indexCode w.1) (assignmentCode w.2.val)) ⟨⟨n, φ⟩, ⟨v, h⟩⟩

/-- This theorem provides a set, not merely a relation-valued field. -/
theorem exists_satisfactionSet {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) :
    ∃ S : ZFSet.{u}, ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n)
      (v : Fin n → ZFCarrier U),
      ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode v) ∈ S ↔
        OneYTruth.realize M φ Empty.elim v :=
  ⟨satisfactionSet indexCode M, fun _ φ v => mem_satisfactionSet_iff hi M φ v⟩

end OneYTruth
