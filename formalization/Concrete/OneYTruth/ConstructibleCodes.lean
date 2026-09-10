import OneYTruth.SyntaxDiagram
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# Individual codes stay inside a specified limit constructible level

These are genuine bounds in `LStageZF θ`, stronger than membership in the
whole class L. They concern individual finite codes and give subset bounds
for syntax/assignment collections. A subset of `LStageZF θ` is NOT thereby
an element of `LStageZF θ`; the internal collection obligation remains.
-/

namespace OneYTruth.FormulaCode

open Constructible Constructible.FiniteSequenceZF

universe u v

theorem rawCode_mem_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ LStageZF θ) (φ : Raw I) :
    rawCode indexCode φ ∈ LStageZF θ := by
  induction φ <;> simp only [rawCode]
  all_goals
    apply sequenceCode_mem_LStageZF_of_isSuccLimit hθ
    simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
      false_implies, forall_const, natCode_mem_LStageZF_of_isSuccLimit hθ, and_true]

theorem formulaCode_mem_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k n : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ LStageZF θ)
    (φ : (language k I).BoundedFormula Empty n) :
    formulaCode indexCode φ ∈ LStageZF θ := rawCode_mem_LStageZF hθ hi (toRaw φ)

theorem packedCode_mem_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k : Nat} {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ LStageZF θ) (φ : Packed k I) :
    packedCode indexCode φ ∈ LStageZF θ :=
  orderedPair_mem_LStageZF_of_isSuccLimit hθ
    (natCode_mem_LStageZF_of_isSuccLimit hθ φ.1) (formulaCode_mem_LStageZF hθ hi φ.2)

/-- Even the language at the endpoint θ only names ordinals strictly below θ. -/
theorem ordinalIndexCode_mem_LStageZF {θ η : Ordinal.{u}} (hηθ : η ≤ θ)
    (i : {ξ : Ordinal.{u} // ξ < η}) :
    ordinalIndexCode i ∈ LStageZF θ :=
  ordinal_toZFSet_mem_LStageZF_of_lt (lt_of_lt_of_le i.property hηθ)

end OneYTruth.FormulaCode

namespace OneYTruth

open Constructible Constructible.FiniteSequenceZF FormulaCode

universe u v

theorem assignmentCode_mem_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {U : ZFSet.{u}} (hU : U ⊆ LStageZF θ) {n : Nat} (v : Fin n → ZFCarrier U) :
    assignmentCode v ∈ LStageZF θ := by
  apply sequenceCode_mem_LStageZF_of_isSuccLimit hθ
  intro x hx
  rw [List.mem_reverse] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hU (v i).property

theorem SyntaxDiagram.nodeCode_mem_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k : Nat} {I : Type v} {U : ZFSet.{u}} (hU : U ⊆ LStageZF θ)
    {indexCode : I → ZFSet.{u}} (hi : ∀ i, indexCode i ∈ LStageZF θ)
    (w : ScopedAssignment (k := k) I U) :
    SyntaxDiagram.nodeCode indexCode w ∈ LStageZF θ :=
  orderedPair_mem_LStageZF_of_isSuccLimit hθ
    (packedCode_mem_LStageZF hθ hi w.1) (assignmentCode_mem_LStageZF hθ hU w.2)

/-- A collection bound, deliberately stated as subset rather than elementhood. -/
theorem scopedPairs_subset_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}} (hU : U ⊆ LStageZF θ)
    {indexCode : I → ZFSet.{u}} (hi : ∀ i, indexCode i ∈ LStageZF θ) :
    scopedPairs (k := k) U indexCode ⊆ LStageZF θ := by
  intro x hx
  obtain ⟨w, rfl⟩ := ZFSet.mem_range.mp hx
  exact SyntaxDiagram.nodeCode_mem_LStageZF hθ hU hi w

/-- The full external truth set has small individual codes; this alone does not internalize it. -/
theorem satisfactionSet_subset_LStageZF {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}} (hU : U ⊆ LStageZF θ)
    {indexCode : I → ZFSet.{u}} (hi : ∀ i, indexCode i ∈ LStageZF θ)
    (M : Interpretation k I (ZFCarrier U)) :
    satisfactionSet indexCode M ⊆ LStageZF θ := by
  intro x hx
  obtain ⟨⟨φ, v, _⟩, rfl⟩ := ZFSet.mem_range.mp hx
  exact SyntaxDiagram.nodeCode_mem_LStageZF hθ hU hi ⟨φ, v⟩

end OneYTruth
