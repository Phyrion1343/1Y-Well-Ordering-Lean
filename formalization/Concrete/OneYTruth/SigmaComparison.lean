import OneYTruth.BoundedEvaluation
import OneYTruth.SatisfactionTrace

/-! # A bounded comparison of the genuine closed Sigma-one satisfaction nodes

The node set is the actual small range of well-scoped Sigma-one formulas
and assignments in the smaller domain. Its construction is independent
of either interpretation's truth. This file does not assert that the
complete node set or either satisfaction set belongs to an internal stage.
-/

namespace OneYTruth.SigmaComparison

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula FormulaCode

universe u v w

abbrev SigmaAssignment (k : Nat) (I : Type v) (U : ZFSet.{u}) :=
  Σ φ : {φ : Packed k I // IsSigmaOne φ.2}, Fin φ.val.1 → ZFCarrier U

/-- Every node contains genuine syntax with its arity and a genuine U-assignment. -/
noncomputable def sigmaNodes {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : SigmaAssignment k I U =>
    ZFSet.pair (packedCode indexCode w.1.val) (assignmentCode w.2))

theorem mem_sigmaNodes_iff {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U p : ZFSet.{u}) :
    p ∈ sigmaNodes (k := k) indexCode U ↔
      ∃ (n : Nat) (φ : (language k I).BoundedFormula Empty n), IsSigmaOne φ ∧
        ∃ xs : Fin n → ZFCarrier U,
          ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode xs) = p := by
  constructor
  · intro hp
    obtain ⟨⟨⟨⟨n, φ⟩, hφ⟩, xs⟩, he⟩ := ZFSet.mem_range.mp hp
    exact ⟨n, φ, hφ, xs, he⟩
  · rintro ⟨n, φ, hφ, xs, he⟩
    exact ZFSet.mem_range.mpr ⟨⟨⟨⟨n, φ⟩, hφ⟩, xs⟩, he⟩

theorem node_mem_sigmaNodes {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) {U : ZFSet.{u}} {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) (hφ : IsSigmaOne φ)
    (xs : Fin n → ZFCarrier U) :
    ZFSet.pair (packedCode indexCode ⟨n, φ⟩) (assignmentCode xs) ∈
      sigmaNodes (k := k) indexCode U :=
  (mem_sigmaNodes_iff indexCode U _).mpr ⟨n, φ, hφ, xs, rfl⟩

def Agree (nodes S T : ZFSet.{u}) : Prop := ∀ p ∈ nodes, p ∈ S ↔ p ∈ T

/-- Coordinates are the node set, the first truth set, and the second truth set. -/
def comparisonFormula : Delta0Formula 3 := BoundedEvaluation.atomicClauseAt 1 0 2

def parameters (nodes S T : ZFSet.{u}) : Tuple ZFSet.{u} 3 := ![nodes, S, T]

theorem satisfies_comparisonFormula (nodes S T : ZFSet.{u}) :
    Satisfies ZFMem comparisonFormula (parameters nodes S T) ↔ Agree nodes S T := by
  rw [comparisonFormula, BoundedEvaluation.satisfies_atomicClauseAt]
  rfl

def mixedComparisonFormula (k : Nat) (I : Type v) :=
  ofConstructibleDeltaZero k I comparisonFormula

theorem mixedComparisonFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedComparisonFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I comparisonFormula

theorem realize_mixedComparisonFormula {k : Nat} {I : Type v} {W : ZFSet.{u}}
    (hW : W.IsTransitive) (M : Interpretation k I (ZFCarrier W))
    (hmem : M.mem = zfCarrierMem W) (nodes S T : ZFSet.{u})
    (p : Fin 3 → ZFCarrier W) (hp : ∀ i, (p i).val = parameters nodes S T i) :
    OneYTruth.realize M (mixedComparisonFormula k I) Empty.elim p ↔ Agree nodes S T := by
  rw [mixedComparisonFormula, realize_ofConstructibleDeltaZero_absolute hW M hmem]
  have he : Constructible.Delta0Formula.val p = parameters nodes S T := funext hp
  rw [he]
  exact satisfies_comparisonFormula nodes S T

/-- A comparison of the two actual full truth sets is exactly preservation
of every genuine closed finite-scope Sigma-one formula and U-assignment. -/
theorem agree_satisfaction_iff_closed {k : Nat} {I : Type v} [Small.{u} I]
    {U V : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (N : Interpretation k I (ZFCarrier V))
    (f : ZFCarrier U → ZFCarrier V) (hf : ∀ a, (f a).val = a.val) :
    Agree (sigmaNodes (k := k) indexCode U) (satisfactionSet indexCode M) (satisfactionSet indexCode N) ↔
      ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), IsSigmaOne φ →
        ∀ xs : Fin n → ZFCarrier U,
          OneYTruth.realize N φ Empty.elim (f ∘ xs) ↔ OneYTruth.realize M φ Empty.elim xs := by
  have hCode {n : Nat} (xs : Fin n → ZFCarrier U) : assignmentCode xs = assignmentCode (f ∘ xs) :=
    assignmentCode_eq_of_values_eq xs (f ∘ xs) (fun i => (hf (xs i)).symm)
  constructor
  · intro h n φ hφ xs
    have ht := h _ (node_mem_sigmaNodes indexCode φ hφ xs)
    rw [mem_satisfactionSet_iff hi M, hCode xs, mem_satisfactionSet_iff hi N] at ht
    exact ht.symm
  · intro h p hp
    obtain ⟨n, φ, hφ, xs, rfl⟩ := (mem_sigmaNodes_iff indexCode U p).mp hp
    rw [mem_satisfactionSet_iff hi M, hCode xs, mem_satisfactionSet_iff hi N]
    exact (h n φ hφ xs).symm

theorem realize_comparison_iff_closed {k : Nat} {I : Type v} [Small.{u} I]
    {U V W : ZFSet.{u}} (indexCode : I → ZFSet.{u}) (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (N : Interpretation k I (ZFCarrier V))
    (f : ZFCarrier U → ZFCarrier V) (hf : ∀ a, (f a).val = a.val)
    {K : Nat} {J : Type w} (hW : W.IsTransitive) (A : Interpretation K J (ZFCarrier W))
    (hmem : A.mem = zfCarrierMem W) (p : Fin 3 → ZFCarrier W)
    (hp : ∀ i, (p i).val = parameters (sigmaNodes (k := k) indexCode U)
      (satisfactionSet indexCode M) (satisfactionSet indexCode N) i) :
    OneYTruth.realize A (mixedComparisonFormula K J) Empty.elim p ↔
      ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), IsSigmaOne φ →
        ∀ xs : Fin n → ZFCarrier U,
          OneYTruth.realize N φ Empty.elim (f ∘ xs) ↔ OneYTruth.realize M φ Empty.elim xs :=
  (realize_mixedComparisonFormula hW A hmem _ _ _ p hp).trans
    (agree_satisfaction_iff_closed indexCode hi M N f hf)

end OneYTruth.SigmaComparison

#print axioms OneYTruth.SigmaComparison.mem_sigmaNodes_iff
#print axioms OneYTruth.SigmaComparison.mixedComparisonFormula_isDeltaZero
#print axioms OneYTruth.SigmaComparison.realize_comparison_iff_closed
