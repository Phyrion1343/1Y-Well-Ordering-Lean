import OneYTruth.EvaluationStep
import OneYTruth.SyntaxDiagram

/-!
# Pointwise convergence of canonical finite evaluation

Approximation sets need not be monotone. Every particular formula stabilizes
after its finite connective depth; in particular their unrestricted union
is not used as the satisfaction set.
-/

namespace OneYTruth.SyntaxDiagram

open FirstOrder FirstOrder.Language Constructible FormulaCode BoundedEvaluation

universe u v

def syntaxStep {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u})
    {n : Nat} (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U) : Prop :=
  match φ with
  | .falsum => False
  | .equal t s => OneYTruth.realize M (.equal t s) Empty.elim v
  | .rel r ts => OneYTruth.realize M (.rel r ts) Empty.elim v
  | .imp φ ψ => nodeCode indexCode ⟨⟨n, φ⟩, v⟩ ∈ S → nodeCode indexCode ⟨⟨n, ψ⟩, v⟩ ∈ S
  | .all φ => ∀ a : ZFCarrier U, nodeCode indexCode ⟨⟨n + 1, φ⟩, Fin.snoc v a⟩ ∈ S

theorem syntaxStep_of_atomic {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u})
    {n : Nat} (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U)
    (ha : IsAtomic φ) : syntaxStep indexCode M S φ v ↔ OneYTruth.realize M φ Empty.elim v := by
  cases φ <;> simp only [IsAtomic] at ha
  all_goals first | contradiction | rfl

theorem node_mem_stepSet_iff {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) (S : ZFSet.{u})
    (w : ScopedAssignment (k := k) I U) :
    nodeCode indexCode w ∈ stepSet (diagram indexCode M) S ↔ syntaxStep indexCode M S w.1.2 w.2 := by
  have hn : nodeCode indexCode w ∈ (diagram indexCode M).nodes := nodeCode_mem_scopedPairs indexCode w
  rw [mem_stepSet_iff, and_iff_right hn]
  constructor
  · rintro (hAtom | hImp | hAll)
    · obtain ⟨ha, ht⟩ := (mem_trueAtomSet_iff hi M w).mp hAtom
      exact (syntaxStep_of_atomic indexCode M S w.1.2 w.2 ha).mpr ht
    · obtain ⟨a, _, b, _, hab, hstep⟩ := hImp
      obtain ⟨⟨n, ⟨φ, ψ⟩, v⟩, ht⟩ := ZFSet.mem_range.mp hab
      obtain ⟨hp, hab⟩ := ZFSet.pair_inj.mp ht
      obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hab
      have hw : (⟨⟨n, .imp φ ψ⟩, v⟩ : ScopedAssignment (k := k) I U) = w :=
        nodeCode_injective hi hp
      subst w
      subst a
      subst b
      exact hstep
    · obtain ⟨hp, hchildren⟩ := hAll
      obtain ⟨q, hq⟩ := ZFSet.mem_range.mp hp
      have hw := nodeCode_injective hi hq
      subst w
      exact (all_children_iff hi S q).mp hchildren
  · intro h
    rcases w with ⟨⟨n, φ⟩, v⟩
    cases φ with
    | falsum => exact False.elim h
    | equal t s =>
      exact Or.inl ((mem_trueAtomSet_iff hi M ⟨⟨n, .equal t s⟩, v⟩).mpr ⟨trivial, h⟩)
    | rel r ts =>
      exact Or.inl ((mem_trueAtomSet_iff hi M ⟨⟨n, .rel r ts⟩, v⟩).mpr ⟨trivial, h⟩)
    | imp φ ψ =>
      exact Or.inr (Or.inl ⟨nodeCode indexCode ⟨⟨n, φ⟩, v⟩,
        nodeCode_mem_scopedPairs indexCode _, nodeCode indexCode ⟨⟨n, ψ⟩, v⟩,
        nodeCode_mem_scopedPairs indexCode _,
        ZFSet.mem_range_self (f := fun z : ImplicationAssignment (k := k) I U =>
          Godel.triple (nodeCode indexCode ⟨⟨z.1, .imp z.2.1.1 z.2.1.2⟩, z.2.2⟩)
            (nodeCode indexCode ⟨⟨z.1, z.2.1.1⟩, z.2.2⟩)
            (nodeCode indexCode ⟨⟨z.1, z.2.1.2⟩, z.2.2⟩)) ⟨n, (φ, ψ), v⟩, h⟩)
    | all φ =>
      let q : QuantifiedAssignment (k := k) I U := ⟨n, φ, v⟩
      exact Or.inr (Or.inr ⟨ZFSet.mem_range_self q, (all_children_iff hi S q).mpr h⟩)

def formulaDepth {k : Nat} {I : Type v} {n : Nat} :
    (language k I).BoundedFormula Empty n → Nat
  | .falsum | .equal _ _ | .rel _ _ => 0
  | .imp φ ψ => max (formulaDepth φ) (formulaDepth ψ) + 1
  | .all φ => formulaDepth φ + 1

theorem node_mem_iterate_iff_of_depth {k : Nat} {I : Type v} [Small.{u} I] {U : ZFSet.{u}}
    {indexCode : I → ZFSet.{u}} (hi : Function.Injective indexCode)
    (M : Interpretation k I (ZFCarrier U)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty n) (v : Fin n → ZFCarrier U)
    (m : Nat) (hm : formulaDepth φ + 1 ≤ m) :
    nodeCode indexCode ⟨⟨n, φ⟩, v⟩ ∈ iterate (diagram indexCode M) m ↔
      OneYTruth.realize M φ Empty.elim v := by
  induction φ generalizing m with
  | falsum =>
    cases m with
    | zero => simp [formulaDepth] at hm
    | succ m => exact node_mem_stepSet_iff hi M _ _
  | equal t s =>
    cases m with
    | zero => simp [formulaDepth] at hm
    | succ m => exact node_mem_stepSet_iff hi M _ _
  | rel r ts =>
    cases m with
    | zero => simp [formulaDepth] at hm
    | succ m => exact node_mem_stepSet_iff hi M _ _
  | imp φ ψ ihφ ihψ =>
    cases m with
    | zero => omega
    | succ m =>
      rw [iterate, node_mem_stepSet_iff hi M]
      change (nodeCode indexCode ⟨⟨_, φ⟩, v⟩ ∈ iterate (diagram indexCode M) m →
        nodeCode indexCode ⟨⟨_, ψ⟩, v⟩ ∈ iterate (diagram indexCode M) m) ↔ _
      have hφ : formulaDepth φ + 1 ≤ m := by simp only [formulaDepth] at hm; omega
      have hψ : formulaDepth ψ + 1 ≤ m := by simp only [formulaDepth] at hm; omega
      rw [ihφ v m hφ, ihψ v m hψ]
      rfl
  | all φ ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [iterate, node_mem_stepSet_iff hi M]
      have hφ : formulaDepth φ + 1 ≤ m := by simp only [formulaDepth] at hm; omega
      change (∀ a : ZFCarrier U, nodeCode indexCode ⟨⟨_, φ⟩, Fin.snoc v a⟩ ∈
        iterate (diagram indexCode M) m) ↔ _
      simp only [ih _ m hφ]
      rfl

end OneYTruth.SyntaxDiagram
