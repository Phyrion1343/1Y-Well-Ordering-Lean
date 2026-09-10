import Lean

/-!
# 全部合法 0-Y 表达式

合法性只要求空序列，或首项为 1 且所有项为正；不要求从标准种子生成。
序列长度保留，因此空表达式与任意多个 1 构成的表达式不同。
-/

namespace ZeroY

abbrev Sequence := List Nat

/-- 全部项为正，且非空时首项为 1。 -/
def Legal (s : Sequence) : Prop :=
  (∀ value ∈ s, 0 < value) ∧ (s = [] ∨ s.head? = some 1)

/-- 表达式的载体不包含标准生成性条件。 -/
structure Expr where
  values : Sequence
  legal : Legal values

namespace Expr

@[ext]
theorem ext {s t : Expr} (h : s.values = t.values) : s = t := by
  cases s
  cases t
  simp_all

def empty : Expr := ⟨[], by simp [Legal]⟩

/-- 行数为 height 的非零标准种子对应 (1,height+1)。 -/
def seed (height : Nat) : Expr :=
  ⟨[1, height + 1], by simp [Legal]⟩

end Expr

/-- 有限序列的严格字典序；真前缀较小。 -/
inductive SeqLt : Sequence → Sequence → Prop where
  | nil (value : Nat) (rest : Sequence) : SeqLt [] (value :: rest)
  | head {a b : Nat} {s t : Sequence} (h : a < b) : SeqLt (a :: s) (b :: t)
  | tail (value : Nat) {s t : Sequence} (h : SeqLt s t) :
      SeqLt (value :: s) (value :: t)

def ExprLt (s t : Expr) : Prop := SeqLt s.values t.values

/-- 全域字典序下降族：第 k 项是 k+1 个 1 后接 2。 -/
def descendingValues : Nat → Sequence
  | 0 => [1, 2]
  | k + 1 => 1 :: descendingValues k

theorem descendingValues_legal (k : Nat) : Legal (descendingValues k) := by
  induction k with
  | zero => simp [descendingValues, Legal]
  | succ k ih =>
      rcases ih with ⟨hPositive, _⟩
      constructor
      · intro value hMem
        simp only [descendingValues, List.mem_cons] at hMem
        rcases hMem with hEqual | hMem
        · subst value
          exact Nat.zero_lt_succ 0
        · exact hPositive value hMem
      · exact Or.inr rfl

def descendingExpr (k : Nat) : Expr :=
  ⟨descendingValues k, descendingValues_legal k⟩

theorem descendingValues_lt (k : Nat) :
    SeqLt (descendingValues (k + 1)) (descendingValues k) := by
  induction k with
  | zero => exact .tail 1 (.head (by decide))
  | succ k ih => exact .tail 1 ih

theorem descendingExpr_lt (k : Nat) :
    ExprLt (descendingExpr (k + 1)) (descendingExpr k) :=
  descendingValues_lt k

/-- 下降族本身已经排除全部合法表达式的全域字典序良基性。 -/
theorem exprLt_not_wellFounded : ¬ WellFounded ExprLt := by
  intro hWellFounded
  have hNoChain : ∀ s : Expr, Acc ExprLt s → ∀ k, descendingExpr k ≠ s := by
    intro s hAcc
    induction hAcc with
    | intro s _ ih =>
        intro k hEqual
        have hSmaller : ExprLt (descendingExpr (k + 1)) s := by
          rw [← hEqual]
          exact descendingExpr_lt k
        exact ih (descendingExpr (k + 1)) hSmaller (k + 1) rfl
  exact hNoChain (descendingExpr 0) (hWellFounded.apply _) 0 rfl

end ZeroY
