import ZeroY.Syntax

/-!
# 合法表达式上的严格线序

有限自然数序列的字典序是严格线序，但在全部合法表达式上并不良基。
此处的线序性质不使用标准生成性或任何山脉转换定理。
-/

namespace ZeroY

namespace SeqLt

theorem irrefl (s : Sequence) : ¬ SeqLt s s := by
  induction s with
  | nil => intro h; cases h
  | cons value rest ih =>
      intro h
      cases h with
      | head h => exact Nat.lt_irrefl value h
      | tail _ h => exact ih h

theorem trans {s t u : Sequence} (hST : SeqLt s t) (hTU : SeqLt t u) :
    SeqLt s u := by
  induction hST generalizing u with
  | nil value rest =>
      cases hTU with
      | head _ => exact .nil _ _
      | tail _ _ => exact .nil _ _
  | head hOrder =>
      cases hTU with
      | head hNext => exact .head (Nat.lt_trans hOrder hNext)
      | tail _ _ => exact .head hOrder
  | tail value hTail ih =>
      cases hTU with
      | head hNext => exact .head hNext
      | tail _ hNext => exact .tail value (ih hNext)

theorem asymm {s t : Sequence} (hST : SeqLt s t) : ¬ SeqLt t s := by
  intro hTS
  exact irrefl s (trans hST hTS)

theorem trichotomy (s t : Sequence) : s = t ∨ SeqLt s t ∨ SeqLt t s := by
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => exact Or.inl rfl
      | cons value rest => exact Or.inr (Or.inl (.nil value rest))
  | cons value rest ih =>
      cases t with
      | nil => exact Or.inr (Or.inr (.nil value rest))
      | cons other tail =>
          by_cases hEqual : value = other
          · subst other
            rcases ih tail with hEqual | hForward | hBackward
            · exact Or.inl (congrArg (List.cons value) hEqual)
            · exact Or.inr (Or.inl (.tail value hForward))
            · exact Or.inr (Or.inr (.tail value hBackward))
          · by_cases hLess : value < other
            · exact Or.inr (Or.inl (.head hLess))
            · exact Or.inr (Or.inr (.head (by omega)))

/-- 相同的有限前缀可以从严格字典序比较中消去。 -/
theorem prefix_iff (initial s t : Sequence) :
    SeqLt (initial ++ s) (initial ++ t) ↔ SeqLt s t := by
  induction initial with
  | nil => rfl
  | cons value rest ih =>
      constructor
      · intro h
        cases h with
        | head hOrder => exact False.elim (Nat.lt_irrefl value hOrder)
        | tail _ hTail => exact ih.mp hTail
      · intro h
        exact .tail value (ih.mpr h)

end SeqLt

theorem exprLt_irrefl (s : Expr) : ¬ ExprLt s s := SeqLt.irrefl s.values

theorem exprLt_trans {s t u : Expr} (hST : ExprLt s t) (hTU : ExprLt t u) :
    ExprLt s u := SeqLt.trans hST hTU

theorem exprLt_trichotomy (s t : Expr) : s = t ∨ ExprLt s t ∨ ExprLt t s := by
  rcases SeqLt.trichotomy s.values t.values with hEqual | hForward | hBackward
  · exact Or.inl (Expr.ext hEqual)
  · exact Or.inr (Or.inl hForward)
  · exact Or.inr (Or.inr hBackward)

end ZeroY
