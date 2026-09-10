import ZeroY.Expansion
import ZeroY.Transport

/-!
# 0-Y 本身的生成集与有限展开路径

这些集合直接用独立的 0-Y 展开定义，不通过 BMS 编码像定义。
-/

namespace ZeroY

abbrev YStep := ExpansionStep expandY

inductive YExpansionPath : Expr → Expr → Prop
  | refl (s : Expr) : YExpansionPath s s
  | tail {root middle : Expr} (prior : YExpansionPath root middle) (index : Nat) :
      YExpansionPath root (expandY middle index)

namespace YExpansionPath

theorem single (s : Expr) (index : Nat) : YExpansionPath s (expandY s index) :=
  .tail (.refl s) index

theorem trans {first second third : Expr} (left : YExpansionPath first second)
    (right : YExpansionPath second third) : YExpansionPath first third := by
  induction right with
  | refl => exact left
  | tail prior index ih => exact .tail ih index

end YExpansionPath

inductive YGenerated : Expr → Prop
  | seed (height : Nat) : YGenerated (Expr.seed height)
  | expand {s : Expr} (prior : YGenerated s) (index : Nat) : YGenerated (expandY s index)

theorem yGenerated_of_path {root s : Expr} (hRoot : YGenerated root)
    (hPath : YExpansionPath root s) : YGenerated s := by
  induction hPath with
  | refl => exact hRoot
  | tail prior index ih => exact .expand ih index

theorem yGenerated_iff_seed_path (s : Expr) :
    YGenerated s ↔ ∃ height, YExpansionPath (Expr.seed height) s := by
  constructor
  · intro hGenerated
    induction hGenerated with
    | seed height => exact ⟨height, .refl _⟩
    | expand prior index ih =>
        obtain ⟨height, hPath⟩ := ih
        exact ⟨height, .tail hPath index⟩
  · rintro ⟨height, hPath⟩
    exact yGenerated_of_path (.seed height) hPath

abbrev YGeneratedExpr := {s : Expr // YGenerated s}

abbrev YDescendant (root : Expr) := {s : Expr // YExpansionPath root s}

def YGeneratedLt (first second : YGeneratedExpr) : Prop := ExprLt first.1 second.1

def YDescendantLt {root : Expr} (first second : YDescendant root) : Prop := ExprLt first.1 second.1

end ZeroY
