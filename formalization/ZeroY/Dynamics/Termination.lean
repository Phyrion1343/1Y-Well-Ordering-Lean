import ZeroY.Dynamics.Equivalence

/-!
# 任意指标选择的实际迭代最终到达空式

该结论比仅陈述严格展开关系良基更直接：从任意合法起点，每一步任选
自然数参数，按真正展开函数迭代，有限步后必为空式。
-/

namespace ZeroY

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

def yTrajectory (initial : Expr) (indices : Nat → Nat) : Nat → Expr
  | 0 => initial
  | step + 1 => expandY (yTrajectory initial indices step) (indices step)

universe u

theorem yTrajectory_terminates {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (initial : Expr) (indices : Nat → Nat) :
    ∃ step, (yTrajectory initial indices step).values = [] := by
  apply Classical.byContradiction
  intro hNever
  apply no_infinite_yStep_chain system
  refine ⟨yTrajectory initial indices, ?_⟩
  intro step
  have hNonempty : 0 < (yTrajectory initial indices step).values.length := by
    apply List.length_pos_iff.mpr
    intro hEmpty
    exact hNever ⟨step, hEmpty⟩
  refine ⟨⟨indices step, rfl⟩, ?_⟩
  intro hEqual
  have hLess := expandY_lt (yTrajectory initial indices step) (indices step) hNonempty
  change ExprLt (yTrajectory initial indices (step + 1))
    (yTrajectory initial indices step) at hLess
  rw [hEqual] at hLess
  exact exprLt_irrefl _ hLess

end ZeroY
