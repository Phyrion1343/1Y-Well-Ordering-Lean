import ZeroY.Wiki.WellFounded

/-! # Wiki 任意参数迭代最终到达空式 -/

namespace ZeroY

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

theorem SeqLt.take_left {left right : Sequence} (hLess : SeqLt left right) (count : Nat) :
    SeqLt (left.take count) right := by
  induction hLess generalizing count with
  | nil value rest => simpa only [List.take_nil] using SeqLt.nil value rest
  | head hValue =>
      cases count with
      | zero => exact .nil _ _
      | succ count => exact .head hValue
  | tail value hPrior ih =>
      cases count with
      | zero => exact .nil _ _
      | succ count => exact .tail value (ih count)

theorem expandWiki_lt (s : Expr) (index : Nat) (hNonempty : 0 < s.values.length) :
    ExprLt (expandWiki s index) s :=
  SeqLt.take_left (expandY_lt s (index + 1) hNonempty) _

def wikiTrajectory (initial : Expr) (indices : Nat → Nat) : Nat → Expr
  | 0 => initial
  | step + 1 => expandWiki (wikiTrajectory initial indices step) (indices step)

universe u

theorem wikiTrajectory_terminates {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (initial : Expr) (indices : Nat → Nat) :
    ∃ step, (wikiTrajectory initial indices step).values = [] := by
  apply Classical.byContradiction
  intro hNever
  apply no_infinite_wikiStep_chain system
  refine ⟨wikiTrajectory initial indices, ?_⟩
  intro step
  have hNonempty : 0 < (wikiTrajectory initial indices step).values.length := by
    apply List.length_pos_iff.mpr
    intro hEmpty
    exact hNever ⟨step, hEmpty⟩
  refine ⟨⟨indices step, rfl⟩, ?_⟩
  intro hEqual
  have hLess := expandWiki_lt (wikiTrajectory initial indices step) (indices step) hNonempty
  change ExprLt (wikiTrajectory initial indices (step + 1))
    (wikiTrajectory initial indices step) at hLess
  rw [hEqual] at hLess
  exact exprLt_irrefl _ hLess

end ZeroY
