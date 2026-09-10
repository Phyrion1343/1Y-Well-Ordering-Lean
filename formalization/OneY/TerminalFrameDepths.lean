import OneY.TerminalFrameParents

/-! # BM4 entries are the computed depths of the actual terminal copy graph -/

namespace OneY.ParentForest

theorem depth_eq_parentDepth (F : ParentForest) (c : Nat) :
    F.depth c = ZeroY.parentDepth F.parent c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : F.parent c with
      | none => rw [F.depth_of_parent_none hp, ZeroY.Forest.parentDepth_none hp]
      | some p =>
          rw [F.depth_of_parent_some hp,
            ZeroY.Forest.parentDepth_some F.parent_left hp, ih p (F.parent_left hp)]

end OneY.ParentForest

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS

theorem expanded_entry (a : RootedRow) {K d x y cap index c : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hc : c < ((matrix (layers a K).row (x+1) cap).expand index).raw.length) (r : Nat) :
    matrixEntry ((matrix (layers a K).row (x+1) cap).expand index).raw c ((x+1)+1+r) =
      ((badAtTerminalContext a hbad).row r).depth c := by
  have hI := (expanded_relative_structure (layers a K).row (x+1) cap index hcap).1
  rw [depthRegular_eq_parentDepth hI ((x+1)+1+r) c hc,
    ParentForest.depth_eq_parentDepth]
  apply Forest.parentDepth_congr_below (fun hp => parent_some_lt hp)
  intro q hq
  exact expanded_parent a hbad hcap (by omega) r

theorem original_entry (a : RootedRow) {K d x y cap c : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hc : c < x+1) (r : Nat) :
    matrixEntry (matrix (layers a K).row (x+1) cap).raw c ((x+1)+1+r) =
      (((badAtTerminalContext a hbad).mountain.row r)).depth c :=
  matrix_numeric_entry_all (layers a K).row (hcap c hc) hc r

end OneY.NumericFrame

#print axioms OneY.ParentForest.depth_eq_parentDepth
#print axioms OneY.NumericFrame.expanded_entry
