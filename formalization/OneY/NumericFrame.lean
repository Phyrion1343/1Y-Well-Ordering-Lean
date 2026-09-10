import OneY.DepthMatrix
import OneY.SparseDepth
import OneY.TopComparison

/-!
# An actual sparse numerical mountain above its finite candidate frame

This matrix represents the finite depth coordinates. Column top values
remain separate data: no root-one numerical decoding is asserted here.
-/

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS

def forest (base : Row) (width r : Nat) : ParentForest :=
  if r ≤ width then ForestFrame.rowForest base.forest width r
  else (rows base (r-width-1)).forest

theorem forest_frame (base : Row) (width : Nat) {r : Nat} (hr : r ≤ width) :
    forest base width r = ForestFrame.rowForest base.forest width r := by
  simp only [forest, if_pos hr]

theorem forest_numeric (base : Row) (width r : Nat) :
    forest base width (width+1+r) = (rows base r).forest := by
  have hn : ¬ width+1+r ≤ width := by omega
  have he : width+1+r-width-1 = r := by omega
  rw [forest, if_neg hn, he]

theorem forest_boundary (base : Row) (width : Nat) :
    forest base width width = base.forest := by
  rw [forest_frame base width (Nat.le_refl width)]
  cases base.forest
  simp [ForestFrame.rowForest, ForestFrame.cutoff]

theorem forest_first (base : Row) {width c : Nat} (hc : c < width) :
    Forest.nearestSmaller ZeroY.linearParent (forest base width 0).depth c =
      (forest base width 0).parent c := by
  have hf := forest_frame base width (Nat.zero_le width)
  rw [hf]
  rw [Forest.nearestSmaller_previous_congr_below ZeroY.linearParent_leftward
    (fun q hq => (ForestFrame.rowForest_initial_parent base.forest
      (by omega : q < width)).symm)]
  exact (ForestFrame.rowForest base.forest width 0).nearestSmaller_depth_parent c

theorem forest_step (base : Row) (width r c : Nat) :
    Forest.nearestSmaller (forest base width r).parent (forest base width (r+1)).depth c =
      (forest base width (r+1)).parent c := by
  by_cases hr : r < width
  · rw [forest_frame base width (by omega : r ≤ width),
      forest_frame base width (by omega : r+1 ≤ width)]
    exact ForestFrame.rowForest_step base.forest width r c
  · by_cases he : r = width
    · subst r
      have hn := forest_numeric base width 0
      simp only [Nat.add_zero] at hn
      rw [forest_boundary, hn]
      exact base.forest.nearestSmaller_depth_parent c
    · have ha : width+1+(r-width-1) = r := by omega
      have hb : width+1+((r-width-1)+1) = r+1 := by omega
      rw [← ha, forest_numeric, ha, ← hb, forest_numeric]
      exact (rows base (r-width-1)).next_depth_nearestSmaller c

def matrix (base : Row) (width cap : Nat) : ValidArray :=
  DepthMatrix.matrix (forest base width) width (width+1+cap)

theorem matrix_length (base : Row) (width cap : Nat) :
    (matrix base width cap).raw.length = width :=
  DepthMatrix.matrix_length _ _ _

theorem matrix_depthRegular (base : Row) (width cap : Nat) :
    DepthRegular (matrix base width cap).raw :=
  DepthMatrix.matrix_depthRegular _ _ _ (fun _ hc => forest_first base hc)
    (fun r c _ => forest_step base width r c)

theorem matrix_parent (base : Row) {width cap r c : Nat}
    (hr : r < width+1+cap) (hc : c < width) :
    parent r (matrix base width cap).raw c = (forest base width r).parent c :=
  DepthMatrix.matrix_parent _ _ _ (fun _ hq => forest_first base hq)
    (fun u q _ => forest_step base width u q) hr hc

theorem matrix_numeric_parent (base : Row) {width cap r c : Nat}
    (hr : r < cap) (hc : c < width) :
    parent (width+1+r) (matrix base width cap).raw c = (rows base r).forest.parent c := by
  rw [matrix_parent base (by omega : width+1+r < width+1+cap) hc, forest_numeric]

theorem matrix_numeric_entry (base : Row) {width cap r c : Nat}
    (hr : r < cap) (hc : c < width) :
    matrixEntry (matrix base width cap).raw c (width+1+r) = (rows base r).forest.depth c := by
  unfold matrix
  rw [DepthMatrix.matrix_entry _ (by omega : width+1+r < width+1+cap) hc, forest_numeric]

theorem matrix_numeric_entry_all (base : Row) {width cap c : Nat}
    (hcap : base.value c ≤ cap) (hc : c < width) (r : Nat) :
    matrixEntry (matrix base width cap).raw c (width+1+r) = (rows base r).forest.depth c := by
  by_cases hr : r < cap
  · exact matrix_numeric_entry base hr hc
  · unfold matrix
    rw [DepthMatrix.matrix_entry_above _ (by omega : width+1+cap ≤ width+1+r) hc,
      rows_depth_zero_of_bound base (by omega : base.value c ≤ r)]

theorem matrix_numeric_parent_all (base : Row) {width cap c : Nat}
    (hcap : base.value c ≤ cap) (hc : c < width) (r : Nat) :
    parent (width+1+r) (matrix base width cap).raw c = (rows base r).forest.parent c := by
  by_cases hr : r < cap
  · exact matrix_numeric_parent base hr hc
  · have hn : (rows base r).forest.parent c = none :=
      ((rows base r).forest.depth_zero_iff c).mp
        (rows_depth_zero_of_bound base (by omega : base.value c ≤ r))
    rw [hn]
    change parent (width+1+r) (trimZeroRows (DepthMatrix.raw _ _ _)) c = none
    rw [parent_trimZeroRows_all]
    exact DepthMatrix.raw_parent_above _ (by omega) hc

end OneY.NumericFrame

#print axioms OneY.NumericFrame.matrix_depthRegular
#print axioms OneY.NumericFrame.matrix_numeric_parent_all
#print axioms OneY.NumericFrame.matrix_numeric_entry_all
