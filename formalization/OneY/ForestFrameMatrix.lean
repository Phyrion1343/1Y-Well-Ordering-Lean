import OneY.ForestFrame
import ZeroY.Structural.RawRecognition

/-!
# The concrete finite cutoff frame as a BM4 matrix

Its entries are computed forest depths. The actual BM4 parent algorithm is
proved to recover those forests on the finite column prefix, and trimming
preserves both the recovered parents and depth regularity.
-/

namespace OneY.ForestFrame

open YesMetaZFC.BMS ZeroY

def raw (F : ParentForest) (width : Nat) : Matrix :=
  (List.range width).map fun c =>
    (List.range (width+1)).map fun r => (rowForest F width r).depth c

theorem raw_length (F : ParentForest) (width : Nat) : (raw F width).length = width := by
  simp only [raw, List.length_map, List.length_range]

theorem raw_rectangular (F : ParentForest) (width : Nat) :
    rectangular (raw F width) = true := by
  apply rectangular_iff_exists_uniformHeight.mpr
  refine ⟨width+1, ?_⟩
  intro col hcol
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcol
  simp only [List.length_map, List.length_range]

theorem raw_entry (F : ParentForest) {width c r : Nat}
    (hc : c < width) (hr : r ≤ width) :
    matrixEntry (raw F width) c r = (rowForest F width r).depth c := by
  have hr' : r < width+1 := by omega
  simp [matrixEntry, columnEntry, raw, hc, hr']

theorem raw_entry_above (F : ParentForest) {width c r : Nat}
    (hc : c < width) (hr : width < r) : matrixEntry (raw F width) c r = 0 := by
  have hr' : ¬ r < width+1 := by omega
  simp [matrixEntry, columnEntry, raw, hc, hr']

/-- These are actual BM4 parents, with no matrix parent graph supplied as
an additional field. -/
theorem raw_parent (F : ParentForest) {width r c : Nat}
    (hr : r ≤ width) (hc : c < width) :
    parent r (raw F width) c = (rowForest F width r).parent c := by
  induction r generalizing c with
  | zero =>
      rw [parent_eq_nearestSmaller (raw_rectangular F width) 0]
      have hPrevious := Forest.nearestSmaller_previous_congr_below
        (target := c)
        ZeroY.linearParent_leftward
        (fun q hq => (rowForest_initial_parent F (by omega : q < width)).symm)
        (fun q => matrixEntry (raw F width) q 0)
      change Forest.nearestSmaller ZeroY.linearParent
        (fun q => matrixEntry (raw F width) q 0) c = _
      rw [hPrevious, Forest.nearestSmaller_congr_below
        (fun q hq => raw_entry F (by omega : q < width) (by omega : 0 ≤ width))]
      exact (rowForest F width 0).nearestSmaller_depth_parent c
  | succ r ih =>
      rw [parent_eq_nearestSmaller (raw_rectangular F width) (r+1)]
      change Forest.nearestSmaller (parent r (raw F width))
        (fun q => matrixEntry (raw F width) q (r+1)) c = _
      rw [Forest.nearestSmaller_previous_congr_below
        (fun h => parent_some_lt h)
        (fun q hq => ih (by omega : r ≤ width) (by omega : q < width))
        (fun q => matrixEntry (raw F width) q (r+1))]
      rw [Forest.nearestSmaller_congr_below
        (fun q hq => raw_entry F (by omega : q < width) hr)]
      exact rowForest_step F width r c

theorem raw_parent_above (F : ParentForest) {width r c : Nat}
    (hr : width < r) (hc : c < width) : parent r (raw F width) c = none := by
  rw [parent_eq_nearestSmaller (raw_rectangular F width) r]
  have hleft : Forest.Leftward (previousParent (raw F width) r) := by
    cases r with
    | zero => exact ZeroY.linearParent_leftward
    | succ r => exact fun h => parent_some_lt h
  apply (Forest.nearestSmaller_none_iff hleft).mpr
  intro p ha
  rw [raw_entry_above F hc hr]
  exact Nat.zero_le _

theorem raw_depthRegular (F : ParentForest) (width : Nat) : DepthRegular (raw F width) := by
  intro r c hc
  rw [raw_length] at hc
  by_cases hr : r ≤ width
  · rw [raw_parent F hr hc]
    cases hp : (rowForest F width r).parent c with
    | none =>
        rw [raw_entry F hc hr]
        exact (rowForest F width r).depth_of_parent_none hp
    | some p =>
        have hpc := (rowForest F width r).parent_left hp
        change matrixEntry (raw F width) c r = matrixEntry (raw F width) p r+1
        rw [raw_entry F hc hr, raw_entry F (by omega : p < width) hr]
        exact (rowForest F width r).depth_of_parent_some hp
  · rw [raw_parent_above F (by omega : width < r) hc]
    exact raw_entry_above F hc (by omega)

def matrix (F : ParentForest) (width : Nat) : ValidArray where
  raw := trimZeroRows (raw F width)
  rectangular_eq := rectangular_trimZeroRows (raw_rectangular F width)
  trimmed_eq := trimZeroRows_idempotent _

theorem matrix_length (F : ParentForest) (width : Nat) :
    (matrix F width).raw.length = width := by
  change (trimZeroRows (raw F width)).length = width
  rw [length_trimZeroRows, raw_length]

theorem matrix_depthRegular (F : ParentForest) (width : Nat) :
    DepthRegular (matrix F width).raw :=
  depthRegular_trimZeroRows (raw_depthRegular F width)

theorem matrix_parent (F : ParentForest) {width r c : Nat}
    (hr : r ≤ width) (hc : c < width) :
    parent r (matrix F width).raw c = (rowForest F width r).parent c := by
  change parent r (trimZeroRows (raw F width)) c = _
  rw [parent_trimZeroRows_all]
  exact raw_parent F hr hc

theorem matrix_terminal_parent (F : ParentForest) {width c : Nat} (hc : c < width) :
    parent width (matrix F width).raw c = F.parent c := by
  rw [matrix_parent F (Nat.le_refl width) hc]
  exact rowForest_terminal_parent F width c

end OneY.ForestFrame

#print axioms OneY.ForestFrame.raw_parent
#print axioms OneY.ForestFrame.matrix_depthRegular
#print axioms OneY.ForestFrame.matrix_terminal_parent
