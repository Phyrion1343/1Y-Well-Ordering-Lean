import OneY.ForestFrameMatrix

/-! # Finite matrices built from a proved tower of computed forest depths -/

namespace OneY.DepthMatrix

open ZeroY YesMetaZFC.BMS

def raw (F : Nat → ParentForest) (width height : Nat) : Matrix :=
  (List.range width).map fun c => (List.range height).map fun r => (F r).depth c

theorem raw_length (F : Nat → ParentForest) (width height : Nat) :
    (raw F width height).length = width := by
  simp only [raw, List.length_map, List.length_range]

theorem raw_rectangular (F : Nat → ParentForest) (width height : Nat) :
    rectangular (raw F width height) = true := by
  apply rectangular_iff_exists_uniformHeight.mpr
  refine ⟨height, ?_⟩
  intro col hcol
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcol
  simp only [List.length_map, List.length_range]

theorem raw_entry (F : Nat → ParentForest) {width height c r : Nat}
    (hc : c < width) (hr : r < height) :
    matrixEntry (raw F width height) c r = (F r).depth c := by
  simp [matrixEntry, columnEntry, raw, hc, hr]

theorem raw_entry_above (F : Nat → ParentForest) {width height c r : Nat}
    (hc : c < width) (hr : height ≤ r) : matrixEntry (raw F width height) c r = 0 := by
  have hr' : ¬ r < height := by omega
  simp [matrixEntry, columnEntry, raw, hc, hr']

theorem raw_parent (F : Nat → ParentForest) (width height : Nat)
    (hfirst : ∀ c, c < width →
      Forest.nearestSmaller ZeroY.linearParent (F 0).depth c = (F 0).parent c)
    (hstep : ∀ r c, c < width →
      Forest.nearestSmaller (F r).parent (F (r+1)).depth c = (F (r+1)).parent c)
    {r c : Nat} (hr : r < height) (hc : c < width) :
    parent r (raw F width height) c = (F r).parent c := by
  induction r generalizing c with
  | zero =>
      rw [parent_eq_nearestSmaller (raw_rectangular F width height) 0]
      change Forest.nearestSmaller ZeroY.linearParent
        (fun q => matrixEntry (raw F width height) q 0) c = _
      rw [Forest.nearestSmaller_congr_below
        (fun q hq => raw_entry F (by omega : q < width) hr)]
      exact hfirst c hc
  | succ r ih =>
      rw [parent_eq_nearestSmaller (raw_rectangular F width height) (r+1)]
      change Forest.nearestSmaller (parent r (raw F width height))
        (fun q => matrixEntry (raw F width height) q (r+1)) c = _
      rw [Forest.nearestSmaller_previous_congr_below
        (fun h => parent_some_lt h)
        (fun q hq => ih (by omega : r < height) (by omega : q < width))
        (fun q => matrixEntry (raw F width height) q (r+1))]
      rw [Forest.nearestSmaller_congr_below
        (fun q hq => raw_entry F (by omega : q < width) hr)]
      exact hstep r c hc

theorem raw_parent_above (F : Nat → ParentForest) {width height r c : Nat}
    (hr : height ≤ r) (hc : c < width) : parent r (raw F width height) c = none := by
  rw [parent_eq_nearestSmaller (raw_rectangular F width height) r]
  have hleft : Forest.Leftward (previousParent (raw F width height) r) := by
    cases r with
    | zero => exact ZeroY.linearParent_leftward
    | succ r => exact fun h => parent_some_lt h
  apply (Forest.nearestSmaller_none_iff hleft).mpr
  intro p ha
  rw [raw_entry_above F hc hr]
  exact Nat.zero_le _

theorem raw_depthRegular (F : Nat → ParentForest) (width height : Nat)
    (hfirst : ∀ c, c < width →
      Forest.nearestSmaller ZeroY.linearParent (F 0).depth c = (F 0).parent c)
    (hstep : ∀ r c, c < width →
      Forest.nearestSmaller (F r).parent (F (r+1)).depth c = (F (r+1)).parent c) :
    DepthRegular (raw F width height) := by
  intro r c hc
  rw [raw_length] at hc
  by_cases hr : r < height
  · rw [raw_parent F width height hfirst hstep hr hc]
    cases hp : (F r).parent c with
    | none =>
        rw [raw_entry F hc hr]
        exact (F r).depth_of_parent_none hp
    | some p =>
        have hpc := (F r).parent_left hp
        change matrixEntry (raw F width height) c r = matrixEntry (raw F width height) p r+1
        rw [raw_entry F hc hr, raw_entry F (by omega : p < width) hr]
        exact (F r).depth_of_parent_some hp
  · rw [raw_parent_above F (by omega : height ≤ r) hc]
    exact raw_entry_above F hc (by omega)

def matrix (F : Nat → ParentForest) (width height : Nat) : ValidArray where
  raw := trimZeroRows (raw F width height)
  rectangular_eq := rectangular_trimZeroRows (raw_rectangular F width height)
  trimmed_eq := trimZeroRows_idempotent _

theorem matrix_length (F : Nat → ParentForest) (width height : Nat) :
    (matrix F width height).raw.length = width := by
  change (trimZeroRows (raw F width height)).length = width
  rw [length_trimZeroRows, raw_length]

theorem matrix_depthRegular (F : Nat → ParentForest) (width height : Nat)
    (hfirst : ∀ c, c < width →
      Forest.nearestSmaller ZeroY.linearParent (F 0).depth c = (F 0).parent c)
    (hstep : ∀ r c, c < width →
      Forest.nearestSmaller (F r).parent (F (r+1)).depth c = (F (r+1)).parent c) :
    DepthRegular (matrix F width height).raw :=
  depthRegular_trimZeroRows (raw_depthRegular F width height hfirst hstep)

theorem matrix_parent (F : Nat → ParentForest) (width height : Nat)
    (hfirst : ∀ c, c < width →
      Forest.nearestSmaller ZeroY.linearParent (F 0).depth c = (F 0).parent c)
    (hstep : ∀ r c, c < width →
      Forest.nearestSmaller (F r).parent (F (r+1)).depth c = (F (r+1)).parent c)
    {r c : Nat} (hr : r < height) (hc : c < width) :
    parent r (matrix F width height).raw c = (F r).parent c := by
  change parent r (trimZeroRows (raw F width height)) c = _
  rw [parent_trimZeroRows_all]
  exact raw_parent F width height hfirst hstep hr hc

theorem matrix_entry (F : Nat → ParentForest) {width height r c : Nat}
    (hr : r < height) (hc : c < width) :
    matrixEntry (matrix F width height).raw c r = (F r).depth c := by
  change matrixEntry (trimZeroRows (raw F width height)) c r = _
  rw [matrixEntry_trimZeroRows]
  exact raw_entry F hc hr

theorem matrix_entry_above (F : Nat → ParentForest) {width height r c : Nat}
    (hr : height ≤ r) (hc : c < width) :
    matrixEntry (matrix F width height).raw c r = 0 := by
  change matrixEntry (trimZeroRows (raw F width height)) c r = _
  rw [matrixEntry_trimZeroRows]
  exact raw_entry_above F hc hr

end OneY.DepthMatrix

#print axioms OneY.DepthMatrix.matrix_depthRegular
#print axioms OneY.DepthMatrix.matrix_parent
