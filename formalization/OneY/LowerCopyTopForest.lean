import OneY.LowerCopyRoots
import OneY.FrameCopy
import OneY.SparseBlocker

/-! # The exact transported vertical root forest

Although the pseudo-parent forest has an exceptional contraction, its
strict-height root forest follows the ordinary last-column seam rule.
This is a purely geometric theorem about the computed copied graph.
-/

namespace OneY.LowerCopy.Context

theorem topForest_parent_original (C : Context) {c : Nat} (hc : c ≤ C.coordinates.x) :
    C.toRowMountain.topForest.parent c = C.mountain.topForest.parent c := by
  change (if C.height c = 0 then none else some (C.toRowMountain.rootAt (C.height c-1) c)) = _
  rw [C.height_original hc, C.rootAt_original hc]
  rfl

theorem topForest_parent_encode (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.toRowMountain.topForest.parent (C.coordinates.encode s b) =
      (C.mountain.topForest.parent s).map (C.coordinates.parentCopy b) := by
  change (if C.height (C.coordinates.encode s b) = 0 then none else
    some (C.toRowMountain.rootAt (C.height (C.coordinates.encode s b)-1) (C.coordinates.encode s b))) = _
  rw [C.height_encode hs hx b]
  by_cases hCone : C.InCone s
  · rw [if_pos hCone]
    have hHeight := C.height_lt_of_inCone hCone hs
    have hOldPos : C.mountain.height s ≠ 0 := by omega
    have hNewPos : C.mountain.height s+b*C.rise ≠ 0 := by omega
    have hRow : C.mountain.height s+b*C.rise-1 = C.mountain.height s-1+b*C.rise := by omega
    rw [if_neg hNewPos, hRow, C.rootAt_lifted hs hx hCone (by omega) b]
    change some _ = (if C.mountain.height s = 0 then none else some _).map _
    rw [if_neg hOldPos, Option.map_some, C.coordinates.parentCopy_bad b
      (C.root_le_of_inCone (C.high_root_inCone (by omega : C.floor ≤ C.mountain.height s-1) hCone))]
  · rw [if_neg hCone]
    by_cases hZero : C.mountain.height s = 0
    · rw [if_pos hZero]
      change none = (if C.mountain.height s = 0 then none else some _).map _
      rw [if_pos hZero, Option.map_none]
    · rw [if_neg hZero, C.rootAt_outside hs hx hCone b]
      change some _ = (if C.mountain.height s = 0 then none else some _).map _
      rw [if_neg hZero, Option.map_some]

theorem topForest_eq_frameCopy (C : Context) :
    C.toRowMountain.topForest = FrameCopy.forest C.coordinates C.mountain.topForest := by
  apply Numeric.parentForest_eq_of_parent_eq
  intro c
  change C.toRowMountain.topForest.parent c = FrameCopy.parent C.coordinates C.mountain.topForest c
  by_cases hc : c ≤ C.coordinates.x
  · rw [C.topForest_parent_original hc, FrameCopy.parent_original C.coordinates C.mountain.topForest hc]
  · have hs := C.coordinates.source_bounds c
    have he := C.coordinates.encode_coordinates (by have := C.coordinates.root_lt_last; omega : C.coordinates.y < c)
    rw [← he, C.topForest_parent_encode hs.1 hs.2,
      FrameCopy.parent_encode C.coordinates C.mountain.topForest hs.1 hs.2]

#print axioms topForest_parent_encode
#print axioms topForest_eq_frameCopy

end OneY.LowerCopy.Context
