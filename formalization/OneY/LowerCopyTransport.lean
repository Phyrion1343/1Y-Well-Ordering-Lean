import OneY.LowerCopyBottomRecovery

/-! # B/C transport produced by a restored lower layer

The input comparisons concern its upper layer only. The lower layer's
finite-row and inherited-frame NS equations are obtained from the proved
recovery theorems, rather than assumed.
-/

namespace OneY.LowerCopy.Context

open Reconstruction

theorem value_copy_of_good_base_parent (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    {s : Nat} (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hGood : ∀ p, base.forest.parent s = some p → p < C.coordinates.y) (b : Nat) :
    value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) = base.value s := by
  cases hp : (C.mountain.row 0).parent s with
  | none =>
      rw [C.value_bottom_none_eq_one base hBase hRoots hMountain newTop hFixed hs (Nat.le_of_lt hx) hp b]
      have hb : base.forest.parent s = none := by rw [hMountain] at hp; exact hp
      exact (hRoots s hb).symm
  | some p =>
      have hb : base.forest.parent s = some p := by rw [hMountain] at hp; exact hp
      rw [← C.value_tail_eq_from_upperFixed (Numeric.topValue base) newTop
        (fun q hq => hPrefixTop q (by have := C.coordinates.root_lt_last; omega)) hFixed
        hs hx hp (hGood p hb) b 0 (Nat.le_refl _), hMountain, value_numeric_base]

theorem depth_zero_lt_copy_of_common_frame (C : Context) (F : ParentForest)
    (hNS : ∀ i, ZeroY.Forest.nearestSmaller F.parent (C.mountain.row 0).depth i = (C.mountain.row 0).parent i)
    {s z : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hz : C.coordinates.y < z) (hzx : z ≤ C.coordinates.x)
    (hFrame : F.parent s = F.parent z)
    (hDepth : (C.mountain.row 0).depth s < (C.mountain.row 0).depth z) (b : Nat) :
    (C.row 0).depth (C.coordinates.parentCopy b s) < (C.row 0).depth (C.coordinates.parentCopy b z) := by
  have hMono : (C.mountain.row 0).Ancestor C.coordinates.y s →
      (C.mountain.row 0).Ancestor C.coordinates.y z :=
    ParentForest.ancestor_mono_of_common_chain_depth F (C.mountain.row 0) hNS
      (ZeroY.Forest.ancestor_iff_of_parent_eq hFrame) (Nat.le_of_lt hDepth)
  by_cases hFloor : 0 < C.floor
  · by_cases hAS : (C.mountain.row 0).Ancestor C.coordinates.y s
    · rw [C.depth_low_of_root_ancestor hx (Or.inr hAS) hFloor b,
        C.depth_low_of_root_ancestor hzx (Or.inr (hMono hAS)) hFloor b]
      omega
    · rw [C.depth_low_of_no_root_ancestor hx (by omega) hAS hFloor b]
      by_cases hAZ : (C.mountain.row 0).Ancestor C.coordinates.y z
      · rw [C.depth_low_of_root_ancestor hzx (Or.inr hAZ) hFloor b]
        omega
      · rw [C.depth_low_of_no_root_ancestor hzx (by omega) hAZ hFloor b]
        exact hDepth
  · have he : C.floor = 0 := by omega
    have hConeMono : C.InCone s → C.InCone z := by
      rw [C.inCone_iff_root_ancestor (by omega), C.inCone_iff_root_ancestor (by omega), he]
      exact hMono
    by_cases hCS : C.InCone s
    · have hCZ := hConeMono hCS
      have hS := C.depth_floor_inCone hs hx hCS b
      have hZ := C.depth_floor_inCone hz hzx hCZ b
      rw [he] at hS hZ
      rw [hS, hZ]
      omega
    · rw [C.depth_outside_high hx hCS (by omega : C.floor ≤ 0) b]
      by_cases hCZ : C.InCone z
      · have hZ := C.depth_floor_inCone hz hzx hCZ b
        rw [he] at hZ
        rw [hZ]
        omega
      · rw [C.depth_outside_high hzx hCZ (by omega : C.floor ≤ 0) b]
        exact hDepth

/-- B for the inherited candidate frame. It feeds the next lower layer's
`UpperOrder` once that inherited frame is identified with its pseudo forest. -/
theorem value_copy_le_of_common_frame (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hBound : PseudoTopBound C.toRowMountain newTop)
    {s z : Nat} (hz : C.coordinates.y < z) (hZS : z < s) (hsx : s ≤ C.coordinates.x)
    (hFrame : F.parent s = F.parent z) (hLe : base.value s ≤ base.value z) (b : Nat) :
    value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop 0 (C.coordinates.parentCopy b z) := by
  have hSelected' : ∀ i, Numeric.restrictedParent F base.value i = (C.mountain.row 0).parent i := by
    intro i; rw [hMountain]; exact hSelected i
  have hOldForest : (Numeric.select F base.value).forest = C.mountain.row 0 :=
    Numeric.parentForest_eq_of_parent_eq _ _ hSelected'
  have hCompare := Numeric.select_common_parent_depth_compare F base.value (hBase s) (hBase z) hFrame hLe
  rw [hOldForest] at hCompare
  by_cases hEq : (C.mountain.row 0).depth s = (C.mountain.row 0).depth z
  · have hParent : (C.mountain.row 0).parent s = (C.mountain.row 0).parent z := by
      simpa only [hSelected'] using hCompare.2 hEq
    cases hp : (C.mountain.row 0).parent s with
    | none =>
        rw [C.value_bottom_none_eq_one base hBase hRoots hMountain newTop hFixed (by omega) hsx hp b,
          C.value_bottom_none_eq_one base hBase hRoots hMountain newTop hFixed hz (by omega) (hParent.symm.trans hp) b]
        exact Nat.le_refl _
    | some p =>
        exact C.bottom_value_le_copy_of_common_parent base hBase hMountain newTop hPositive hUpper
          (C.restrictedParent_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound)
          hz hZS hsx hp (hParent.symm.trans hp) hLe b
  · have hDepth : (C.mountain.row 0).depth s < (C.mountain.row 0).depth z := by omega
    have hNS : ∀ i, ZeroY.Forest.nearestSmaller F.parent (C.mountain.row 0).depth i = (C.mountain.row 0).parent i := by
      intro i
      rw [← hOldForest]
      exact Numeric.select_depth_nearestSmaller F base.value (fun c hc => by have := hBase c; omega) i
    have hNewDepth := C.depth_zero_lt_copy_of_common_frame F hNS (by omega) hsx hz (by omega) hFrame hDepth b
    have hNewForest : (Numeric.select (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0)).forest = C.row 0 :=
      Numeric.parentForest_eq_of_parent_eq _ _
        (C.restrictedParent_bottom_numeric base hBase hRoots hMountain F hSelected newTop hPositive hPrefixTop hFixed hUpper hBound)
    have hNewFrame : (FrameCopy.forest C.coordinates F).parent (C.coordinates.parentCopy b s) =
        (FrameCopy.forest C.coordinates F).parent (C.coordinates.parentCopy b z) := by
      change FrameCopy.parent _ _ _ = FrameCopy.parent _ _ _
      rw [FrameCopy.parent_nonroot C.coordinates F hsx (by omega) b,
        FrameCopy.parent_nonroot C.coordinates F (by omega : z ≤ C.coordinates.x) (by omega) b, hFrame]
    by_cases hNewLe : value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) ≤
        value C.toRowMountain newTop 0 (C.coordinates.parentCopy b z)
    · exact hNewLe
    · have hReverse := (Numeric.select_common_parent_depth_compare (FrameCopy.forest C.coordinates F)
        (value C.toRowMountain newTop 0) (value_pos _ _ hPositive (Nat.zero_le _))
        (value_pos _ _ hPositive (Nat.zero_le _)) hNewFrame.symm (by omega)).1
      rw [hNewForest] at hReverse
      omega

#print axioms value_copy_of_good_base_parent
#print axioms depth_zero_lt_copy_of_common_frame
#print axioms value_copy_le_of_common_frame

end OneY.LowerCopy.Context
