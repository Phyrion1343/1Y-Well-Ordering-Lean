import OneY.LowerCopyCanonical
import OneY.FrameCopy

/-! # The actual inherited candidate forest at the lower copied bottom row -/

namespace OneY.LowerCopy.Context

open Reconstruction

theorem root_ancestor_last_zero (C : Context) :
    (C.mountain.row 0).Ancestor C.coordinates.y C.coordinates.x := by
  have ha : (C.mountain.row C.floor).Ancestor C.coordinates.y C.coordinates.x := by
    rcases (C.mountain.rootAt_eq_iff_path (r := C.floor) (q := C.coordinates.y)
      (c := C.coordinates.x) rfl).mp C.last_root with ha | he
    · exact ha
    · have := C.coordinates.root_lt_last; omega
  exact ParentForest.Refines.ancestor (C.mountain.refines_le (Nat.zero_le _)) ha

theorem parent_zero_encode (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.parent 0 (C.coordinates.encode s b) =
      ((C.mountain.row 0).parent s).map (C.coordinates.parentCopy b) := by
  rw [C.parent_encode hs hx b 0]
  split
  · rename_i hMove
    have hh : C.floor = 0 := by omega
    simp only [hh, Nat.zero_sub, ite_self]
    cases hp : (C.mountain.row 0).parent s with
    | none => rfl
    | some p =>
        have hConeP := C.high_parent_inCone hMove.1 (by omega) hp
        simp only [Option.map_some, C.coordinates.parentCopy_bad b (C.root_le_of_inCone hConeP)]
  · rfl

theorem zero_forest_eq_frameCopy (C : Context) :
    C.row 0 = FrameCopy.forest C.coordinates (C.mountain.row 0) := by
  apply Numeric.parentForest_eq_of_parent_eq
  intro c
  change C.parent 0 c = FrameCopy.parent C.coordinates (C.mountain.row 0) c
  by_cases hc : c ≤ C.coordinates.x
  · rw [C.parent_original hc, FrameCopy.parent_original C.coordinates (C.mountain.row 0) hc]
  · have hs := C.coordinates.source_bounds c
    have he := C.coordinates.encode_coordinates (by have := C.coordinates.root_lt_last; omega : C.coordinates.y < c)
    rw [← he, C.parent_zero_encode hs.1 hs.2,
      FrameCopy.parent_encode C.coordinates (C.mountain.row 0) hs.1 hs.2]

theorem parent_zero_parentCopy (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.parent 0 (C.coordinates.parentCopy b s) =
      ((C.mountain.row 0).parent s).map (C.coordinates.parentCopy b) := by
  rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
  exact C.parent_zero_encode hs hx b

theorem root_ancestor_inherited (C : Context) (F : ParentForest)
    (hRefines : (C.mountain.row 0).Refines F) : F.Ancestor C.coordinates.y C.coordinates.x :=
  ParentForest.Refines.ancestor hRefines C.root_ancestor_last_zero

theorem zero_refines_frameCopy (C : Context) (F : ParentForest)
    (hRefines : (C.mountain.row 0).Refines F) :
    (C.row 0).Refines (FrameCopy.forest C.coordinates F) := by
  intro c p hp
  change C.parent 0 c = some p at hp
  by_cases hc : c ≤ C.coordinates.x
  · rw [C.parent_original hc] at hp
    exact FrameCopy.prefix_ancestor C.coordinates F (hRefines hp) hc
  · have hAfter : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have hs := C.coordinates.source_bounds c
    have he := C.coordinates.encode_coordinates hAfter
    rw [← he, C.parent_zero_encode hs.1 hs.2] at hp
    cases hOld : (C.mountain.row 0).parent (C.coordinates.source c) with
    | none => simp only [hOld, Option.map_none] at hp; contradiction
    | some q =>
        simp only [hOld, Option.map_some] at hp
        have ht := FrameCopy.ancestor_copy C.coordinates F (C.root_ancestor_inherited F hRefines)
          (hRefines hOld) hs.2 (C.coordinates.block c)
        rw [C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)] at ht
        change (FrameCopy.forest C.coordinates F).Ancestor _ (C.coordinates.encode _ _) at ht
        rw [he, Option.some.inj hp] at ht
        exact ht

theorem keyLE_bottom_parent (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hUpper : C.UpperOrder oldTop newTop) {c z p : Nat}
    (hz : C.coordinates.y < z) (hzc : z < c) (hcx : c ≤ C.coordinates.x)
    (hC : (C.mountain.row 0).parent c = some p) (hZ : (C.mountain.row 0).parent z = some p)
    (hKey : KeyLEFrom C.mountain oldTop 1 c z) (b : Nat) :
    KeyLEFrom C.toRowMountain newTop 1 (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z) := by
  have hcLive := C.mountain.parent_source hC
  have hzLive := C.mountain.parent_source hZ
  have hInitial := hC.trans hZ.symm
  by_cases hFloor : 0 < C.floor
  · exact C.keyLE_low_start hRegular oldTop newTop hUpper hz hzc hcx hcLive hzLive hFloor hInitial hKey b
  · have he : C.floor = 0 := by omega
    have ht := C.keyLE_floor_start hRegular oldTop newTop hUpper hz hzc hcx
      (by simpa only [he] using hcLive) (by simpa only [he] using hzLive)
      (by simpa only [he] using hInitial) (by simpa only [he] using hKey) b
    simpa only [he] using ht

#print axioms zero_forest_eq_frameCopy
#print axioms zero_refines_frameCopy
#print axioms keyLE_bottom_parent

end OneY.LowerCopy.Context
