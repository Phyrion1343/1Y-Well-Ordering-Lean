import OneY.TerminalCopyTransport
import OneY.FrameCopy

/-! # The external inherited candidate forest of the active bottom row -/

namespace OneY.TerminalCopy.Context

theorem root_ancestor_inherited (C : Context) (F : ParentForest)
    (hRefines : (C.mountain.row 0).Refines F) : F.Ancestor C.coordinates.y C.coordinates.x :=
  ParentForest.Refines.ancestor hRefines (C.root_ancestor_last (Nat.zero_le _))

theorem zero_refines_frameCopy (C : Context) (F : ParentForest)
    (hRefines : (C.mountain.row 0).Refines F) :
    (C.row 0).Refines (FrameCopy.forest C.coordinates F) := by
  intro c p hp
  change C.parent 0 c = some p at hp
  have hRoot := C.root_ancestor_inherited F hRefines
  by_cases hc : c < C.coordinates.x
  · rw [C.parent_original hc 0] at hp
    exact FrameCopy.prefix_ancestor C.coordinates F (hRefines hp) (Nat.le_of_lt hc)
  · have hs := C.coordinates.source_bounds c
    have he := C.coordinates.encode_coordinates (by have := C.coordinates.root_lt_last; omega : C.coordinates.y < c)
    rw [← he, C.parent_encode hs.1 hs.2 _ 0] at hp
    split at hp
    · rename_i hCritical
      have ha := (hRefines hp).trans hRoot
      have ht := FrameCopy.ancestor_copy C.coordinates F hRoot ha (Nat.le_refl C.coordinates.x)
        (C.coordinates.block c)
      have hpGood := (C.mountain.row 0).parent_left hp
      rw [C.coordinates.parentCopy_good _ hpGood,
        C.coordinates.parentCopy_bad _ (Nat.le_of_lt C.coordinates.root_lt_last)] at ht
      change (FrameCopy.forest C.coordinates F).Ancestor p (C.coordinates.encode C.coordinates.x _) at ht
      rw [← hCritical.1, he] at ht
      exact ht
    · obtain ⟨q, hq, hEq⟩ := Option.map_eq_some_iff.mp hp
      have ht := FrameCopy.ancestor_copy C.coordinates F hRoot (hRefines hq) hs.2 (C.coordinates.block c)
      rw [hEq, C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)] at ht
      change (FrameCopy.forest C.coordinates F).Ancestor p (C.coordinates.encode _ _) at ht
      rw [he] at ht
      exact ht

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_bottom_refines (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c) :
    ((badAtTerminalContext a hbad).mountain.row 0).Refines F := by
  intro c p hp
  exact ParentForest.ancestor_of_zeroY (restrictedParent_spec F _ ((hSelected c).trans hp)).1

theorem badAtTerminalBase_order_of_common_parent (a : RootedRow) {K d x y s z p : Nat}
    (hbad : BadAt a K d x y) (hs : y < s) (hx : s < x) (hz : y < z) (hzx : z < x)
    (hP : (layers a K).row.forest.parent s = some p)
    (hZP : (layers a K).row.forest.parent z = some p)
    (hLe : (layers a K).row.value s ≤ (layers a K).row.value z) (b : Nat) :
    (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) ≤
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b z) := by
  let C := badAtTerminalContext a hbad
  let oldTop := topValue (layers a K).row
  let newTop := C.ordinaryContext.copyValue oldTop
  have hP0 : (C.mountain.row 0).parent s = some p := hP
  have hZP0 : (C.mountain.row 0).parent z = some p := hZP
  have hv0 (q : Nat) : Reconstruction.value C.mountain oldTop 0 q = (layers a K).row.value q :=
    Reconstruction.value_numeric_base (layers a K).row (layers a K).positive q
  have hOldLe : Reconstruction.value C.mountain oldTop 0 s ≤ Reconstruction.value C.mountain oldTop 0 z := by
    rw [hv0, hv0]
    exact hLe
  have hOldNext : Reconstruction.value C.mountain oldTop 1 s ≤ Reconstruction.value C.mountain oldTop 1 z := by
    rw [Reconstruction.value_recurrence C.mountain oldTop hP0,
      Reconstruction.value_recurrence C.mountain oldTop hZP0] at hOldLe
    exact Nat.le_of_add_le_add_right hOldLe
  have hOldKey := (Reconstruction.keyLEFrom_iff_value_le C.mountain oldTop
    (fun q => topValue_pos (layers a K).row ((layers a K).positive q)) 0
    (fun r _ q => Reconstruction.restrictedParent_numeric_reconstruction (layers a K).row (layers a K).positive r q)
    (C.mountain.parent_source hP) (C.mountain.parent_source hZP) (hP.trans hZP.symm)).mpr hOldNext
  obtain ⟨cap, hCap⟩ := exists_value_cap (layers a K).row.value x
  have hNewKey := NumericFrame.copied_keyLE (u := 0) a hbad
    (fun q hq => hCap q (by omega)) hs hx hz hzx (hP.trans hZP.symm) hOldKey b
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_parentCopy_nonroot hx (by change s ≠ y; omega) b 0, hP0, Option.map_some]
  have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_parentCopy_nonroot hzx (by change z ≠ y; omega) b 0, hZP0, Option.map_some]
  have hNewNext := (Reconstruction.keyLEFrom_iff_value_le C.toRowMountain newTop
    (fun q => topValue_pos (layers a K).row ((layers a K).positive _)) 0
    (fun r _ q => badAtTerminal_restrictedParent a hbad r q)
    (C.toRowMountain.parent_source hNewP) (C.toRowMountain.parent_source hNewZP)
    (hNewP.trans hNewZP.symm)).mp hNewKey
  change Reconstruction.value C.toRowMountain newTop 0 _ ≤ Reconstruction.value C.toRowMountain newTop 0 _
  rw [Reconstruction.value_recurrence C.toRowMountain newTop hNewP,
    Reconstruction.value_recurrence C.toRowMountain newTop hNewZP]
  exact Nat.add_le_add_right hNewNext _

end OneY.Numeric

#print axioms OneY.TerminalCopy.Context.zero_refines_frameCopy
#print axioms OneY.Numeric.badAtTerminalBase_order_of_common_parent
