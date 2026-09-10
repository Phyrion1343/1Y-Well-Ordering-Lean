import OneY.TerminalCopyBottomRecovery

/-! # The low terminal seam lies below its deleted-last-column ghost -/

namespace OneY.NumericFrame

open Numeric ZeroY ZeroY.BMS YesMetaZFC.BMS LowerCopy.Context

theorem seam_keyLE (a : RootedRow) {K d x y z cap : Nat}
    (hbad : BadAt a K d x y) (hLow : 0 < d)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hz : y < z) (hzx : z < x)
    (hParent : (layers a K).row.forest.parent x = (layers a K).row.forest.parent z)
    (hKey : KeyLEFrom (badAtTerminalContext a hbad).mountain (topValue (layers a K).row) 1 x z)
    (b : Nat) :
    KeyLEFrom (badAtTerminalContext a hbad).toRowMountain
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) 1
      ((badAtTerminalContext a hbad).coordinates.encode x b)
      ((badAtTerminalContext a hbad).coordinates.parentCopy b z) := by
  let C := badAtTerminalContext a hbad
  let E := badAtContext a hbad (hcap x (Nat.lt_succ_self x))
  let A := matrix (layers a K).row (x+1) cap
  let top := C.ordinaryContext.copyValue (topValue (layers a K).row)
  have hcopy : BMS.copyColumn E b z = C.coordinates.parentCopy b z := rfl
  have hseam : E.copyPosition (b+1) 0 = C.coordinates.encode x b := by
    change y+(b+1)*(x-y)+0 = x+b*(x-y)
    have ht := C.root_copy_succ_eq b
    change y+(b+1)*(x-y) = x+b*(x-y) at ht
    omega
  have hnewx : C.coordinates.encode x b < (A.expand (b+1)).raw.length := by
    rw [← hseam]
    exact E.copyPosition_lt_length (Nat.le_refl _) E.blockLength_pos
  have hnewz : C.coordinates.parentCopy b z < (A.expand (b+1)).raw.length := by
    rw [← hcopy, BMS.copyColumn_bad E b (by change y ≤ z; omega)]
    exact E.copyPosition_lt_length (by omega) (by change z-y < x-y; omega)
  apply (DecoratedColumn.keyLEFrom_iff_columns C.toRowMountain top (A.expand (b+1)).raw
    ((x+1)+1) 1 _ _ (fun r => expanded_entry a hbad hcap hnewx r)
    (fun r => expanded_entry a hbad hcap hnewz r)).mpr
  have hOld := (DecoratedColumn.keyLEFrom_iff_columns C.mountain (topValue (layers a K).row)
    A.raw ((x+1)+1) 1 x z
    (fun r => original_entry a hbad hcap (Nat.lt_succ_self x) r)
    (fun r => original_entry a hbad hcap (by omega) r)).mp hKey
  have hPrevious : previousParent A.raw (((x+1)+1)+1) x = previousParent A.raw (((x+1)+1)+1) z := by
    change parent ((x+1)+1) A.raw x = parent ((x+1)+1) A.raw z
    have hpX := matrix_numeric_parent_all (layers a K).row (hcap x (Nat.lt_succ_self x)) (Nat.lt_succ_self x) 0
    have hpZ := matrix_numeric_parent_all (width := x+1) (layers a K).row (hcap z (by omega)) (by omega) 0
    simpa only [Nat.add_zero] using hpX.trans (hParent.trans hpZ.symm)
  have hLift := DecoratedColumn.lifted_le E (matrix_depthRegular _ _ _)
    (by change x < (matrix _ (x+1) cap).raw.length; rw [matrix_length]; omega)
    (by change z < (matrix _ (x+1) cap).raw.length; rw [matrix_length]; omega)
    E.parentColumn_lt_lastIndex hz hPrevious hOld b
  have hStrict := DecoratedColumn.strict_of_lt_of_le (a := top (E.copyPosition (b+1) 0))
    (newroot_suffix_lt_ghost E (index := b+1) (Nat.le_refl _)
      (by change (x+1)+1 < (x+1)+1+d; omega)) hLift
  have htcopy : top (C.coordinates.parentCopy b z) = topValue (layers a K).row z :=
    C.ordinaryContext.copyValue_parentCopy _ hzx b
  rw [htcopy, ← hcopy, ← hseam]
  exact DecoratedColumn.congr (ColumnEq.refl _)
    (suffix_copyColumn_eq_lifted E (by omega) hzx (by change y ≤ z; omega) (((x+1)+1)+1)) hStrict

end OneY.NumericFrame

namespace OneY.Numeric

theorem badAtTerminalBase_seam_order (a : RootedRow) {K d x y z p : Nat}
    (hbad : BadAt a K d x y) (hLow : 0 < d) (hz : y < z) (hzx : z < x)
    (hP : (layers a K).row.forest.parent x = some p)
    (hZP : (layers a K).row.forest.parent z = some p)
    (hLe : (layers a K).row.value x ≤ (layers a K).row.value z) (b : Nat) :
    (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.encode x b) ≤
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b z) := by
  let C := badAtTerminalContext a hbad
  let oldTop := topValue (layers a K).row
  let newTop := C.ordinaryContext.copyValue oldTop
  have hP0 : (C.mountain.row 0).parent x = some p := hP
  have hZP0 : (C.mountain.row 0).parent z = some p := hZP
  have hv0 (q : Nat) : Reconstruction.value C.mountain oldTop 0 q = (layers a K).row.value q :=
    Reconstruction.value_numeric_base (layers a K).row (layers a K).positive q
  have hOldLe : Reconstruction.value C.mountain oldTop 0 x ≤ Reconstruction.value C.mountain oldTop 0 z := by
    rw [hv0, hv0]; exact hLe
  have hOldNext : Reconstruction.value C.mountain oldTop 1 x ≤ Reconstruction.value C.mountain oldTop 1 z := by
    rw [Reconstruction.value_recurrence C.mountain oldTop hP0,
      Reconstruction.value_recurrence C.mountain oldTop hZP0] at hOldLe
    exact Nat.le_of_add_le_add_right hOldLe
  have hOldKey := (Reconstruction.keyLEFrom_iff_value_le C.mountain oldTop
    (fun q => topValue_pos (layers a K).row ((layers a K).positive q)) 0
    (fun r _ q => Reconstruction.restrictedParent_numeric_reconstruction (layers a K).row (layers a K).positive r q)
    (C.mountain.parent_source hP0) (C.mountain.parent_source hZP0) (hP0.trans hZP0.symm)).mpr hOldNext
  obtain ⟨cap, hCap⟩ := exists_value_cap (layers a K).row.value x
  have hNewKey := NumericFrame.seam_keyLE a hbad hLow (fun q hq => hCap q (by omega))
    hz hzx (hP.trans hZP.symm) hOldKey b
  have hNewP : C.parent 0 (C.coordinates.encode x b) = some (C.coordinates.parentCopy b p) := by
    have he := C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hLow b
    change C.parent 0 (C.coordinates.encode x b) = ((C.mountain.row 0).parent x).map _ at he
    rw [he, hP0, Option.map_some]
  have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_parentCopy_nonroot hzx (by change z ≠ y; omega) b 0, hZP0, Option.map_some]
  have hNewNext := (Reconstruction.keyLEFrom_iff_value_le C.toRowMountain newTop
    (fun _q => topValue_pos (layers a K).row ((layers a K).positive _)) 0
    (fun r _ q => badAtTerminal_restrictedParent a hbad r q)
    (C.toRowMountain.parent_source hNewP) (C.toRowMountain.parent_source hNewZP)
    (hNewP.trans hNewZP.symm)).mp hNewKey
  change Reconstruction.value C.toRowMountain newTop 0 _ ≤ Reconstruction.value C.toRowMountain newTop 0 _
  rw [Reconstruction.value_recurrence C.toRowMountain newTop hNewP,
    Reconstruction.value_recurrence C.toRowMountain newTop hNewZP]
  exact Nat.add_le_add_right hNewNext _

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminalBase_seam_order
