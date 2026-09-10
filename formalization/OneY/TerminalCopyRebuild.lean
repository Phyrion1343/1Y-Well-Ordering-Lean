import OneY.TerminalCopyComplete
import OneY.TerminalCopyExtraction

/-! # Rebuilding the active mountain and its extracted upper layer

The rebuilt base has the specified copied bottom forest. All higher
parents, actual heights, actual tops and the next extraction are computed
and proved equal to the diagram. Selection of that bottom forest in an
external candidate forest is a separate interface.
-/

namespace OneY.Numeric

def badAtTerminalBase (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) : Row :=
  Reconstruction.numericRow (badAtTerminalContext a hbad).toRowMountain
    ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
    (fun _c => topValue_pos (layers a K).row ((layers a K).positive _)) 0

theorem badAtTerminalBase_positive (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (c : Nat) : 0 < (badAtTerminalBase a hbad).value c :=
  Reconstruction.value_pos _ _
    (fun _q => topValue_pos (layers a K).row ((layers a K).positive _)) (Nat.zero_le _)

theorem badAtTerminalBase_rows (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (r : Nat) :
    rows (badAtTerminalBase a hbad) r =
      Reconstruction.numericRow (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (fun _c => topValue_pos (layers a K).row ((layers a K).positive _)) r := by
  let C := badAtTerminalContext a hbad
  simpa only [Nat.zero_add, badAtTerminalBase, C] using Reconstruction.numericRow_rows C.toRowMountain
    (C.ordinaryContext.copyValue (topValue (layers a K).row))
    (fun _q => topValue_pos (layers a K).row ((layers a K).positive _)) 0
    (fun u _ q => badAtTerminal_restrictedParent a hbad u q) r

theorem badAtTerminalBase_height (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (c : Nat) :
    height (badAtTerminalBase a hbad) c = (badAtTerminalContext a hbad).height c := by
  let base := badAtTerminalBase a hbad
  let C := badAtTerminalContext a hbad
  have hlive : ∀ r, 0 < (rows base r).value c ↔ r ≤ C.height c := by
    intro r
    rw [badAtTerminalBase_rows]
    exact Reconstruction.value_pos_iff _ _
      (fun q => topValue_pos (layers a K).row ((layers a K).positive _)) r c
  apply Nat.le_antisymm
  · exact (hlive (height base c)).mp (height_live base (badAtTerminalBase_positive a hbad c))
  · exact (live_iff_le_height base (badAtTerminalBase_positive a hbad c) _).mp
      ((hlive _).mpr (Nat.le_refl _))

theorem badAtTerminalBase_topValue (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (c : Nat) :
    topValue (badAtTerminalBase a hbad) c =
      (badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row) c :=
  Reconstruction.numericRow_topValue _ _ _ 0
    (fun u _ q => badAtTerminal_restrictedParent a hbad u q) (Nat.zero_le _)

theorem badAtTerminalBase_mountain (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    mountain (badAtTerminalBase a hbad) (badAtTerminalBase_positive a hbad) =
      (badAtTerminalContext a hbad).toRowMountain := by
  apply RootGeometry.RowMountain.ext_height_parents
  · funext c
    exact badAtTerminalBase_height a hbad c
  · intro r
    funext c
    change (rows (badAtTerminalBase a hbad) r).forest.parent c = _
    rw [badAtTerminalBase_rows]
    rfl

theorem badAtTerminalBase_rawExtract (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    rawExtract (badAtTerminalBase a hbad) (badAtTerminalBase_positive a hbad) =
      ordinaryCopiedBase (rawExtract (layers a K).row (layers a K).positive)
        (rawExtract_positive (layers a K).row (layers a K).positive)
        (badAtTerminalContext a hbad).coordinates := by
  have hTop : topValue (badAtTerminalBase a hbad) =
      (badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row) :=
    funext (badAtTerminalBase_topValue a hbad)
  have hSel := badAtTerminal_topForest_select a hbad
  apply Row.ext_values_parents
  · exact hTop
  · funext c
    rw [rawExtract_parent_eq_topForest, badAtTerminalBase_mountain, hTop]
    exact congrArg (fun row : Row => row.forest.parent c) hSel

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminalBase_mountain
#print axioms OneY.Numeric.badAtTerminalBase_rawExtract
