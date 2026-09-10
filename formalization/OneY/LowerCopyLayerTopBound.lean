import OneY.LowerCopyLayerTransport
import OneY.LowerCopyTopBound
import OneY.TerminalCopyExternal

/-! # Supplying the lower pseudo-top bound from actual adjacent layers -/

namespace OneY.Numeric

theorem badAtLowerContext_pseudo_root (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) :
    (Pseudo.forest (badAtLowerContext a hbad hk).mountain).Ancestor y x := by
  have ha : (layers a (k+1)).row.forest.Ancestor y x :=
    active_parent_layer_ancestor a hbad.1 (by omega : k+1 ≤ K)
  exact ParentForest.Refines.ancestor
    (select_refines (Pseudo.forest (mountain (layers a k).row (layers a k).positive))
      (topValue (layers a k).row)) ha

theorem badAtTerminalBase_lowerTopBound (a : RootedRow) {k d x y : Nat}
    (hbad : BadAt a (k+1) d x y) :
    Reconstruction.PseudoTopBound (badAtLowerContext a hbad (Nat.lt_succ_self k)).toRowMountain
      (badAtTerminalBase a hbad).value := by
  let C := badAtLowerContext a hbad (Nat.lt_succ_self k)
  let T := badAtTerminalContext a hbad
  let Q := Pseudo.forest C.mountain
  let R := C.mountain.topForest
  have hQ : ∀ c, restrictedParent Q (layers a (k+1)).row.value c = (layers a (k+1)).row.forest.parent c := fun _ => rfl
  have hR : ∀ c, restrictedParent R (layers a (k+1)).row.value c = (layers a (k+1)).row.forest.parent c := by
    intro c
    exact (rawExtract_parent_eq_topForest (layers a k).row (layers a k).positive c).symm
  have hNewQ := badAtTerminal_restrictedParent_external a hbad Q hQ
  have hNewR := badAtTerminal_restrictedParent_external a hbad R hR
  apply C.pseudoTopBound_of_upper_selections (layers a k).row (layers a k).positive rfl
    (badAtLowerContext_pseudo_root a hbad (Nat.lt_succ_self k))
    (badAtTerminalBase a hbad).value (badAtTerminalBase_positive a hbad)
  · intro s hs hx b
    change restrictedParent (FrameCopy.forest T.coordinates Q) (badAtTerminalBase a hbad).value
      (T.coordinates.parentCopy b s) = ((layers a (k+1)).row.forest.parent s).map (T.coordinates.parentCopy b)
    rw [hNewQ]
    exact T.parent_parentCopy_nonroot hx (by change s ≠ y; change y < s at hs; omega) b 0
  · intro c
    exact (hNewQ c).trans (hNewR c).symm

theorem badAtLowerCopiedBase_lowerTopBound (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k+1 < K) (newTop : Nat → Nat)
    (hPositive : ∀ c, 0 < newTop c)
    (hPrefix : ∀ s, s < x → topValue (layers a (k+1)).row s = newTop s)
    (hFixed : (badAtLowerContext a hbad hk).UpperFixed (topValue (layers a (k+1)).row) newTop)
    (hUpper : (badAtLowerContext a hbad hk).UpperOrder (topValue (layers a (k+1)).row) newTop)
    (hBound : Reconstruction.PseudoTopBound (badAtLowerContext a hbad hk).toRowMountain newTop) :
    Reconstruction.PseudoTopBound (badAtLowerContext a hbad (by omega : k < K)).toRowMountain
      ((badAtLowerContext a hbad hk).copiedBase newTop hPositive).value := by
  let C := badAtLowerContext a hbad (by omega : k < K)
  let U := badAtLowerContext a hbad hk
  let Q := Pseudo.forest C.mountain
  let R := C.mountain.topForest
  have hQ : ∀ c, restrictedParent Q (layers a (k+1)).row.value c = (layers a (k+1)).row.forest.parent c := fun _ => rfl
  have hR : ∀ c, restrictedParent R (layers a (k+1)).row.value c = (layers a (k+1)).row.forest.parent c := by
    intro c
    exact (rawExtract_parent_eq_topForest (layers a k).row (layers a k).positive c).symm
  have hNewQ := U.restrictedParent_bottom_numeric (layers a (k+1)).row (layers a (k+1)).positive
    (layers a (k+1)).rootsOne rfl Q hQ newTop hPositive hPrefix hFixed hUpper hBound
  have hNewR := U.restrictedParent_bottom_numeric (layers a (k+1)).row (layers a (k+1)).positive
    (layers a (k+1)).rootsOne rfl R hR newTop hPositive hPrefix hFixed hUpper hBound
  apply C.pseudoTopBound_of_upper_selections (layers a k).row (layers a k).positive rfl
    (badAtLowerContext_pseudo_root a hbad (by omega : k < K))
    (U.copiedBase newTop hPositive).value (U.copiedBase_positive newTop hPositive)
  · intro s hs hx b
    change restrictedParent (FrameCopy.forest U.coordinates Q)
      (Reconstruction.value U.toRowMountain newTop 0) (U.coordinates.parentCopy b s) =
        ((layers a (k+1)).row.forest.parent s).map (U.coordinates.parentCopy b)
    rw [hNewQ]
    exact U.parent_zero_parentCopy hs (Nat.le_of_lt hx) b
  · intro c
    exact (hNewQ c).trans (hNewR c).symm

#print axioms badAtTerminalBase_lowerTopBound
#print axioms badAtLowerCopiedBase_lowerTopBound

end OneY.Numeric
