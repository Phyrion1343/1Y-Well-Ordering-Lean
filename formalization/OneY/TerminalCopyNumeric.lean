import OneY.BadRoot
import OneY.TerminalCopyNesting

/-! # The active copy context computed from an actual numerical bad root -/

namespace OneY.Numeric

def badAtTerminalContext (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : TerminalCopy.Context where
  mountain := mountain (layers a K).row (layers a K).positive
  coordinates := ⟨y, x, (rows (layers a K).row d).forest.parent_left hbad.1⟩
  level := d
  last_parent := hbad.1
  last_height := (badAt_height_and_top hbad).1

def badAtTerminalMountain (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : RootGeometry.RowMountain :=
  (badAtTerminalContext a hbad).toRowMountain

theorem badAtTerminal_seam_height (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (b : Nat) :
    (badAtTerminalContext a hbad).height (x+b*(x-y)) = height (layers a K).row y := by
  let C := badAtTerminalContext a hbad
  have h := C.height_encode C.coordinates.root_lt_last (Nat.le_refl _) b
  rw [if_pos rfl] at h
  exact h

theorem badAtTerminal_seam_parent_below (a : RootedRow) {K d x y r : Nat}
    (hbad : BadAt a K d x y) (hr : r < d) (b : Nat) :
    (badAtTerminalContext a hbad).parent r (x+b*(x-y)) =
      ((rows (layers a K).row r).forest.parent x).map
        ((badAtTerminalContext a hbad).coordinates.parentCopy b) := by
  let C := badAtTerminalContext a hbad
  exact C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr b

theorem badAtTerminal_seam_parent_above (a : RootedRow) {K d x y r : Nat}
    (hbad : BadAt a K d x y) (hr : d ≤ r) (b : Nat) :
    (badAtTerminalContext a hbad).parent r (x+b*(x-y)) =
      (rows (layers a K).row r).forest.parent y := by
  let C := badAtTerminalContext a hbad
  have h := C.parent_encode C.coordinates.root_lt_last (Nat.le_refl _) b r
  rw [if_pos (show C.coordinates.x = C.coordinates.x ∧ C.level ≤ r from ⟨rfl, hr⟩)] at h
  exact h

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminalContext
#print axioms OneY.Numeric.badAtTerminalMountain
#print axioms OneY.Numeric.badAtTerminal_seam_parent_above
