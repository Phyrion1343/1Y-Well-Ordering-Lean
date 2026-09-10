import OneY.TerminalCopyRoots
import OneY.PseudoSelection

/-!
# The contracted extraction forest above an active finite copy

The actual computed component roots already give the ordinary copied top
forest. Selecting copied top values in that contracted forest therefore
gives the ordinary copy of the next numerical layer. This statement is
independent of low-row numerical reconstruction. Identifying the uncontracted
pseudo selection additionally requires its equal-height antitonicity.
-/

namespace OneY.TerminalCopy.Context

theorem restrictedParent_topForest (C : Context) (top : Nat → Nat) (c : Nat) :
    Numeric.restrictedParent C.toRowMountain.topForest
      (C.ordinaryContext.copyValue top) c =
      (Numeric.restrictedParent C.mountain.topForest top
        (C.ordinaryContext.source0 c)).map
          (C.coordinates.parentCopy (C.ordinaryContext.block0 c)) := by
  exact C.ordinaryContext.restrictedParent_of_forest_copy
    (fun q => C.topForest_parent_formula q) top c

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_topForest_select (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    select (badAtTerminalContext a hbad).toRowMountain.topForest
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue
        (topValue (layers a K).row)) =
      ordinaryCopiedBase (rawExtract (layers a K).row (layers a K).positive)
        (rawExtract_positive (layers a K).row (layers a K).positive)
        (badAtTerminalContext a hbad).coordinates := by
  let C := badAtTerminalContext a hbad
  apply Row.ext_values_parents
  · rfl
  · funext c
    change restrictedParent C.toRowMountain.topForest
      (C.ordinaryContext.copyValue (topValue (layers a K).row)) c = _
    rw [C.restrictedParent_topForest]
    have hp := rawExtract_parent_eq_topForest (layers a K).row (layers a K).positive
      (C.ordinaryContext.source0 c)
    change (rawExtract (layers a K).row (layers a K).positive).forest.parent
      (C.ordinaryContext.source0 c) =
        restrictedParent C.mountain.topForest (topValue (layers a K).row)
          (C.ordinaryContext.source0 c) at hp
    rw [← hp]
    rfl

end OneY.Numeric

#print axioms OneY.TerminalCopy.Context.restrictedParent_topForest
#print axioms OneY.Numeric.badAtTerminal_topForest_select
