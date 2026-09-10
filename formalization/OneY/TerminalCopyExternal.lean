import OneY.TerminalCopyExternalSeam

/-! # Complete active-bottom recovery in its actual inherited frame -/

namespace OneY.Numeric

theorem badAtTerminal_restrictedParent_external (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (c : Nat) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value c = (badAtTerminalContext a hbad).parent 0 c := by
  let C := badAtTerminalContext a hbad
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases hc : c < x
      · exact badAtTerminal_external_prefix a hbad F hSelected hc
      · have hs := C.coordinates.source_bounds c
        change y < C.coordinates.source c ∧ C.coordinates.source c ≤ x at hs
        have hAfter : C.coordinates.y < c := by
          change y < c
          have := C.coordinates.root_lt_last
          change y < x at this
          omega
        have he := C.coordinates.encode_coordinates hAfter
        by_cases hSeam : C.coordinates.source c = x
        · rw [hSeam] at he
          have hPrefix : ∀ i, i < C.coordinates.encode x (C.coordinates.block c) →
              restrictedParent (FrameCopy.forest C.coordinates F) (badAtTerminalBase a hbad).value i = C.parent 0 i := by
            intro i hi
            rw [he] at hi
            exact ih i hi
          rw [← he]
          by_cases hZero : d = 0
          · subst d
            exact badAtTerminal_external_seam_zero a hbad F hSelected (C.coordinates.block c) hPrefix
          · exact badAtTerminal_external_seam_low a hbad (by omega) F hSelected (C.coordinates.block c) hPrefix
        · have hSource : C.coordinates.source c < x := by omega
          have hCopy : C.coordinates.parentCopy (C.coordinates.block c) (C.coordinates.source c) = c := by
            rw [C.coordinates.parentCopy_bad _ (by change y ≤ C.coordinates.source c; omega)]
            exact he
          have hPrefix : ∀ i, i < C.coordinates.parentCopy (C.coordinates.block c) (C.coordinates.source c) →
              restrictedParent (FrameCopy.forest C.coordinates F) (badAtTerminalBase a hbad).value i = C.parent 0 i := by
            intro i hi
            rw [hCopy] at hi
            exact ih i hi
          rw [← hCopy]
          exact badAtTerminal_external_nonroot a hbad F hSelected hs.1 hSource (C.coordinates.block c) hPrefix

theorem badAtTerminalBase_select_external (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c) :
    select (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value = badAtTerminalBase a hbad := by
  apply Row.ext_values_parents
  · rfl
  · funext c
    exact badAtTerminal_restrictedParent_external a hbad F hSelected c

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminal_restrictedParent_external
#print axioms OneY.Numeric.badAtTerminalBase_select_external
