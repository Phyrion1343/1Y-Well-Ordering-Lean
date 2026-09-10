import OneY.TerminalCopyDepths

/-! # The active layer supplies the inherited-frame comparison B -/

namespace OneY.TerminalCopy.Context

theorem depth_zero_lt_copy_of_common_frame (C : Context) (hLow : 0 < C.level)
    (F : ParentForest)
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
  by_cases hAS : (C.mountain.row 0).Ancestor C.coordinates.y s
  · rw [C.depth_low_of_root_ancestor hx (Or.inr hAS) hLow b,
      C.depth_low_of_root_ancestor hzx (Or.inr (hMono hAS)) hLow b]
    omega
  · rw [C.depth_low_of_no_root_ancestor hx (by omega) hAS hLow b]
    by_cases hAZ : (C.mountain.row 0).Ancestor C.coordinates.y z
    · rw [C.depth_low_of_root_ancestor hzx (Or.inr hAZ) hLow b]
      omega
    · rw [C.depth_low_of_no_root_ancestor hzx (by omega) hAZ hLow b]
      exact hDepth

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminalBase_order_of_common_frame (a : RootedRow) {K d x y s z : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (hz : y < z) (hZS : z < s) (hsx : s ≤ x)
    (hFrame : F.parent s = F.parent z)
    (hLe : (layers a K).row.value s ≤ (layers a K).row.value z) (b : Nat) :
    (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) ≤
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b z) := by
  let C := badAtTerminalContext a hbad
  by_cases hZero : d = 0
  · subst d
    change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 _ ≤
      Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 _
    rw [C.value_above _ (show C.level ≤ 0 from Nat.le_refl 0),
      C.value_above _ (show C.level ≤ 0 from Nat.le_refl 0)]
    have hSource (q : Nat) (hq : q < x) :
        C.ordinaryContext.source0 (C.coordinates.parentCopy b q) = q :=
      C.ordinaryContext.source0_parentCopy hq b
    have hValue (q : Nat) : Reconstruction.value C.mountain (topValue (layers a K).row) 0 q =
        (layers a K).row.value q :=
      Reconstruction.value_numeric_base (layers a K).row (layers a K).positive q
    rw [hSource z (by omega)]
    by_cases hslt : s < x
    · rw [hSource s hslt, hValue, hValue]
      exact hLe
    · have he : s = x := by omega
      subst s
      rw [C.coordinates.parentCopy_bad b (by change y ≤ x; omega)]
      change Reconstruction.value C.mountain (topValue (layers a K).row) 0
        (C.ordinaryContext.source0 (C.coordinates.encode x b)) ≤ _
      have hSeam : C.ordinaryContext.source0 (C.coordinates.encode x b) = y := C.ordinary_source_seam b
      rw [hSeam, hValue, hValue]
      have hp : (layers a K).row.forest.parent x = some y := hbad.1
      exact Nat.le_trans (Nat.le_of_lt ((layers a K).row.parent_values hp).2) hLe
  · have hLow : 0 < C.level := by change 0 < d; omega
    have hSelected' : ∀ i, restrictedParent F (layers a K).row.value i = (C.mountain.row 0).parent i := hSelected
    have hOldForest : (select F (layers a K).row.value).forest = C.mountain.row 0 :=
      parentForest_eq_of_parent_eq _ _ hSelected'
    have hCompare := select_common_parent_depth_compare F (layers a K).row.value
      ((layers a K).positive s) ((layers a K).positive z) hFrame hLe
    rw [hOldForest] at hCompare
    by_cases hEq : (C.mountain.row 0).depth s = (C.mountain.row 0).depth z
    · have hParent : (C.mountain.row 0).parent s = (C.mountain.row 0).parent z := by
        simpa only [hSelected'] using hCompare.2 hEq
      cases hp : (C.mountain.row 0).parent s with
      | none =>
          have hS : C.parent 0 (C.coordinates.parentCopy b s) = none := by
            rw [C.parent_low_parentCopy hLow hsx (by change s ≠ y; omega) b, hp, Option.map_none]
          have hZ : C.parent 0 (C.coordinates.parentCopy b z) = none := by
            rw [C.parent_low_parentCopy hLow (by change z ≤ x; omega) (by change z ≠ y; omega) b,
              hParent.symm.trans hp, Option.map_none]
          rw [badAtTerminalBase_none_eq_one a hbad hS, badAtTerminalBase_none_eq_one a hbad hZ]
          exact Nat.le_refl _
      | some p =>
          by_cases hslt : s < x
          · exact badAtTerminalBase_order_of_common_parent a hbad (by omega) hslt hz (by omega)
              hp (hParent.symm.trans hp) hLe b
          · have he : s = x := by omega
            subst s
            rw [C.coordinates.parentCopy_bad b (by change y ≤ x; omega)]
            exact badAtTerminalBase_seam_order a hbad hLow hz (by omega) hp (hParent.symm.trans hp) hLe b
    · have hDepth : (C.mountain.row 0).depth s < (C.mountain.row 0).depth z := by omega
      have hNS : ∀ i, ZeroY.Forest.nearestSmaller F.parent (C.mountain.row 0).depth i = (C.mountain.row 0).parent i := by
        intro i
        rw [← hOldForest]
        exact select_depth_nearestSmaller F (layers a K).row.value
          (fun c hc => by have := (layers a K).positive c; omega) i
      have hNewDepth := C.depth_zero_lt_copy_of_common_frame hLow F hNS
        (by change y < s; omega) hsx hz (by change z ≤ x; omega) hFrame hDepth b
      have hNewForest : (select (FrameCopy.forest C.coordinates F) (badAtTerminalBase a hbad).value).forest = C.row 0 :=
        parentForest_eq_of_parent_eq _ _ (badAtTerminal_restrictedParent_external a hbad F hSelected)
      have hNewFrame : (FrameCopy.forest C.coordinates F).parent (C.coordinates.parentCopy b s) =
          (FrameCopy.forest C.coordinates F).parent (C.coordinates.parentCopy b z) := by
        change FrameCopy.parent _ _ _ = FrameCopy.parent _ _ _
        rw [FrameCopy.parent_nonroot C.coordinates F hsx (by change s ≠ y; omega) b,
          FrameCopy.parent_nonroot C.coordinates F (by change z ≤ x; omega) (by change z ≠ y; omega) b, hFrame]
      by_cases hNewLe : (badAtTerminalBase a hbad).value (C.coordinates.parentCopy b s) ≤
          (badAtTerminalBase a hbad).value (C.coordinates.parentCopy b z)
      · exact hNewLe
      · have hReverse := (select_common_parent_depth_compare (FrameCopy.forest C.coordinates F)
          (badAtTerminalBase a hbad).value (badAtTerminalBase_positive a hbad _)
          (badAtTerminalBase_positive a hbad _) hNewFrame.symm (by omega)).1
        rw [hNewForest] at hReverse
        omega

theorem badAtTerminalBase_upperOrder (a : RootedRow) {k d x y : Nat}
    (hbad : BadAt a (k+1) d x y) :
    (badAtLowerContext a hbad (Nat.lt_succ_self k)).UpperOrder
      (topValue (layers a k).row) (badAtTerminalBase a hbad).value := by
  intro z s hz hZS hsx hFrame hLe b
  exact badAtTerminalBase_order_of_common_frame a hbad
    (Pseudo.forest (mountain (layers a k).row (layers a k).positive))
    (fun _ => rfl) hz hZS hsx hFrame hLe b

end OneY.Numeric

#print axioms OneY.TerminalCopy.Context.depth_zero_lt_copy_of_common_frame
#print axioms OneY.Numeric.badAtTerminalBase_order_of_common_frame
#print axioms OneY.Numeric.badAtTerminalBase_upperOrder
