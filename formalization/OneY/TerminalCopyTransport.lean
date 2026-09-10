import OneY.TerminalCopyRebuild
import OneY.ActiveGeometry
import OneY.LowerCopyBlocker

/-! # Numerical transport supplied by the active finite layer -/

namespace OneY.TerminalCopy.Context

theorem value_copy_of_good_base_parent (C : Context) (top : Nat → Nat)
    {s : Nat} (hs : s < C.coordinates.x) (hNot : s ≠ C.coordinates.y)
    (hGood : ∀ p, (C.mountain.row 0).parent s = some p → p < C.coordinates.y)
    (b r : Nat) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) r
      (C.coordinates.parentCopy b s) = Reconstruction.value C.mountain top r s := by
  have hAllGood : ∀ u p, (C.mountain.row u).parent s = some p → p < C.coordinates.y := by
    intro u p hp
    have ha := C.mountain.refines_le (Nat.zero_le u) hp
    cases hzero : (C.mountain.row 0).parent s with
    | none =>
        cases ha with
        | direct h => rw [hzero] at h; contradiction
        | step _ h => rw [hzero] at h; contradiction
    | some q =>
        have hq := hGood q hzero
        rcases ZeroY.Forest.ancestor_eq_or_below_parent hzero
          (ParentForest.ancestor_to_zeroY ha) with he | hpa
        · omega
        · have hpq := ZeroY.Forest.ancestor_lt (C.mountain.row 0).parent_left hpa
          omega
  rw [Reconstruction.value_eq, Reconstruction.value_eq]
  have hh : C.toRowMountain.height (C.coordinates.parentCopy b s) = C.mountain.height s :=
    C.height_parentCopy hs b
  have ht : C.ordinaryContext.copyValue top (C.coordinates.parentCopy b s) = top s :=
    C.ordinaryContext.copyValue_parentCopy top hs b
  rw [hh, ht]
  by_cases hLive : r ≤ C.mountain.height s
  · simp only [hLive, ↓reduceIte]
    apply congrArg (fun n => top s+n)
    apply congrArg List.sum
    apply List.map_congr_left
    intro u _
    unfold Reconstruction.parentValue
    change (match C.parent u (C.coordinates.parentCopy b s) with
      | none => 0
      | some p => Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) u p) = _
    rw [C.parent_parentCopy_nonroot hs hNot b u]
    cases hp : (C.mountain.row u).parent s with
    | none => rfl
    | some p =>
        have hg := hAllGood u p hp
        simp only [Option.map_some, C.coordinates.parentCopy_good b hg]
        exact C.value_original top (by have := C.coordinates.root_lt_last; omega) u
  · simp only [hLive, ↓reduceIte]

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminalBase_fixed_of_good_parent (a : RootedRow) {K d x y s : Nat}
    (hbad : BadAt a K d x y) (hs : y < s) (hx : s < x)
    (hGood : ∀ p, (layers a K).row.forest.parent s = some p → p < y) (b : Nat) :
    (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) =
      (layers a K).row.value s := by
  let C := badAtTerminalContext a hbad
  change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row))
    0 (C.coordinates.parentCopy b s) = _
  rw [C.value_copy_of_good_base_parent (topValue (layers a K).row) hx (by change s ≠ y; omega) hGood b 0]
  exact Reconstruction.value_numeric_cell (layers a K).row (layers a K).positive 0 s

theorem badAtTerminalBase_upperFixed (a : RootedRow) {k d x y : Nat}
    (hbad : BadAt a (k+1) d x y) :
    (badAtLowerContext a hbad (Nat.lt_succ_self k)).UpperFixed
      (topValue (layers a k).row) (badAtTerminalBase a hbad).value := by
  intro s hs hx hGood b
  exact (badAtTerminalBase_fixed_of_good_parent a hbad hs hx hGood b).symm

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminalBase_fixed_of_good_parent
#print axioms OneY.Numeric.badAtTerminalBase_upperFixed
