import OneY.TerminalCopyUpperOrder

/-! # The initial linear candidate forest survives every block copy -/

namespace OneY.FrameCopy

theorem linear_parent (C : CopyCoordinates.Context) (c : Nat) :
    parent C Numeric.linearForest c = ZeroY.linearParent c := by
  by_cases hc : c ≤ C.x
  · exact parent_original C Numeric.linearForest hc
  · have hs := C.source_bounds c
    have hcp : C.y < c := by have := C.root_lt_last; omega
    have he := C.encode_coordinates hcp
    have hSource : 0 < C.source c := by omega
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hSource)
    rw [← he, parent_encode C Numeric.linearForest hs.1 hs.2, hq]
    change (some q).map (C.parentCopy (C.block c)) = ZeroY.linearParent (C.encode (q+1) (C.block c))
    have hGood : C.y ≤ q := by omega
    rw [Option.map_some, C.parentCopy_bad _ hGood]
    simp only [CopyCoordinates.Context.encode, Nat.add_right_comm q 1, ZeroY.linearParent]

theorem linear_forest (C : CopyCoordinates.Context) :
    forest C Numeric.linearForest = Numeric.linearForest := by
  apply Numeric.parentForest_eq_of_parent_eq
  exact linear_parent C

end OneY.FrameCopy

namespace OneY.Numeric

theorem badAtTerminalBase_select_linear (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) :
    select linearForest (badAtTerminalBase (rootedSequence s hs) hbad).value =
      badAtTerminalBase (rootedSequence s hs) hbad := by
  have ht := badAtTerminalBase_select_external (rootedSequence s hs) hbad linearForest (fun _ => rfl)
  rwa [FrameCopy.linear_forest] at ht

end OneY.Numeric

#print axioms OneY.FrameCopy.linear_forest
#print axioms OneY.Numeric.badAtTerminalBase_select_linear
