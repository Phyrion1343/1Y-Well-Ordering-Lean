import OneY.TerminalCopyLinear
import OneY.ExpansionProperties

/-! # The computed upper tower and active-layer reconstruction

The all-one cap of the finite executable algorithm is treated explicitly.
No canonicality of any lower layer is used in these assembly equations.
-/

namespace OneY.Numeric

theorem expandedMountain_above (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : K < k) :
    expandedMountain a hbad k =
      (ordinaryCopyContext (layers a k).row (layers a k).positive
        (badAtTerminalContext a hbad).coordinates).toRowMountain := by
  simp only [expandedMountain, dif_neg (show ¬k < K by omega), if_neg (show ¬k = K by omega)]
  rfl

theorem expandedMountain_active (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    expandedMountain a hbad K = (badAtTerminalContext a hbad).toRowMountain := by
  simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
  rfl

theorem assemble_expanded_above (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (start count : Nat) (hStart : K < start) :
    TowerReconstruction.assemble
      ((List.range' start count).map (expandedMountain a hbad))
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (layers a (start+count)).row.value) =
        (badAtTerminalContext a hbad).ordinaryContext.copyValue (layers a start).row.value := by
  induction count generalizing start with
  | zero => simp only [Nat.add_zero, List.range'_zero, List.map_nil, TowerReconstruction.assemble]
  | succ count ih =>
      have he : start+(count+1) = (start+1)+count := by omega
      simp only [List.range'_succ, List.map_cons, TowerReconstruction.assemble, he]
      rw [ih (start+1) (by omega), expandedMountain_above a hbad hStart]
      funext c
      exact ordinaryCopy_value (layers a start).row (layers a start).positive
        (badAtTerminalContext a hbad).coordinates 0 c

theorem assemble_expanded_active (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (count : Nat) :
    TowerReconstruction.assemble
      ((List.range' K (count+1)).map (expandedMountain a hbad))
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (layers a (K+(count+1))).row.value) =
        (badAtTerminalBase a hbad).value := by
  have he : K+(count+1) = (K+1)+count := by omega
  simp only [List.range'_succ, List.map_cons, TowerReconstruction.assemble, he]
  rw [assemble_expanded_above a hbad (K+1) count (Nat.lt_succ_self _), expandedMountain_active]
  rfl

theorem assemble_expanded_sequence_active (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y)
    (hK : K < sequenceBound s) :
    TowerReconstruction.assemble
      ((List.range' K (sequenceBound s-K)).map (expandedMountain (rootedSequence s hs) hbad))
      (fun _ => 1) = (badAtTerminalBase (rootedSequence s hs) hbad).value := by
  have he : sequenceBound s-K = (sequenceBound s-K-1)+1 := by omega
  have hEnd : K+((sequenceBound s-K-1)+1) = sequenceBound s := by omega
  have ht := assemble_expanded_active (rootedSequence s hs) hbad (sequenceBound s-K-1)
  rw [hEnd] at ht
  have hone : (badAtTerminalContext (rootedSequence s hs) hbad).ordinaryContext.copyValue
      (layers (rootedSequence s hs) (sequenceBound s)).row.value = (fun _ => 1) := by
    funext c
    exact sequence_layers_all_one s hs (by omega) _
  rw [hone] at ht
  rw [he]
  exact ht

end OneY.Numeric

#print axioms OneY.Numeric.assemble_expanded_above
#print axioms OneY.Numeric.assemble_expanded_active
#print axioms OneY.Numeric.assemble_expanded_sequence_active
