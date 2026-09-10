import OneY.TerminalTowerRebuild
import OneY.RootIndexed.Prefix
import OneY.RootIndexed.CopyDiagram

/-! # Transporting actual finite reconstruction to every computed layer -/

namespace OneY.Numeric

theorem reconstructedValues_layers_agreesBelow (graphs : List RootGeometry.RowMountain)
    (width : Nat) (base : RootedRow)
    (hValue : TowerReconstruction.assemble graphs (fun _ => 1) = base.row.value)
    (hSelected : select linearForest base.row.value = base.row) (k : Nat) :
    (layers (rootedSequence (reconstructedValues graphs width) (reconstructedValues_legal _ _)) k).row.AgreesBelow
      (layers base k).row width :=
  layers_agree_below _ _ (ofSequence_reconstructedValues_agreesBelow graphs width base.row hValue hSelected) k

theorem expandValues_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) :
    expandValues s hs N =
      reconstructedValues (expandedGraphs (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 (sequenceBound s))
        (s.length-1 + N*(s.length-1-z.column)) := by
  unfold expandValues
  dsimp only
  split
  · rename_i hn
    rw [hz] at hn
    contradiction
  · rename_i w hw
    have he : w = z := Option.some.inj (hw.symm.trans hz)
    subst w
    rfl

theorem expandedMountain_height_zero_above_bound (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y)
    (hK : K < sequenceBound s) {k : Nat} (hk : sequenceBound s ≤ k) (c : Nat) :
    (expandedMountain (rootedSequence s hs) hbad k).height c = 0 := by
  rw [expandedMountain_above _ hbad (by omega : K < k)]
  change height (layers (rootedSequence s hs) k).row _ = 0
  have hn := sequence_layers_no_parents s hs (by omega : sequenceBound s ≤ k+1)
  apply Nat.eq_zero_of_le_zero
  exact ((mountain (layers (rootedSequence s hs) k).row
    (layers (rootedSequence s hs) k).positive).parent_none_iff 0 _).mp (hn _)

end OneY.Numeric

namespace OneY.RootIndexed

open Numeric

theorem mountainDiagram_isPrefix_of_height_bound (M N : Nat → RootGeometry.RowMountain)
    (width J bound : Nat)
    (hH : ∀ k c, c < width → (M k).height c = (N k).height c)
    (hP : ∀ k r c, c < width → ((M k).row r).parent c = ((N k).row r).parent c)
    (hEmpty : ∀ k, bound ≤ k → ∀ c, c < width → (N k).height c = 0) :
    (mountainDiagram J width M).IsPrefix (mountainDiagram bound width N) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro e he
  obtain ⟨k, _, c, hc, r, hr, he⟩ := (mem_towerAtoms_iff J width M e).mp he
  have hrN : r < (N k).height c := by rw [← hH k c hc]; exact hr
  have hk : k < bound := by
    by_cases hk : k < bound
    · exact hk
    · rw [hEmpty k (by omega) c hc] at hrN
      omega
  apply (mem_towerAtoms_iff bound width N e).mpr
  refine ⟨k, hk, c, hc, r, hrN, ?_⟩
  rw [← rowAtom_prefix_congr k (M k) (N k) width (hP k) r hc]
  exact he

theorem reconstructedValues_diagram_isPrefix (graphs : List RootGeometry.RowMountain)
    (width : Nat) (base : RootedRow)
    (hValue : TowerReconstruction.assemble graphs (fun _ => 1) = base.row.value)
    (hSelected : select linearForest base.row.value = base.row)
    (M : Nat → RootGeometry.RowMountain)
    (hMountain : ∀ k, mountain (layers base k).row (layers base k).positive = M k)
    (bound : Nat) :
    (sequenceDiagram (reconstructedValues graphs width) (reconstructedValues_legal _ _) bound).IsPrefix
      (mountainDiagram bound width M) := by
  unfold sequenceDiagram
  rw [reconstructedValues_length]
  apply mountainDiagram_isPrefix (Nat.le_refl _) (Nat.le_refl _)
  · intro k c hc
    have ht := (reconstructedValues_layers_agreesBelow graphs width base hValue hSelected k).height hc
    have hm := congrArg (fun N : RootGeometry.RowMountain => N.height c) (hMountain k)
    exact ht.trans hm
  · intro k r c hc
    have ht := ((reconstructedValues_layers_agreesBelow graphs width base hValue hSelected k).rows r).2 c hc
    have hm := congrArg (fun N : RootGeometry.RowMountain => (N.row r).parent c) (hMountain k)
    exact ht.trans hm

theorem reconstructedValues_diagram_isPrefix_of_height_bound (graphs : List RootGeometry.RowMountain)
    (width : Nat) (base : RootedRow)
    (hValue : TowerReconstruction.assemble graphs (fun _ => 1) = base.row.value)
    (hSelected : select linearForest base.row.value = base.row)
    (M : Nat → RootGeometry.RowMountain)
    (hMountain : ∀ k, mountain (layers base k).row (layers base k).positive = M k)
    (J bound : Nat) (hEmpty : ∀ k, bound ≤ k → ∀ c, c < width → (M k).height c = 0) :
    (sequenceDiagram (reconstructedValues graphs width) (reconstructedValues_legal _ _) J).IsPrefix
      (mountainDiagram bound width M) := by
  unfold sequenceDiagram
  rw [reconstructedValues_length]
  apply mountainDiagram_isPrefix_of_height_bound _ _ width J bound
  · intro k c hc
    have ht := (reconstructedValues_layers_agreesBelow graphs width base hValue hSelected k).height hc
    exact ht.trans (congrArg (fun N : RootGeometry.RowMountain => N.height c) (hMountain k))
  · intro k r c hc
    have ht := ((reconstructedValues_layers_agreesBelow graphs width base hValue hSelected k).rows r).2 c hc
    exact ht.trans (congrArg (fun N : RootGeometry.RowMountain => (N.row r).parent c) (hMountain k))
  · exact hEmpty

theorem reconstructedValues_active_zero_diagram_isPrefix (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) (N bound : Nat) :
    (sequenceDiagram
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        ((badCoordinates (rootedSequence s hs) hbad).width N))
      (reconstructedValues_legal _ _) bound).IsPrefix
      (copyDiagram (rootedSequence s hs) hbad bound N) := by
  apply reconstructedValues_diagram_isPrefix _ _ (badAtTerminalRooted (rootedSequence s hs) hbad)
  · have ht := assemble_expanded_sequence_active s hs hbad (sequenceBound_pos s)
    simpa only [Nat.sub_zero, List.range_eq_range', expandedGraphs, badAtTerminalRooted] using ht
  · exact badAtTerminalBase_select_linear s hs hbad
  · intro k
    simpa only [Nat.zero_add] using badAtTerminalRooted_layers_mountain (rootedSequence s hs) hbad k

end OneY.RootIndexed

#print axioms OneY.Numeric.expandValues_of_badRoot
#print axioms OneY.RootIndexed.reconstructedValues_diagram_isPrefix
#print axioms OneY.RootIndexed.reconstructedValues_active_zero_diagram_isPrefix
