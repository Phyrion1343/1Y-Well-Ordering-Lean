import OneY.TowerCopyAssembly
import OneY.Prefix

/-! # Every layer above the rebuilt active layer is the computed ordinary copy -/

namespace OneY.Numeric

def badAtTerminalRooted (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : RootedRow where
  row := badAtTerminalBase a hbad
  positive := badAtTerminalBase_positive a hbad
  rootsOne := fun _ hp => badAtTerminalBase_none_eq_one a hbad hp

theorem rawExtract_eq_of_row_eq {a b : Row} (ha : ∀ c, 0 < a.value c)
    (hb : ∀ c, 0 < b.value c) (h : a = b) : rawExtract a ha = rawExtract b hb := by
  cases h
  rfl

theorem badAtTerminalRooted_layers_succ (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (j : Nat) :
    (layers (badAtTerminalRooted a hbad) (j+1)).row =
      ordinaryCopiedBase (layers a (K+(j+1))).row (layers a (K+(j+1))).positive
        (badAtTerminalContext a hbad).coordinates := by
  induction j with
  | zero => exact badAtTerminalBase_rawExtract a hbad
  | succ j ih =>
      change rawExtract (layers (badAtTerminalRooted a hbad) (j+1)).row _ = _
      rw [rawExtract_eq_of_row_eq _ (ordinaryCopiedBase_positive _ _ _) ih, ordinaryCopy_rawExtract]
      have he : K+(j+1+1) = (K+(j+1))+1 := by omega
      simp only [he]
      rfl

theorem badAtTerminalRooted_layers_mountain (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (j : Nat) :
    mountain (layers (badAtTerminalRooted a hbad) j).row
      (layers (badAtTerminalRooted a hbad) j).positive = expandedMountain a hbad (K+j) := by
  cases j with
  | zero =>
      simp only [Nat.add_zero]
      rw [expandedMountain_active]
      exact badAtTerminalBase_mountain a hbad
  | succ j =>
      have ht := badAtTerminalRooted_layers_succ a hbad j
      have hm : mountain (layers (badAtTerminalRooted a hbad) (j+1)).row
          (layers (badAtTerminalRooted a hbad) (j+1)).positive =
        mountain (ordinaryCopiedBase (layers a (K+(j+1))).row (layers a (K+(j+1))).positive
          (badAtTerminalContext a hbad).coordinates) (ordinaryCopiedBase_positive _ _ _) := by
        congr 1
      rw [hm, ordinaryCopy_mountain, expandedMountain_above a hbad (by omega)]

theorem ofSequence_reconstructedValues_agreesBelow (graphs : List RootGeometry.RowMountain)
    (width : Nat) (base : Row)
    (hValue : TowerReconstruction.assemble graphs (fun _ => 1) = base.value)
    (hSelected : select linearForest base.value = base) :
    (ofSequence (reconstructedValues graphs width)).AgreesBelow base width := by
  have hv : ∀ c, c < width → (ofSequence (reconstructedValues graphs width)).value c = base.value c := by
    intro c hc
    change ((List.range width).map (TowerReconstruction.assemble graphs (fun _ => 1)))[c]?.getD 1 = _
    simp only [List.getElem?_map, List.getElem?_range hc, Option.map_some, Option.getD_some, hValue]
  refine ⟨hv, ?_⟩
  intro c hc
  have ht := restrictedParent_agreesBelow linearForest linearForest
    (ofSequence (reconstructedValues graphs width)).value base.value width (fun _ _ => rfl) hv hc
  exact ht.trans (congrArg (fun a : Row => a.forest.parent c) hSelected)

theorem reconstructedValues_active_zero_agreesBelow (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) (width : Nat) :
    (ofSequence (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)).AgreesBelow
      (badAtTerminalBase (rootedSequence s hs) hbad) width := by
  apply ofSequence_reconstructedValues_agreesBelow
  · have ht := assemble_expanded_sequence_active s hs hbad (sequenceBound_pos s)
    simpa only [Nat.sub_zero, List.range_eq_range', expandedGraphs] using ht
  · exact badAtTerminalBase_select_linear s hs hbad

theorem reconstructedValues_active_zero_layers (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) (width k : Nat) :
    (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row.AgreesBelow
      (layers (badAtTerminalRooted (rootedSequence s hs) hbad) k).row width :=
  layers_agree_below _ _ (reconstructedValues_active_zero_agreesBelow s hs hbad width) k

theorem reconstructedValues_active_zero_height (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) (width k : Nat)
    {c : Nat} (hc : c < width) :
    height (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row c =
        (expandedMountain (rootedSequence s hs) hbad k).height c := by
  rw [(reconstructedValues_active_zero_layers s hs hbad width k).height hc]
  have ht := congrArg (fun M : RootGeometry.RowMountain => M.height c)
    (badAtTerminalRooted_layers_mountain (rootedSequence s hs) hbad k)
  simpa only [Nat.zero_add, mountain] using ht

theorem reconstructedValues_active_zero_parent (s : List Nat) (hs : ZeroY.Legal s)
    {d x y : Nat} (hbad : BadAt (rootedSequence s hs) 0 d x y) (width k r : Nat)
    {c : Nat} (hc : c < width) :
    (rows (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row r).forest.parent c =
        ((expandedMountain (rootedSequence s hs) hbad k).row r).parent c := by
  rw [((reconstructedValues_active_zero_layers s hs hbad width k).rows r).2 c hc]
  have ht := congrArg (fun M : RootGeometry.RowMountain => (M.row r).parent c)
    (badAtTerminalRooted_layers_mountain (rootedSequence s hs) hbad k)
  simpa only [Nat.zero_add, mountain] using ht

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminalRooted_layers_mountain
#print axioms OneY.Numeric.reconstructedValues_active_zero_layers
#print axioms OneY.Numeric.reconstructedValues_active_zero_parent
