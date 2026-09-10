import OneY.Expansion

/-! # Prefix preservation for the concrete expansion algorithm -/

namespace OneY.Numeric

theorem expandedMountain_height_original (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k : Nat) {c : Nat} (hc : c < x) :
    (expandedMountain a hbad k).height c = height (layers a k).row c := by
  unfold expandedMountain
  split
  · exact LowerCopy.Context.height_original _ (Nat.le_of_lt hc)
  · split
    · rename_i hk he
      subst k
      exact TerminalCopy.Context.height_original _ hc
    · exact OrdinaryCopy.Context.height_original
        (OrdinaryCopy.Context.mk (mountain (layers a k).row (layers a k).positive)
          ⟨y, x, (rows (layers a K).row d).forest.parent_left hbad.1⟩) hc

theorem expandedMountain_parent_original (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k r : Nat) {c : Nat} (hc : c < x) :
    ((expandedMountain a hbad k).row r).parent c =
      (rows (layers a k).row r).forest.parent c := by
  unfold expandedMountain
  split
  · exact LowerCopy.Context.parent_original _ (Nat.le_of_lt hc)
  · split
    · rename_i hk he
      subst k
      exact TerminalCopy.Context.parent_original _ hc r
    · exact OrdinaryCopy.Context.parent_original _ hc r

theorem assemble_expandedGraphs_original (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y)
    {c : Nat} (hc : c < x) :
    TowerReconstruction.assemble
        (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        (fun _ => 1) c = (ofSequence s).value c := by
  have h := TowerReconstruction.assemble_family_prefix
    (expandedMountain (rootedSequence s hs) hbad)
    (fun k => mountain (layers (rootedSequence s hs) k).row
      (layers (rootedSequence s hs) k).positive)
    (fun _ => 1) (fun _ => 1) x
    (fun k _ hc => expandedMountain_height_original _ hbad k hc)
    (fun k r _ hc => expandedMountain_parent_original _ hbad k r hc)
    (fun _ _ => rfl) 0 (sequenceBound s) c hc
  have hseq := congrFun (TowerReconstruction.assemble_sequence s hs) c
  have h' : TowerReconstruction.assemble
        (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        (fun _ => 1) c =
      TowerReconstruction.assemble
        (TowerReconstruction.originalGraphs (rootedSequence s hs) 0 (sequenceBound s))
        (fun _ => 1) c := by
    simpa only [expandedGraphs, TowerReconstruction.originalGraphs,
      List.range_eq_range'] using h
  exact h'.trans hseq

theorem reconstructedValues_length (graphs : List RootGeometry.RowMountain) (width : Nat) :
    (reconstructedValues graphs width).length = width := by
  simp [reconstructedValues]

theorem expandValues_prefix (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {c : Nat} (hc : c < s.length-1) :
    (expandValues s hs N)[c]? = s[c]? := by
  unfold expandValues
  dsimp only
  split
  · exact List.getElem?_take_of_lt hc
  · rename_i z hz
    simp only [reconstructedValues, List.getElem?_map,
      List.getElem?_range (show c < s.length-1+N*(s.length-1-z.column) by omega),
      Option.map_some]
    rw [assemble_expandedGraphs_original s hs (findBadRoot_sound s hs _ hz).2 hc]
    change some (s[c]?.getD 1) = s[c]?
    simp [List.getElem?_eq_getElem (show c < s.length by omega)]

theorem expandValues_take (s : List Nat) (hs : ZeroY.Legal s) (N : Nat) :
    (expandValues s hs N).take (s.length-1) = s.take (s.length-1) := by
  apply List.ext_getElem?
  intro c
  by_cases hc : c < s.length-1
  · rw [List.getElem?_take_of_lt hc, List.getElem?_take_of_lt hc]
    exact expandValues_prefix s hs N hc
  · rw [List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem expandValues_zero (s : List Nat) (hs : ZeroY.Legal s) :
    expandValues s hs 0 = s.take (s.length-1) := by
  have hlen : (expandValues s hs 0).length ≤ s.length-1 := by
    unfold expandValues
    dsimp only
    split
    · simp
    · simp [reconstructedValues_length]
  have h := expandValues_take s hs 0
  rw [List.take_of_length_le hlen] at h
  exact h

end OneY.Numeric

#print axioms OneY.Numeric.assemble_expandedGraphs_original
#print axioms OneY.Numeric.expandValues_zero
