import OneY.BadRoot

/-! # The executable mountain builder stops at the first all-one layer -/

namespace OneY.Numeric

theorem rowDone_iff (n : Nat) (a : RootedRow) :
    rowDone n a = true ↔ ∀ c, c < n → a.row.value c = 1 := by
  simp only [rowDone, List.all_eq_true, List.mem_range, decide_eq_true_eq]

def stopLayer (s : List Nat) (hs : ZeroY.Legal s) : Nat :=
  (List.range (sequenceBound s)).findIdx fun k =>
    rowDone s.length (layers (rootedSequence s hs) k)

theorem sequenceBound_pos (s : List Nat) : 0 < sequenceBound s := by
  have h : 1 ≤ sequenceBound s := Nat.le_max_left _ _
  omega

theorem stopLayer_lt (s : List Nat) (hs : ZeroY.Legal s) :
    stopLayer s hs < sequenceBound s := by
  have hpos := sequenceBound_pos s
  have hd := sequence_layers_all_one s hs (k := sequenceBound s-1) (by omega)
  have hex : ∃ k ∈ List.range (sequenceBound s),
      rowDone s.length (layers (rootedSequence s hs) k) = true := by
    refine ⟨sequenceBound s-1, ?_, (rowDone_iff _ _).mpr (fun c _ => hd c)⟩
    simp only [List.mem_range]
    omega
  have h := List.findIdx_lt_length_of_exists hex
  simpa only [stopLayer, List.length_range] using h

theorem stopLayer_done (s : List Nat) (hs : ZeroY.Legal s) :
    rowDone s.length (layers (rootedSequence s hs) (stopLayer s hs)) = true := by
  have hi : (List.range (sequenceBound s)).findIdx
      (fun k => rowDone s.length (layers (rootedSequence s hs) k)) <
        (List.range (sequenceBound s)).length := by
    simpa only [stopLayer, List.length_range] using stopLayer_lt s hs
  have h := @List.findIdx_getElem Nat
    (fun k => rowDone s.length (layers (rootedSequence s hs) k))
    (List.range (sequenceBound s)) hi
  simpa only [stopLayer, List.getElem_range] using h

theorem before_stopLayer_not_done (s : List Nat) (hs : ZeroY.Legal s)
    {k : Nat} (hk : k < stopLayer s hs) :
    rowDone s.length (layers (rootedSequence s hs) k) = false := by
  have h := List.not_of_lt_findIdx (xs := List.range (sequenceBound s))
    (p := fun k => rowDone s.length (layers (rootedSequence s hs) k)) hk
  simpa only [List.getElem_range] using h

theorem completeLayers_eq (s : List Nat) (hs : ZeroY.Legal s) :
    completeLayers s hs =
      ((List.range (sequenceBound s)).map (layers (rootedSequence s hs))).take
        (stopLayer s hs+1) := by
  simp only [completeLayers, boundedLayers, List.findIdx_map, stopLayer,
    Function.comp_def]

theorem completeLayers_length (s : List Nat) (hs : ZeroY.Legal s) :
    (completeLayers s hs).length = stopLayer s hs+1 := by
  rw [completeLayers_eq]
  simp only [List.length_take, List.length_map, List.length_range]
  exact Nat.min_eq_left (by have := stopLayer_lt s hs; omega)

theorem completeLayers_nonempty (s : List Nat) (hs : ZeroY.Legal s) :
    completeLayers s hs ≠ [] := by
  intro he
  have h := completeLayers_length s hs
  rw [he] at h
  simp at h

end OneY.Numeric

#print axioms OneY.Numeric.stopLayer_done
#print axioms OneY.Numeric.before_stopLayer_not_done
#print axioms OneY.Numeric.completeLayers_length
