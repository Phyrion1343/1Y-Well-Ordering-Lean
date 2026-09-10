import OneY.ReconstructionNumeric
import OneY.Extraction

/-! # Actual downward reconstruction through a finite list of layers -/

namespace OneY.TowerReconstruction

open RootGeometry

def assemble : List RowMountain → (Nat → Nat) → Nat → Nat
  | [], top => top
  | M :: rest, top => Reconstruction.value M (assemble rest top) 0

theorem assemble_positive (mountains : List RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) (c : Nat) : 0 < assemble mountains top c := by
  induction mountains generalizing c with
  | nil => exact hTop c
  | cons M rest ih =>
      exact Reconstruction.value_pos M (assemble rest top)
        (fun c => ih c) (Nat.zero_le _)

theorem height_zero (M : RowMountain) : M.height 0 = 0 := by
  by_cases hh : 0 < M.height 0
  · obtain ⟨p, hp⟩ := M.parent_exists 0 0 hh
    have h := (M.row 0).parent_left hp
    omega
  · omega

theorem assemble_first (mountains : List RowMountain) (top : Nat → Nat) :
    assemble mountains top 0 = top 0 := by
  induction mountains with
  | nil => rfl
  | cons M rest ih =>
      change Reconstruction.value M (assemble rest top) 0 0 = top 0
      have h := Reconstruction.value_top M (assemble rest top) 0
      rw [height_zero M] at h
      rw [h]
      exact ih

def originalGraphs (a : Numeric.RootedRow) (start count : Nat) : List RowMountain :=
  (List.range' start count).map fun k =>
    Numeric.mountain (Numeric.layers a k).row (Numeric.layers a k).positive

/-- The complete downward reconstruction inverts every finite stretch of
the actual extraction tower, including its inherited forest data. -/
theorem assemble_originalGraphs (a : Numeric.RootedRow) (start count : Nat) :
    assemble (originalGraphs a start count) (Numeric.layers a (start+count)).row.value =
      (Numeric.layers a start).row.value := by
  induction count generalizing start with
  | zero => simp [originalGraphs, assemble]
  | succ count ih =>
      have he : start+(count+1) = (start+1)+count := by omega
      simp only [originalGraphs, List.range'_succ, List.map_cons, assemble]
      rw [he]
      change Reconstruction.value (Numeric.mountain (Numeric.layers a start).row
        (Numeric.layers a start).positive)
          (assemble (originalGraphs a (start+1) count)
            (Numeric.layers a ((start+1)+count)).row.value) 0 = _
      rw [ih]
      funext c
      exact Reconstruction.value_numeric_base (Numeric.layers a start).row
        (Numeric.layers a start).positive c

theorem assemble_sequence (s : List Nat) (hs : ZeroY.Legal s) :
    assemble (originalGraphs (Numeric.rootedSequence s hs) 0 (Numeric.sequenceBound s))
      (fun _ => 1) = (Numeric.ofSequence s).value := by
  have hone : (Numeric.layers (Numeric.rootedSequence s hs) (0+Numeric.sequenceBound s)).row.value =
      (fun _ => 1) := by
    funext c
    exact Numeric.sequence_layers_all_one s hs (by omega) c
  have h := assemble_originalGraphs (Numeric.rootedSequence s hs) 0 (Numeric.sequenceBound s)
  rw [hone] at h
  exact h

theorem assemble_family_prefix (M N : Nat → RowMountain) (topM topN : Nat → Nat)
    (width : Nat)
    (hHeight : ∀ k c, c < width → (M k).height c = (N k).height c)
    (hParent : ∀ k r c, c < width → ((M k).row r).parent c = ((N k).row r).parent c)
    (hTop : ∀ c, c < width → topM c = topN c) (start count : Nat) :
    ∀ c, c < width →
      assemble ((List.range' start count).map M) topM c =
        assemble ((List.range' start count).map N) topN c := by
  induction count generalizing start with
  | zero => simpa only [List.range'_zero, List.map_nil, assemble] using hTop
  | succ count ih =>
      intro c hc
      simp only [List.range'_succ, List.map_cons, assemble]
      exact Reconstruction.value_prefix_congr (M start) (N start) _ _ width
        (hHeight start) (hParent start) (ih (start+1)) c hc 0

end OneY.TowerReconstruction

#print axioms OneY.TowerReconstruction.assemble_positive
#print axioms OneY.TowerReconstruction.assemble_originalGraphs
#print axioms OneY.TowerReconstruction.assemble_sequence
