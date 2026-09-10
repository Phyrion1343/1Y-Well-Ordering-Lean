import OneY.ReconstructionComparison

/-! # No extra parent at a reconstructed column top

The proof uses the strict left prefix of the current row. It does not assume
the current top is canonical or that depth-NS has already been recovered for
the copied mountain.
-/

namespace OneY.Reconstruction

open RootGeometry LowerCopy.Context

def PseudoTopBound (M : RowMountain) (top : Nat → Nat) : Prop :=
  ∀ c p, Pseudo.parent M c = some p → M.height c = M.height p → top c ≤ top p

def ExtractedHeightDecrease (M : RowMountain) (top : Nat → Nat) : Prop :=
  ∀ c p, Numeric.restrictedParent (Pseudo.forest M) top c = some p → M.height p < M.height c

theorem pseudoTopBound_of_extractedHeightDecrease (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) (hDecrease : ExtractedHeightDecrease M top) : PseudoTopBound M top := by
  intro c p hp hHeight
  by_cases hBound : top c ≤ top p
  · exact hBound
  · have hChosen : Numeric.restrictedParent (Pseudo.forest M) top c = some p := by
      apply (Numeric.restrictedParent_some_iff (Pseudo.forest M) top c p).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (ParentForest.Ancestor.direct hp), hTop p, by omega, ?_⟩
      intro q ha _ _
      rcases ZeroY.Forest.ancestor_eq_or_below_parent hp ha with he | hAnc
      · omega
      · have := ZeroY.Forest.ancestor_lt (Pseudo.forest M).parent_left hAnc
        omega
    have hLt := hDecrease c p hChosen
    omega

/-- A top row is recovered from its current-row strict left prefix and the
upper-layer inequality at equal-height pseudo-parent edges. -/
theorem restrictedParent_top_none (M : RowMountain) (top : Nat → Nat) (hTop : ∀ c, 0 < top c)
    (hBound : PseudoTopBound M top) {u c : Nat} (hHeight : M.height c = u+1)
    (hPrefix : ∀ i, i < c → Numeric.restrictedParent (M.row u) (value M top (u+1)) i =
      (M.row (u+1)).parent i) :
    Numeric.restrictedParent (M.row u) (value M top (u+1)) c = none := by
  apply (Numeric.restrictedParent_none_iff (M.row u) (value M top (u+1)) c).mpr
  intro q hCandidate hQPositive
  have hQLt := hCandidate.lt
  have hQLive := (value_pos_iff M top hTop _ _).mp hQPositive
  let a := M.rootAt (u+1) q
  have hAHeight : M.height a = u+1 := M.root_height hQLive
  have hALe : a ≤ q := M.rootAt_le (u+1) q
  have hACandidate : (M.row u).Ancestor a c := by
    rcases (M.row (u+1)).root_ancestor_or_eq q with ha | he
    · exact (ParentForest.Refines.ancestor (M.nested_succ u) ha).trans hCandidate
    · change a = q at he
      rw [he]
      exact hCandidate
  have hAValue : value M top (u+1) a ≤ value M top (u+1) q := by
    rcases (M.row (u+1)).root_ancestor_or_eq q with ha | he
    · exact value_ancestor_le M top ha
    · change a = q at he
      rw [he]
      exact Nat.le_refl _
  have hAPseudo : Pseudo.Candidate M c a := by
    unfold Pseudo.Candidate
    rw [hHeight, Nat.add_sub_cancel]
    exact ⟨hACandidate, Or.inl hAHeight⟩
  cases hp : Pseudo.parent M c with
  | none =>
      have hh := (Pseudo.parent_none_iff M c).mp hp
      omega
  | some p =>
      obtain ⟨_, hPCandidate, hMax⟩ := (Pseudo.parent_some_iff M c p).mp hp
      have hPHeight := hPCandidate.2
      have hALeP := hMax a hAPseudo
      have hPLt := Pseudo.parent_left M hp
      have hPCandidateU : (M.row u).Ancestor p c := by
        have ha := hPCandidate.1
        rw [hHeight, Nat.add_sub_cancel] at ha
        exact ha
      have hAPath : a = p ∨ (M.row u).Ancestor a p := by
        rcases Nat.eq_or_lt_of_le hALeP with he | hl
        · exact Or.inl he
        · exact Or.inr (ParentForest.ancestor_of_zeroY
            (ZeroY.Forest.ancestor_of_common_target (M.row u).parent_left
              (ParentForest.ancestor_to_zeroY hACandidate) (ParentForest.ancestor_to_zeroY hPCandidateU) hl))
      have hPTop : M.height p = u+1 := by
        rcases hAPath with he | ha
        · rw [← he]
          exact hAHeight
        · have hPLive : u < M.height p := by
            cases ha with
            | direct hh => exact M.parent_source hh
            | step _ hh => exact M.parent_source hh
          omega
      have hTopCP := hBound c p hp (hHeight.trans hPTop.symm)
      have hPAValue : value M top (u+1) p ≤ value M top (u+1) a := by
        rcases hAPath with he | ha
        · rw [he]
          exact Nat.le_refl _
        · have hNone : Numeric.restrictedParent (M.row u) (value M top (u+1)) p = none :=
            (hPrefix p hPLt).trans ((M.parent_none_iff (u+1) p).mpr (by omega))
          exact (Numeric.restrictedParent_none_iff (M.row u) (value M top (u+1)) p).mp hNone a ha
            (value_pos M top hTop (by omega))
      have hCValue : value M top (u+1) c = top c := by rw [← hHeight, value_top]
      have hPValue : value M top (u+1) p = top p := by rw [← hPTop, value_top]
      rw [hCValue]
      rw [hPValue] at hPAValue
      omega

theorem restrictedParent_top_none_of_extracted (M : RowMountain) (top : Nat → Nat)
    (hTop : ∀ c, 0 < top c) (hDecrease : ExtractedHeightDecrease M top)
    {u c : Nat} (hHeight : M.height c = u+1)
    (hPrefix : ∀ i, i < c → Numeric.restrictedParent (M.row u) (value M top (u+1)) i =
      (M.row (u+1)).parent i) :
    Numeric.restrictedParent (M.row u) (value M top (u+1)) c = none :=
  restrictedParent_top_none M top hTop (pseudoTopBound_of_extractedHeightDecrease M top hTop hDecrease) hHeight hPrefix

#print axioms pseudoTopBound_of_extractedHeightDecrease
#print axioms restrictedParent_top_none
#print axioms restrictedParent_top_none_of_extracted

end OneY.Reconstruction
