import OneY.SparseComparison
import OneY.ForestBridge
import ZeroY.Forest.Blocker

/-! # Local recovery of sparse nearest-smaller parents from a blocker -/

namespace OneY.Numeric

theorem parentForest_eq_of_parent_eq (F G : ParentForest)
    (h : ∀ c, F.parent c = G.parent c) : F = G := by
  cases F with
  | mk f hf =>
      cases G with
      | mk g hg =>
          have he : f = g := funext h
          cases he
          rfl

theorem restrictedParent_eq_of_direct_parent (a : Row) (F : ParentForest)
    {c p : Nat} (hP : a.forest.parent c = some p) (hQ : F.parent c = some p) :
    restrictedParent F a.value c = some p := by
  apply (restrictedParent_some_iff F a.value c p).mpr
  have hv := a.parent_values hP
  refine ⟨Relation.TransGen.single hQ, hv.1, hv.2, ?_⟩
  intro q hq _ _
  rcases ZeroY.Forest.ancestor_eq_or_below_parent hQ hq with he | ha
  · omega
  · exact Nat.le_of_lt (ZeroY.Forest.ancestor_lt F.parent_left ha)

theorem exists_value_cap (v : Nat → Nat) (n : Nat) :
    ∃ cap, ∀ i, i ≤ n → v i ≤ cap := by
  induction n with
  | zero =>
      refine ⟨v 0, ?_⟩
      intro i hi
      have he : i = 0 := by omega
      rw [he]
      exact Nat.le_refl _
  | succ n ih =>
      obtain ⟨cap, hCap⟩ := ih
      refine ⟨max cap (v (n+1)), ?_⟩
      intro i hi
      by_cases hn : i ≤ n
      · exact Nat.le_trans (hCap i hn) (Nat.le_max_left _ _)
      · have he : i = n+1 := by omega
        rw [he]
        exact Nat.le_max_right _ _

theorem parent_eq_filled_of_prefix (a : Row) (F : ParentForest) {bound cap c p : Nat}
    (hCap : ∀ i, i ≤ bound → a.value i ≤ cap)
    (hPrefix : ∀ i, i < bound → restrictedParent F a.value i = a.forest.parent i)
    (hc : c < bound) (hp : a.forest.parent c = some p) :
    ZeroY.Forest.nearestSmaller F.parent (filledValue cap a.value) c = some p := by
  have hv := a.parent_values hp
  have hPos : 0 < a.value c := by omega
  rw [← restrictedParent_eq_filled_nearestSmaller F a.value cap hPos (hCap c (by omega)),
    hPrefix c hc, hp]

theorem ancestor_to_filled_of_prefix (a : Row) (F : ParentForest) {bound cap c p : Nat}
    (hCap : ∀ i, i ≤ bound → a.value i ≤ cap)
    (hPrefix : ∀ i, i < bound → restrictedParent F a.value i = a.forest.parent i)
    (hc : c < bound) (ha : a.forest.Ancestor p c) :
    (F.nearestSmaller (filledValue cap a.value)).Ancestor p c := by
  induction ha with
  | direct hp => exact ParentForest.Ancestor.direct (parent_eq_filled_of_prefix a F hCap hPrefix hc hp)
  | @step q c ha hp ih =>
      have hLeft := a.forest.parent_left hp
      exact ParentForest.Ancestor.step (ih (by omega))
        (parent_eq_filled_of_prefix a F hCap hPrefix hc hp)

/-- The current sparse parent is recovered, using only the already recovered
strict prefix and a blocker in the specified forest. Absent cells are handled
by the sentinel conversion, not by assuming the whole row is canonical. -/
theorem restrictedParent_eq_of_blocker (a : Row) (F : ParentForest)
    {c q p z : Nat} (hQ : F.parent c = some q) (hP : a.forest.parent c = some p)
    (hAnc : F.Ancestor p c)
    (hPrefix : ∀ i, i < c → restrictedParent F a.value i = a.forest.parent i)
    (hZ : z = q ∨ a.forest.Ancestor z q) (hZParent : a.forest.parent z = some p)
    (hUpper : a.value c ≤ a.value z) : restrictedParent F a.value c = some p := by
  obtain ⟨cap, hCap⟩ := exists_value_cap a.value c
  have hQLt := F.parent_left hQ
  have hZLt : z < c := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hPV := a.parent_values hP
  have hZV := a.parent_values hZParent
  have hCPos : 0 < a.value c := by omega
  have hZPos : 0 < a.value z := by omega
  have hZNew : z = q ∨ ZeroY.Forest.Ancestor
      (ZeroY.Forest.nearestSmaller F.parent (filledValue cap a.value)) q z := by
    rcases hZ with he | ha
    · exact Or.inl he
    · exact Or.inr (ParentForest.ancestor_to_zeroY
        (ancestor_to_filled_of_prefix a F hCap hPrefix hQLt ha))
  have hZParentNew := parent_eq_filled_of_prefix a F hCap hPrefix hZLt hZParent
  have hLowerFilled : filledValue cap a.value p < filledValue cap a.value c := by
    rw [filledValue_positive cap a.value hPV.1, filledValue_positive cap a.value hCPos]
    exact hPV.2
  have hUpperFilled : filledValue cap a.value c ≤ filledValue cap a.value z := by
    rw [filledValue_positive cap a.value hCPos, filledValue_positive cap a.value hZPos]
    exact hUpper
  have hDense := ZeroY.Forest.nearestSmaller_eq_of_blocker F.parent_left
    (ZeroY.Forest.nearestSmaller_leftward F.parent (filledValue cap a.value)) hQ
    (ParentForest.ancestor_to_zeroY hAnc) (fun _ _ => rfl)
    hZNew hZParentNew hLowerFilled hUpperFilled
  rw [restrictedParent_eq_filled_nearestSmaller F a.value cap hCPos (hCap c (Nat.le_refl _))]
  exact hDense

theorem filled_parent_positive (F : ParentForest) (v : Nat → Nat) {cap c p : Nat}
    (hc : 0 < v c) (hCap : v c ≤ cap)
    (hp : ZeroY.Forest.nearestSmaller F.parent (filledValue cap v) c = some p) :
    0 < v p ∧ v p ≤ cap := by
  have hVal := ((ZeroY.Forest.nearestSmaller_some_iff F.parent_left).mp hp).2.1
  rw [filledValue_positive cap v hc] at hVal
  have hPos : 0 < v p := by
    by_cases hz : v p = 0
    · rw [filledValue, if_pos hz] at hVal
      omega
    · omega
  rw [filledValue_positive cap v hPos] at hVal
  exact ⟨hPos, by omega⟩

theorem filled_ancestor_to_sparse (F : ParentForest) (v : Nat → Nat) {cap c p : Nat}
    (hc : 0 < v c) (hCap : v c ≤ cap)
    (ha : (F.nearestSmaller (filledValue cap v)).Ancestor p c) :
    (select F v).forest.Ancestor p c := by
  induction ha with
  | direct hp =>
      apply ParentForest.Ancestor.direct
      change restrictedParent F v _ = _
      rw [restrictedParent_eq_filled_nearestSmaller F v cap hc hCap]
      exact hp
  | step _ hp ih =>
      have hPos := filled_parent_positive F v hc hCap hp
      apply ParentForest.Ancestor.step (ih hPos.1 hPos.2)
      change restrictedParent F v _ = _
      rw [restrictedParent_eq_filled_nearestSmaller F v cap hc hCap]
      exact hp

/-- A sparse search skipping a positive direct candidate automatically has
a positive blocker. This is the actual sparse analogue of the old NS lemma. -/
theorem restrictedParent_exists_blocker (F : ParentForest) (v : Nat → Nat)
    {c q p : Nat} (hQ : F.parent c = some q)
    (hP : restrictedParent F v c = some p) (hDistinct : p ≠ q) (hQPos : 0 < v q) :
    ∃ z, (z = q ∨ (select F v).forest.Ancestor z q) ∧
      restrictedParent F v z = some p ∧ v c ≤ v z := by
  obtain ⟨cap, hCap⟩ := exists_value_cap v c
  have hPV := (restrictedParent_spec F v hP).2
  have hCPos : 0 < v c := by omega
  have hQLt := F.parent_left hQ
  have hDenseP : ZeroY.Forest.nearestSmaller F.parent (filledValue cap v) c = some p := by
    rw [← restrictedParent_eq_filled_nearestSmaller F v cap hCPos (hCap c (Nat.le_refl _))]
    exact hP
  obtain ⟨z, hZPath, hZParent, hZLe⟩ := ZeroY.Forest.nearestSmaller_exists_blocker
    F.parent_left hQ hDenseP hDistinct
  have hQCap := hCap q (Nat.le_of_lt hQLt)
  have hZFilledCap : filledValue cap v z ≤ cap := by
    rcases hZPath with he | ha
    · rw [he, filledValue_positive cap v hQPos]
      exact hQCap
    · have hv := (ZeroY.Forest.nearestSmaller_ancestor_record F.parent_left ha).1
      rw [filledValue_positive cap v hQPos] at hv
      omega
  have hZPos : 0 < v z := by
    by_cases hz : v z = 0
    · rw [filledValue, if_pos hz] at hZFilledCap
      omega
    · omega
  have hZCap : v z ≤ cap := by simpa only [filledValue_positive cap v hZPos] using hZFilledCap
  refine ⟨z, ?_, ?_, ?_⟩
  · rcases hZPath with he | ha
    · exact Or.inl he
    · exact Or.inr (filled_ancestor_to_sparse F v hQPos hQCap (ParentForest.ancestor_of_zeroY ha))
  · rw [restrictedParent_eq_filled_nearestSmaller F v cap hZPos hZCap]
    exact hZParent
  · simpa only [filledValue_positive cap v hCPos, filledValue_positive cap v hZPos] using hZLe

#print axioms restrictedParent_eq_of_blocker
#print axioms restrictedParent_exists_blocker

end OneY.Numeric
