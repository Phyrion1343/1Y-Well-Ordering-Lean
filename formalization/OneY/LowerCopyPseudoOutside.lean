import OneY.LowerCopyPseudoHigh

/-! # Exact pseudo-parent transport above the floor outside the lifted cone -/

namespace OneY.LowerCopy.Context

theorem parent_outside_all (C : Context) {s r : Nat} (hs : s ≤ C.coordinates.x)
    (hOut : ¬ C.InCone s) (b : Nat) :
    C.parent r (C.coordinates.parentCopy b s) =
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  cases hp : (C.mountain.row r).parent s with
  | none =>
      rw [Option.map_none]
      apply (C.parent_none_iff _ _).mpr
      rw [C.height_parentCopy hs b, if_neg hOut]
      exact (C.mountain.parent_none_iff _ _).mp hp
  | some p =>
      rw [Option.map_some]
      have hNot : s ≠ C.coordinates.y := by
        intro he
        subst s
        exact hOut C.root_inCone
      have ht := C.parent_rowCopy hs hNot hp b
      rwa [C.rowCopy_outside hOut] at ht

theorem outside_ancestor_preimage (C : Context) {s r a : Nat}
    (hs : s ≤ C.coordinates.x) (hOut : ¬ C.InCone s) (hr : C.floor ≤ r) (b : Nat)
    (ha : (C.row r).Ancestor a (C.coordinates.parentCopy b s)) :
    ∃ q, (C.mountain.row r).Ancestor q s ∧ a = C.coordinates.parentCopy b q := by
  have main : ∀ n s, s ≤ C.coordinates.x → ¬ C.InCone s → n = C.coordinates.parentCopy b s →
      ∀ a, (C.row r).Ancestor a n →
        ∃ q, (C.mountain.row r).Ancestor q s ∧ a = C.coordinates.parentCopy b q := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro s hs hOut he a ha
        cases ha with
        | direct hp =>
            change C.parent r n = some a at hp
            rw [he, C.parent_outside_all hs hOut b] at hp
            obtain ⟨q, hq, hEq⟩ := Option.map_eq_some_iff.mp hp
            exact ⟨q, ParentForest.Ancestor.direct hq, hEq.symm⟩
        | @step p n hPath hp =>
            have hlt := (C.row r).parent_left hp
            change C.parent r n = some p at hp
            rw [he, C.parent_outside_all hs hOut b] at hp
            obtain ⟨q, hq, hEq⟩ := Option.map_eq_some_iff.mp hp
            have hqLt := (C.mountain.row r).parent_left hq
            obtain ⟨z, hz, hza⟩ := ih p hlt q (by omega) (C.high_parent_outside hr hOut hq)
              hEq.symm a hPath
            exact ⟨z, ParentForest.Ancestor.step hz hq, hza⟩
  exact main _ s hs hOut rfl a ha

theorem pseudoCandidate_outside_high_iff (C : Context) {s a : Nat}
    (hx : s ≤ C.coordinates.x) (hOut : ¬ C.InCone s) (ht : C.floor < C.mountain.height s) (b : Nat) :
    Pseudo.Candidate C.toRowMountain (C.coordinates.parentCopy b s) a ↔
      ∃ q, Pseudo.Candidate C.mountain s q ∧ a = C.coordinates.parentCopy b q := by
  have hHeight : C.toRowMountain.height (C.coordinates.parentCopy b s) = C.mountain.height s := by
    change C.height _ = _
    rw [C.height_parentCopy hx b, if_neg hOut]
  have hu : C.floor ≤ C.mountain.height s-1 := by omega
  constructor
  · rintro ⟨ha, hh⟩
    rw [hHeight] at ha
    obtain ⟨q, hq, hEq⟩ := C.outside_ancestor_preimage hx hOut hu b ha
    have hqOut := C.high_ancestor_outside hu hOut hq
    have hqLt := hq.lt
    have hqHeight : C.toRowMountain.height (C.coordinates.parentCopy b q) = C.mountain.height q := by
      change C.height _ = _
      rw [C.height_parentCopy (by omega) b, if_neg hqOut]
    rw [hEq, hqHeight, hHeight] at hh
    exact ⟨q, ⟨hq, hh⟩, hEq⟩
  · rintro ⟨q, ⟨hq, hh⟩, rfl⟩
    have hqOut := C.high_ancestor_outside hu hOut hq
    have hqLt := hq.lt
    have hqHeight : C.toRowMountain.height (C.coordinates.parentCopy b q) = C.mountain.height q := by
      change C.height _ = _
      rw [C.height_parentCopy (by omega) b, if_neg hqOut]
    constructor
    · rw [hHeight]
      exact C.outside_ancestor_copy hu hOut hq hx b
    · rwa [hqHeight, hHeight]

theorem pseudo_parent_outside_high (C : Context) {s : Nat}
    (hx : s ≤ C.coordinates.x) (hOut : ¬ C.InCone s) (ht : C.floor < C.mountain.height s) (b : Nat) :
    Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b s) =
      (Pseudo.parent C.mountain s).map (C.coordinates.parentCopy b) := by
  cases hp : Pseudo.parent C.mountain s with
  | none =>
      have := (Pseudo.parent_none_iff C.mountain s).mp hp
      omega
  | some p =>
      have hSpec := (Pseudo.parent_some_iff C.mountain s p).mp hp
      rw [Option.map_some]
      apply (Pseudo.parent_some_iff C.toRowMountain _ _).mpr
      refine ⟨?_, (C.pseudoCandidate_outside_high_iff hx hOut ht b).mpr ⟨p, hSpec.2.1, rfl⟩, ?_⟩
      · change 0 < C.height (C.coordinates.parentCopy b s)
        rw [C.height_parentCopy hx b, if_neg hOut]
        omega
      · intro a ha
        obtain ⟨q, hq, he⟩ := (C.pseudoCandidate_outside_high_iff hx hOut ht b).mp ha
        have hle := hSpec.2.2 q hq
        rw [he]
        unfold CopyCoordinates.Context.parentCopy
        split <;> split <;> omega

#print axioms outside_ancestor_preimage
#print axioms pseudo_parent_outside_high

end OneY.LowerCopy.Context
