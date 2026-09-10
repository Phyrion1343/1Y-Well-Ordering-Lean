import OneY.LowerCopyPseudoSeam
import OneY.LowerCopyRoots

/-! # Exact pseudo-parent transport inside the lifted cone -/

namespace OneY.LowerCopy.Context

theorem parent_lifted_including_root (C : Context) {s u : Nat}
    (hs : s ≤ C.coordinates.x) (hCone : C.InCone s) (hu : C.floor ≤ u) (b : Nat) :
    C.parent (u+b*C.rise) (s+b*C.coordinates.length) =
      ((C.mountain.row u).parent s).map (fun q => q+b*C.coordinates.length) := by
  by_cases he : s = C.coordinates.y
  · subst s
    have hp : (C.mountain.row u).parent C.coordinates.y = none :=
      (C.mountain.parent_none_iff _ _).mpr hu
    rw [hp, Option.map_none]
    apply (C.parent_none_iff _ _).mpr
    rw [C.height_root_copy]
    omega
  · exact C.parent_encode_lifted (by have := C.root_le_of_inCone hCone; omega) hs hCone hu b

theorem lifted_ancestor_preimage (C : Context) {s u a : Nat}
    (hs : s ≤ C.coordinates.x) (hCone : C.InCone s) (hu : C.floor ≤ u) (b : Nat)
    (ha : (C.row (u+b*C.rise)).Ancestor a (s+b*C.coordinates.length)) :
    ∃ q, (C.mountain.row u).Ancestor q s ∧ a = q+b*C.coordinates.length := by
  have main : ∀ n s, s ≤ C.coordinates.x → C.InCone s → n = s+b*C.coordinates.length →
      ∀ a, (C.row (u+b*C.rise)).Ancestor a n →
        ∃ q, (C.mountain.row u).Ancestor q s ∧ a = q+b*C.coordinates.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro s hs hCone he a ha
        cases ha with
        | direct hp =>
            change C.parent (u+b*C.rise) n = some a at hp
            rw [he, C.parent_lifted_including_root hs hCone hu b] at hp
            obtain ⟨q, hq, hEq⟩ := Option.map_eq_some_iff.mp hp
            exact ⟨q, ParentForest.Ancestor.direct hq, hEq.symm⟩
        | @step p n hPath hp =>
            have hlt := (C.row (u+b*C.rise)).parent_left hp
            change C.parent (u+b*C.rise) n = some p at hp
            rw [he, C.parent_lifted_including_root hs hCone hu b] at hp
            obtain ⟨q, hq, hEq⟩ := Option.map_eq_some_iff.mp hp
            have hqLt := (C.mountain.row u).parent_left hq
            obtain ⟨z, hz, hza⟩ := ih p hlt q (by omega) (C.high_parent_inCone hCone hu hq)
              hEq.symm a hPath
            exact ⟨z, ParentForest.Ancestor.step hz hq, hza⟩
  exact main _ s hs hCone rfl a ha

theorem pseudoCandidate_lifted_iff (C : Context) {s a : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hCone : C.InCone s) (b : Nat) :
    Pseudo.Candidate C.toRowMountain (s+b*C.coordinates.length) a ↔
      ∃ q, Pseudo.Candidate C.mountain s q ∧ a = q+b*C.coordinates.length := by
  have ht := C.height_lt_of_inCone hCone hs
  have hHeight : C.toRowMountain.height (s+b*C.coordinates.length) = C.mountain.height s+b*C.rise := by
    change C.height (C.coordinates.encode s b) = _
    rw [C.height_encode hs hx b, if_pos hCone]
  have hRow : C.mountain.height s+b*C.rise-1 = C.mountain.height s-1+b*C.rise := by omega
  have hu : C.floor ≤ C.mountain.height s-1 := by omega
  constructor
  · rintro ⟨ha, hh⟩
    rw [hHeight, hRow] at ha
    obtain ⟨q, hq, hEq⟩ := C.lifted_ancestor_preimage hx hCone hu b ha
    have hqCone := C.high_ancestor_inCone hu hCone hq
    have hqLt := hq.lt
    have hqHeight : C.toRowMountain.height (q+b*C.coordinates.length) = C.mountain.height q+b*C.rise := by
      change C.height _ = _
      rw [← C.coordinates.parentCopy_bad b (C.root_le_of_inCone hqCone),
        C.height_parentCopy (by omega) b, if_pos hqCone]
    rw [hEq, hqHeight, hHeight] at hh
    exact ⟨q, ⟨hq, by omega⟩, hEq⟩
  · rintro ⟨q, ⟨hq, hh⟩, rfl⟩
    have hqCone := C.high_ancestor_inCone hu hCone hq
    have hqLt := hq.lt
    have hqHeight : C.toRowMountain.height (q+b*C.coordinates.length) = C.mountain.height q+b*C.rise := by
      change C.height _ = _
      rw [← C.coordinates.parentCopy_bad b (C.root_le_of_inCone hqCone),
        C.height_parentCopy (by omega) b, if_pos hqCone]
    constructor
    · rw [hHeight, hRow]
      exact C.lifted_ancestor_copy hu hCone hq hx b
    · rw [hqHeight, hHeight]
      omega

theorem pseudo_parent_lifted (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hCone : C.InCone s) (b : Nat) :
    Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b s) =
      (Pseudo.parent C.mountain s).map (C.coordinates.parentCopy b) := by
  have ht := C.height_lt_of_inCone hCone hs
  rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
  cases hp : Pseudo.parent C.mountain s with
  | none =>
      have := (Pseudo.parent_none_iff C.mountain s).mp hp
      omega
  | some p =>
      have hSpec := (Pseudo.parent_some_iff C.mountain s p).mp hp
      have hpCone := C.high_ancestor_inCone (by omega : C.floor ≤ C.mountain.height s-1) hCone hSpec.2.1.1
      rw [Option.map_some, C.coordinates.parentCopy_bad b (C.root_le_of_inCone hpCone)]
      apply (Pseudo.parent_some_iff C.toRowMountain _ _).mpr
      refine ⟨?_, (C.pseudoCandidate_lifted_iff hs hx hCone b).mpr ⟨p, hSpec.2.1, rfl⟩, ?_⟩
      · change 0 < C.height (C.coordinates.encode s b)
        rw [C.height_encode hs hx b, if_pos hCone]
        omega
      · intro a ha
        obtain ⟨q, hq, he⟩ := (C.pseudoCandidate_lifted_iff hs hx hCone b).mp ha
        have := hSpec.2.2 q hq
        omega

#print axioms lifted_ancestor_preimage
#print axioms pseudo_parent_lifted

end OneY.LowerCopy.Context
