import OneY.OrdinaryCopyNumeric
import OneY.Pseudo

/-! # The actual pseudo-parent computation commutes with ordinary copying -/

namespace OneY.OrdinaryCopy.Context

theorem pseudoCandidate_parentCopy_iff (C : Context) {c a : Nat}
    (hc : c < C.coordinates.x) (b : Nat) :
    Pseudo.Candidate C.toRowMountain (C.coordinates.parentCopy b c) a ↔
      ∃ q, Pseudo.Candidate C.mountain c q ∧ a = C.coordinates.parentCopy b q := by
  constructor
  · rintro ⟨ha, hh⟩
    change (C.row (C.height (C.coordinates.parentCopy b c)-1)).Ancestor a
      (C.coordinates.parentCopy b c) at ha
    rw [C.height_parentCopy hc b] at ha
    obtain ⟨q, hq, heq⟩ := (C.ancestor_parentCopy_iff hc b).mp ha
    have hleft := hq.lt
    have hqbound : q < C.coordinates.x := by omega
    change C.height a = C.height (C.coordinates.parentCopy b c) ∨
      C.height a+1 = C.height (C.coordinates.parentCopy b c) at hh
    rw [heq, C.height_parentCopy hqbound b, C.height_parentCopy hc b] at hh
    exact ⟨q, ⟨hq, hh⟩, heq⟩
  · rintro ⟨q, ⟨ha, hh⟩, rfl⟩
    have hleft := ha.lt
    have hqbound : q < C.coordinates.x := by omega
    constructor
    · change (C.row (C.height (C.coordinates.parentCopy b c)-1)).Ancestor
        (C.coordinates.parentCopy b q) (C.coordinates.parentCopy b c)
      rw [C.height_parentCopy hc b]
      exact C.ancestor_copy ha hc b
    · change C.height (C.coordinates.parentCopy b q) = C.height (C.coordinates.parentCopy b c) ∨
        C.height (C.coordinates.parentCopy b q)+1 = C.height (C.coordinates.parentCopy b c)
      rw [C.height_parentCopy hqbound b, C.height_parentCopy hc b]
      exact hh

theorem pseudo_parent_parentCopy (C : Context) {c : Nat}
    (hc : c < C.coordinates.x) (b : Nat) :
    Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b c) =
      (Pseudo.parent C.mountain c).map (C.coordinates.parentCopy b) := by
  cases hp : Pseudo.parent C.mountain c with
  | none =>
      simp only [Option.map_none]
      apply (Pseudo.parent_none_iff C.toRowMountain _).mpr
      change C.height (C.coordinates.parentCopy b c) = 0
      rw [C.height_parentCopy hc b]
      exact (Pseudo.parent_none_iff C.mountain c).mp hp
  | some p =>
      simp only [Option.map_some]
      obtain ⟨hpos, hpc, hmax⟩ := (Pseudo.parent_some_iff C.mountain c p).mp hp
      apply (Pseudo.parent_some_iff C.toRowMountain
        (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b p)).mpr
      refine ⟨?_, (C.pseudoCandidate_parentCopy_iff hc b).mpr ⟨p, hpc, rfl⟩, ?_⟩
      · change 0 < C.height (C.coordinates.parentCopy b c)
        rw [C.height_parentCopy hc b]
        exact hpos
      · intro a ha
        obtain ⟨q, hq, heq⟩ := (C.pseudoCandidate_parentCopy_iff hc b).mp ha
        rw [heq, C.parentCopy_le_iff]
        exact hmax q hq

theorem pseudo_parent_formula (C : Context) (c : Nat) :
    Pseudo.parent C.toRowMountain c =
      (Pseudo.parent C.mountain (C.source0 c)).map
        (C.coordinates.parentCopy (C.block0 c)) := by
  have h := C.pseudo_parent_parentCopy (C.source0_bounds c) (C.block0 c)
  rw [C.parentCopy_coordinates c] at h
  exact h

end OneY.OrdinaryCopy.Context

#print axioms OneY.OrdinaryCopy.Context.pseudoCandidate_parentCopy_iff
#print axioms OneY.OrdinaryCopy.Context.pseudo_parent_formula
