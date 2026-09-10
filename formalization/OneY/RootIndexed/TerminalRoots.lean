import OneY.TerminalCopyNesting
import OneY.Prefix

/-! # Computed row roots at active-layer seams -/

namespace OneY.TerminalCopy.Context

theorem rootAt_low_parentCopy (C : Context) {r c : Nat}
    (hr : r < C.level) (hc : c ≤ C.coordinates.x) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.parentCopy b c) =
      C.coordinates.parentCopy b (C.mountain.rootAt r c) := by
  let q := C.mountain.rootAt r c
  have hqle : q ≤ C.coordinates.x := Nat.le_trans (C.mountain.rootAt_le r c) hc
  have hqnone : (C.mountain.row r).parent q = none := C.mountain.parent_rootAt r c
  have hqheight : C.mountain.height q ≤ r := (C.mountain.parent_none_iff r q).mp hqnone
  have hyheight : C.level ≤ C.mountain.height C.coordinates.y :=
    C.mountain.parent_endpoint C.last_parent
  have hqney : q ≠ C.coordinates.y := by intro he; rw [he] at hqheight; omega
  apply (C.row r).root_unique
  · change C.parent r (C.coordinates.parentCopy b q) = none
    by_cases hgood : q < C.coordinates.y
    · rw [C.coordinates.parentCopy_good b hgood,
        C.parent_original (by have := C.coordinates.root_lt_last; omega) r]
      exact hqnone
    · have hafter : C.coordinates.y < q := by omega
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hafter)]
      change C.parent r (C.coordinates.encode q b) = none
      rw [C.parent_encode_low hafter hqle hr b, hqnone, Option.map_none]
  · rcases (C.mountain.row r).root_ancestor_or_eq c with ha | he
    · exact Or.inl (C.low_ancestor_copy hr ha hc b)
    · exact Or.inr (congrArg (C.coordinates.parentCopy b) he)

theorem rootAt_low_last (C : Context) {r : Nat} (hr : r < C.level) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.encode C.coordinates.x b) =
      C.mountain.rootAt r C.coordinates.x := by
  have hcontrol : C.mountain.rootAt C.level C.coordinates.x ≤ C.coordinates.y := by
    rw [C.mountain.rootAt_of_parent C.last_parent]
    exact C.mountain.rootAt_le _ _
  have hlive : C.level ≤ C.mountain.height C.coordinates.x := by
    have := C.mountain.parent_source C.last_parent
    omega
  have hrootlt := C.mountain.rootAt_strict_mono hr hlive
  have hqgood : C.mountain.rootAt r C.coordinates.x < C.coordinates.y := by omega
  have h := C.rootAt_low_parentCopy hr (Nat.le_refl _) b
  rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last),
    C.coordinates.parentCopy_good b hqgood] at h
  exact h

theorem rootAt_low_last_lt_control (C : Context) {r : Nat}
    (hr : r < C.level) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.encode C.coordinates.x b) <
      C.mountain.rootAt C.level C.coordinates.x := by
  rw [C.rootAt_low_last hr b]
  apply C.mountain.rootAt_strict_mono hr
  exact Nat.le_of_lt (C.mountain.parent_source C.last_parent)

end OneY.TerminalCopy.Context

#print axioms OneY.TerminalCopy.Context.rootAt_low_last_lt_control
