import OneY.OrdinaryCopy

/-! # Computed component roots are preserved by ordinary block copies -/

namespace OneY.OrdinaryCopy.Context

theorem root_parentCopy (C : Context) {c : Nat} (hc : c < C.coordinates.x)
    (b r : Nat) :
    (C.row r).root (C.coordinates.parentCopy b c) =
      C.coordinates.parentCopy b ((C.mountain.row r).root c) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : (C.mountain.row r).parent c with
      | none =>
          have hnew : (C.row r).parent (C.coordinates.parentCopy b c) = none := by
            change C.parent r _ = _
            rw [C.parent_parentCopy hc b r, hp, Option.map_none]
          rw [(C.row r).root_of_parent_none hnew,
            (C.mountain.row r).root_of_parent_none hp]
      | some p =>
          have hleft := (C.mountain.row r).parent_left hp
          have hnew : (C.row r).parent (C.coordinates.parentCopy b c) =
              some (C.coordinates.parentCopy b p) := by
            change C.parent r _ = _
            rw [C.parent_parentCopy hc b r, hp, Option.map_some]
          rw [(C.row r).root_of_parent_some hnew,
            (C.mountain.row r).root_of_parent_some hp]
          exact ih p hleft (by omega)

theorem root_formula (C : Context) (r c : Nat) :
    (C.row r).root c = C.coordinates.parentCopy (C.block0 c)
      ((C.mountain.row r).root (C.source0 c)) := by
  have h := C.root_parentCopy (C.source0_bounds c) (C.block0 c) r
  rw [C.parentCopy_coordinates c] at h
  exact h

theorem rootAt_parentCopy (C : Context) {c : Nat} (hc : c < C.coordinates.x)
    (b r : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.parentCopy b c) =
      C.coordinates.parentCopy b (C.mountain.rootAt r c) :=
  C.root_parentCopy hc b r

theorem topForest_parent_parentCopy (C : Context) {c : Nat} (hc : c < C.coordinates.x)
    (b : Nat) :
    C.toRowMountain.topForest.parent (C.coordinates.parentCopy b c) =
      (C.mountain.topForest.parent c).map (C.coordinates.parentCopy b) := by
  change (if C.height (C.coordinates.parentCopy b c) = 0 then none else
    some (C.toRowMountain.rootAt (C.height (C.coordinates.parentCopy b c)-1)
      (C.coordinates.parentCopy b c))) =
    (if C.mountain.height c = 0 then none else
      some (C.mountain.rootAt (C.mountain.height c-1) c)).map (C.coordinates.parentCopy b)
  rw [C.height_parentCopy hc b, C.rootAt_parentCopy hc b]
  split <;> rfl

theorem topForest_parent_formula (C : Context) (c : Nat) :
    C.toRowMountain.topForest.parent c =
      (C.mountain.topForest.parent (C.source0 c)).map
        (C.coordinates.parentCopy (C.block0 c)) := by
  have h := C.topForest_parent_parentCopy (C.source0_bounds c) (C.block0 c)
  rw [C.parentCopy_coordinates c] at h
  exact h

end OneY.OrdinaryCopy.Context

#print axioms OneY.OrdinaryCopy.Context.root_formula
#print axioms OneY.OrdinaryCopy.Context.topForest_parent_formula
