import OneY.TerminalCopyReconstruction
import OneY.OrdinaryCopyRoots
import OneY.OrdinaryCopyExtraction

/-!
# Computed component roots of the active finite copy

Low-row paths may cross several seams. Their component roots nevertheless
follow ordinary copying: the extra seam path has the same old component root.
The proof uses the actual recursively computed roots, not a root field.
-/

namespace OneY.TerminalCopy.Context

theorem ancestor_parentCopy (C : Context) {r a c : Nat}
    (ha : (C.mountain.row r).Ancestor a c) (hc : c < C.coordinates.x)
    (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a)
      (C.coordinates.parentCopy b c) := by
  by_cases hr : r < C.level
  · exact C.low_ancestor_copy hr ha (Nat.le_of_lt hc) b
  · exact C.high_ancestor_copy (by omega) ha hc b

theorem root_parentCopy (C : Context) {c : Nat} (hc : c < C.coordinates.x)
    (b r : Nat) :
    (C.row r).root (C.coordinates.parentCopy b c) =
      C.coordinates.parentCopy b ((C.mountain.row r).root c) := by
  let q := (C.mountain.row r).root c
  have hqle : q ≤ c := (C.mountain.row r).root_le c
  have hqnone : (C.mountain.row r).parent q = none :=
    (C.mountain.row r).parent_root c
  have hqh : C.mountain.height q ≤ r :=
    (C.mountain.parent_none_iff r q).mp hqnone
  have hnewnone : (C.row r).parent (C.coordinates.parentCopy b q) = none := by
    apply (C.toRowMountain.parent_none_iff r _).mpr
    change C.height (C.coordinates.parentCopy b q) ≤ r
    rw [C.height_parentCopy (by omega : q < C.coordinates.x) b]
    exact hqh
  apply (C.row r).root_unique hnewnone
  rcases (C.mountain.row r).root_ancestor_or_eq c with ha | he
  · exact Or.inl (C.ancestor_parentCopy ha hc b)
  · exact Or.inr (congrArg (C.coordinates.parentCopy b) he)

theorem root_formula (C : Context) (r c : Nat) :
    (C.row r).root c = C.coordinates.parentCopy (C.ordinaryContext.block0 c)
      ((C.mountain.row r).root (C.ordinaryContext.source0 c)) := by
  have h := C.root_parentCopy (C.ordinaryContext.source0_bounds c)
    (C.ordinaryContext.block0 c) r
  have he := C.ordinaryContext.parentCopy_coordinates c
  change C.coordinates.parentCopy (C.ordinaryContext.block0 c)
    (C.ordinaryContext.source0 c) = c at he
  rw [he] at h
  exact h

theorem root_eq_ordinary (C : Context) (r c : Nat) :
    (C.row r).root c = (C.ordinaryContext.row r).root c := by
  rw [C.root_formula, C.ordinaryContext.root_formula]
  rfl

theorem rootAt_parentCopy (C : Context) {c : Nat}
    (hc : c < C.coordinates.x) (b r : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.parentCopy b c) =
      C.coordinates.parentCopy b (C.mountain.rootAt r c) :=
  C.root_parentCopy hc b r

theorem topForest_eq_ordinary (C : Context) :
    C.toRowMountain.topForest = C.ordinaryContext.toRowMountain.topForest := by
  apply ParentForest.ext_parent
  funext c
  change (if C.height c = 0 then none else some ((C.row (C.height c-1)).root c)) =
    (if C.ordinaryContext.height c = 0 then none else
      some ((C.ordinaryContext.row (C.ordinaryContext.height c-1)).root c))
  rw [C.height_eq_ordinary, C.root_eq_ordinary]

theorem topForest_parent_formula (C : Context) (c : Nat) :
    C.toRowMountain.topForest.parent c =
      (C.mountain.topForest.parent (C.ordinaryContext.source0 c)).map
        (C.coordinates.parentCopy (C.ordinaryContext.block0 c)) := by
  rw [C.topForest_eq_ordinary]
  exact C.ordinaryContext.topForest_parent_formula c

end OneY.TerminalCopy.Context

#print axioms OneY.TerminalCopy.Context.root_formula
#print axioms OneY.TerminalCopy.Context.topForest_eq_ordinary
