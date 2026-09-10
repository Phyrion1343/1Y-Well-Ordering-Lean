import OneY.RootGeometry
import OneY.PseudoSelection

/-!
# Vertices and the computed forest of column tops

The top forest visits exactly one component root at each lower height.
Thus its ancestor relation is precisely the geometric vertex relation.
-/

namespace OneY.RootGeometry.RowMountain

theorem topForest_ancestor_spec (M : RowMountain) {a c : Nat}
    (ha : M.topForest.Ancestor a c) :
    M.height a < M.height c ∧ M.rootAt (M.height a) c = a := by
  induction ha with
  | direct hp =>
      have hh := M.topForest_parent_height hp
      exact ⟨by omega, M.topForest_parent_root hp⟩
  | @step p c _ hp ih =>
      have hh := M.topForest_parent_height hp
      have hroot := M.topForest_parent_root hp
      have hnested := M.rootAt_rootAt (Nat.le_of_lt ih.1) c
      rw [hroot] at hnested
      exact ⟨by omega, hnested.symm.trans ih.2⟩

theorem topForest_ancestor_of_rootAt (M : RowMountain) {a c : Nat}
    (hh : M.height a < M.height c) (hr : M.rootAt (M.height a) c = a) :
    M.topForest.Ancestor a c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : M.topForest.parent c with
      | none =>
          have hz := (M.topForest_parent_none_iff c).mp hp
          omega
      | some p =>
          have hheight := M.topForest_parent_height hp
          have hroot := M.topForest_parent_root hp
          by_cases heq : M.height a = M.height p
          · have hap : a = p := by rw [heq, hroot] at hr; exact hr.symm
            subst a
            exact ParentForest.Ancestor.direct hp
          · have hlt : M.height a < M.height p := by omega
            have hnested := M.rootAt_rootAt (Nat.le_of_lt hlt) c
            rw [hroot, hr] at hnested
            exact ParentForest.Ancestor.step
              (ih p (M.topForest.parent_left hp) hlt hnested) hp

theorem topForest_ancestor_iff (M : RowMountain) (a c : Nat) :
    M.topForest.Ancestor a c ↔
      M.height a < M.height c ∧ M.rootAt (M.height a) c = a :=
  ⟨M.topForest_ancestor_spec, fun ⟨hh, hr⟩ => M.topForest_ancestor_of_rootAt hh hr⟩

theorem topForest_ancestor_or_eq_iff (M : RowMountain) (a c : Nat) :
    (M.topForest.Ancestor a c ∨ a = c) ↔
      M.height a ≤ M.height c ∧ M.rootAt (M.height a) c = a := by
  constructor
  · rintro (ha | rfl)
    · have hs := M.topForest_ancestor_spec ha
      exact ⟨Nat.le_of_lt hs.1, hs.2⟩
    · exact ⟨Nat.le_refl _, M.top_root _⟩
  · rintro ⟨hh, hr⟩
    by_cases heq : M.height a = M.height c
    · right
      rw [heq, M.top_root] at hr
      exact hr.symm
    · left
      exact M.topForest_ancestor_of_rootAt (by omega) hr

theorem vertex_iff_topForest (M : RowMountain) (y c : Nat) :
    Geometry.Reach M.toMountain y (M.height c) c ↔
      M.topForest.Ancestor y c ∨ y = c := by
  rw [M.vertex_iff, M.topForest_ancestor_or_eq_iff]

theorem contour_iff_topForest (M : RowMountain) (y r c : Nat) :
    Geometry.Contour M.toMountain y r c ↔
      r < M.height c ∧ M.height y ≤ r ∧
        (M.topForest.Ancestor y c ∨ y = c) := by
  rw [M.contour_iff, M.topForest_ancestor_or_eq_iff]

end OneY.RootGeometry.RowMountain

namespace OneY.Numeric

theorem rawExtract_ancestor_rootAt (base : Row) (hpos : ∀ c, 0 < base.value c)
    {a c : Nat} (ha : (rawExtract base hpos).forest.Ancestor a c) :
    height base a < height base c ∧
      (rows base (height base a)).forest.root c = a := by
  exact (mountain base hpos).topForest_ancestor_spec
    (ParentForest.Refines.ancestor (rawExtract_refines_topForest base hpos) ha)

theorem rawExtract_ancestor_vertex (base : Row) (hpos : ∀ c, 0 < base.value c)
    {a c : Nat} (ha : (rawExtract base hpos).forest.Ancestor a c) :
    Geometry.Reach (geometry base hpos) a (height base c) c :=
  ((mountain base hpos).vertex_iff_topForest a c).mpr
    (Or.inl (ParentForest.Refines.ancestor
      (rawExtract_refines_topForest base hpos) ha))

end OneY.Numeric

#print axioms OneY.RootGeometry.RowMountain.topForest_ancestor_iff
#print axioms OneY.RootGeometry.RowMountain.vertex_iff_topForest
#print axioms OneY.Numeric.rawExtract_ancestor_rootAt
#print axioms OneY.Numeric.rawExtract_ancestor_vertex
