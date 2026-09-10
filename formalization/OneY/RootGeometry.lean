import OneY.Forest
import OneY.Geometry

/-!
# A mountain interface with computed component roots

The input contains row parent forests, column heights, and local adjacent-row
refinement. All root facts required by `Geometry.Mountain` are proved from
the well-founded `ParentForest.root` computation.
-/

namespace OneY.RootGeometry

structure RowMountain where
  height : Nat → Nat
  row : Nat → ParentForest
  parent_exists : ∀ r c : Nat, r < height c → ∃ p, (row r).parent c = some p
  parent_source : ∀ {r c p : Nat}, (row r).parent c = some p → r < height c
  parent_endpoint : ∀ {r c p : Nat}, (row r).parent c = some p → r ≤ height p
  nested_succ : ∀ r : Nat, (row (r + 1)).Refines (row r)

namespace RowMountain

def rootAt (M : RowMountain) (r c : Nat) : Nat := (M.row r).root c

theorem rootAt_le (M : RowMountain) (r c : Nat) : M.rootAt r c ≤ c :=
  (M.row r).root_le c

theorem parent_rootAt (M : RowMountain) (r c : Nat) :
    (M.row r).parent (M.rootAt r c) = none :=
  (M.row r).parent_root c

theorem rootAt_of_parent (M : RowMountain) {r c p : Nat}
    (hp : (M.row r).parent c = some p) : M.rootAt r c = M.rootAt r p :=
  (M.row r).root_of_parent_some hp

theorem parent_none_iff (M : RowMountain) (r c : Nat) :
    (M.row r).parent c = none ↔ M.height c ≤ r := by
  constructor
  · intro hp
    by_cases h : r < M.height c
    · obtain ⟨p, hp'⟩ := M.parent_exists r c h
      have hfalse : (none : Option Nat) = some p := hp.symm.trans hp'
      cases hfalse
    · omega
  · intro hh
    cases hp : (M.row r).parent c with
    | none => rfl
    | some p => have := M.parent_source hp
                omega

theorem top_root (M : RowMountain) (c : Nat) : M.rootAt (M.height c) c = c := by
  exact (M.row (M.height c)).root_of_parent_none
    ((M.parent_none_iff _ _).mpr (Nat.le_refl _))

theorem refines_le (M : RowMountain) {h r : Nat} (hle : h ≤ r) :
    (M.row r).Refines (M.row h) := by
  have aux : ∀ gap : Nat, (M.row (h + gap)).Refines (M.row h) := by
    intro gap
    induction gap with
    | zero => exact ParentForest.refines_refl (M.row h)
    | succ gap ih =>
        exact ParentForest.Refines.trans (M.nested_succ (h + gap)) ih
  have heq : h + (r - h) = r := Nat.add_sub_of_le hle
  rw [← heq]
  intro c p hp
  exact aux (r - h) hp

theorem nested_roots (M : RowMountain) {h r c p : Nat} (hle : h ≤ r)
    (hp : (M.row r).parent c = some p) : M.rootAt h c = M.rootAt h p :=
  ParentForest.Refines.root_eq_of_parent (M.refines_le hle) hp

theorem rootAt_rootAt (M : RowMountain) {h r : Nat} (hle : h ≤ r) (c : Nat) :
    M.rootAt h (M.rootAt r c) = M.rootAt h c :=
  ParentForest.Refines.root_root (M.refines_le hle) c

theorem root_height (M : RowMountain) {r c : Nat} (hc : r ≤ M.height c) :
    M.height (M.rootAt r c) = r := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : (M.row r).parent c with
      | none =>
          have hh := (M.parent_none_iff r c).mp hp
          have hr : M.rootAt r c = c := (M.row r).root_of_parent_none hp
          rw [hr]
          omega
      | some p =>
          rw [M.rootAt_of_parent hp]
          exact ih p ((M.row r).parent_left hp) (M.parent_endpoint hp)

theorem rootAt_lt (M : RowMountain) {r c : Nat} (hc : r < M.height c) :
    M.rootAt r c < c := by
  obtain ⟨p, hp⟩ := M.parent_exists r c hc
  exact (M.row r).root_lt_of_parent_some hp

theorem rootAt_strict_mono (M : RowMountain) {h r c : Nat}
    (hhr : h < r) (hrc : r ≤ M.height c) : M.rootAt h c < M.rootAt r c := by
  have hheight := M.root_height hrc
  have hlt : h < M.height (M.rootAt r c) := by omega
  have hroot := M.rootAt_lt hlt
  rw [M.rootAt_rootAt (Nat.le_of_lt hhr) c] at hroot
  exact hroot

theorem rootAt_eq_iff_path (M : RowMountain) {r q c : Nat}
    (hq : M.height q = r) :
    M.rootAt r c = q ↔ (M.row r).Ancestor q c ∨ q = c := by
  constructor
  · intro h
    change (M.row r).root c = q at h
    simpa only [h] using (M.row r).root_ancestor_or_eq c
  · intro h
    exact (M.row r).root_unique
      ((M.parent_none_iff r q).mpr (by omega)) h

/-- The next lower top on the computed vertical chain of row roots. -/
def topForest (M : RowMountain) : ParentForest where
  parent := fun c =>
    if M.height c = 0 then none else some (M.rootAt (M.height c - 1) c)
  parent_left := by
    intro c p hp
    by_cases hz : M.height c = 0
    · simp only [hz, if_pos] at hp
      cases hp
    · rw [if_neg hz] at hp
      have heq := Option.some.inj hp
      rw [← heq]
      exact M.rootAt_lt (by omega)

theorem topForest_parent_some_iff (M : RowMountain) (c p : Nat) :
    M.topForest.parent c = some p ↔
      0 < M.height c ∧ M.rootAt (M.height c - 1) c = p := by
  change (if M.height c = 0 then none else some (M.rootAt (M.height c - 1) c)) = some p ↔ _
  by_cases hz : M.height c = 0
  · simp [hz]
  · rw [if_neg hz, Option.some.injEq]
    constructor
    · intro hp
      exact ⟨by omega, hp⟩
    · exact And.right

theorem topForest_parent_none_iff (M : RowMountain) (c : Nat) :
    M.topForest.parent c = none ↔ M.height c = 0 := by
  change (if M.height c = 0 then none else some (M.rootAt (M.height c - 1) c)) = none ↔ _
  by_cases hz : M.height c = 0 <;> simp [hz]

theorem topForest_parent_height (M : RowMountain) {c p : Nat}
    (hp : M.topForest.parent c = some p) : M.height p + 1 = M.height c := by
  obtain ⟨hpos, heq⟩ := (M.topForest_parent_some_iff c p).mp hp
  have hh := M.root_height (c := c) (r := M.height c - 1) (by omega)
  rw [heq] at hh
  omega

theorem topForest_parent_root (M : RowMountain) {c p : Nat}
    (hp : M.topForest.parent c = some p) : M.rootAt (M.height p) c = p := by
  obtain ⟨_, heq⟩ := (M.topForest_parent_some_iff c p).mp hp
  have hh := M.topForest_parent_height hp
  have hr : M.height p = M.height c - 1 := by omega
  simpa only [hr] using heq

theorem topForest_depth (M : RowMountain) (c : Nat) :
    M.topForest.depth c = M.height c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : M.topForest.parent c with
      | none =>
          rw [M.topForest.depth_of_parent_none hp]
          exact ((M.topForest_parent_none_iff c).mp hp).symm
      | some p =>
          rw [M.topForest.depth_of_parent_some hp, ih p (M.topForest.parent_left hp)]
          exact M.topForest_parent_height hp

/-- The former geometric root assumptions are discharged by computation. -/
def toMountain (M : RowMountain) : Geometry.Mountain where
  height := M.height
  parent := fun r => (M.row r).parent
  rootAt := M.rootAt
  parent_exists := M.parent_exists
  parent_left := fun hp => (M.row _).parent_left hp
  parent_endpoint := M.parent_endpoint
  parent_source := M.parent_source
  top_root := M.top_root
  nested_roots := M.nested_roots

theorem vertex_iff (M : RowMountain) (y c : Nat) :
    Geometry.Reach M.toMountain y (M.height c) c ↔
      M.height y ≤ M.height c ∧ M.rootAt (M.height y) c = y :=
  Geometry.vertex_iff_cone M.toMountain y c

theorem contour_iff (M : RowMountain) (y r c : Nat) :
    Geometry.Contour M.toMountain y r c ↔
      r < M.height c ∧ M.height y ≤ r ∧
        (M.height y ≤ M.height c ∧ M.rootAt (M.height y) c = y) :=
  Geometry.contour_iff M.toMountain y r c

end RowMountain

end OneY.RootGeometry

#print axioms OneY.RootGeometry.RowMountain.root_height
#print axioms OneY.RootGeometry.RowMountain.nested_roots
#print axioms OneY.RootGeometry.RowMountain.vertex_iff
#print axioms OneY.RootGeometry.RowMountain.contour_iff
#print axioms OneY.RootGeometry.RowMountain.rootAt_strict_mono
#print axioms OneY.RootGeometry.RowMountain.topForest_depth
