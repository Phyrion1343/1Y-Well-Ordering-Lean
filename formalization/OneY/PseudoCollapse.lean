import OneY.Pseudo

/-!
# Contracting the equal-height pseudo-parent edges

The first strict height drop on a pseudo-parent chain is exactly the next
computed row root. This identifies the top forest without assuming a root
map or assuming the correctness of the contraction.
-/

namespace OneY.Pseudo

open RootGeometry

theorem topForest_parent_of_height_drop (M : RowMountain) {c p : Nat}
    (hp : parent M c = some p) (hlt : M.height p < M.height c) :
    M.topForest.parent c = some p := by
  have hc := ((parent_some_iff M c p).mp hp).1
  have hh := parent_height M hp
  have he : M.height p = M.height c - 1 := by omega
  apply (M.topForest_parent_some_iff c p).mpr
  refine ⟨hc, ?_⟩
  change (M.row (M.height c - 1)).root c = p
  apply (M.row (M.height c - 1)).root_unique
  · apply (M.parent_none_iff _ _).mpr
    omega
  · exact Or.inl (parent_ancestor M hp)

theorem topForest_parent_of_same_height (M : RowMountain) {c p : Nat}
    (hp : parent M c = some p) (heq : M.height p = M.height c) :
    M.topForest.parent c = M.topForest.parent p := by
  have he := ParentForest.root_eq_of_ancestor (parent_ancestor M hp)
  change M.rootAt (M.height c - 1) c = M.rootAt (M.height c - 1) p at he
  change (if M.height c = 0 then none else some (M.rootAt (M.height c - 1) c)) =
    (if M.height p = 0 then none else some (M.rootAt (M.height p - 1) p))
  rw [heq, he]

/-- An executable search down the pseudo-parent chain, skipping exactly
the edges whose endpoints have equal heights. -/
def lowerParent (M : RowMountain) (c : Nat) : Option Nat :=
  match _hp : parent M c with
  | none => none
  | some p => if M.height p < M.height c then some p else lowerParent M p
termination_by c
decreasing_by exact parent_left M _hp

theorem lowerParent_of_none (M : RowMountain) {c : Nat}
    (hp : parent M c = none) : lowerParent M c = none := by
  rw [lowerParent]
  split <;> simp_all

theorem lowerParent_of_some (M : RowMountain) {c p : Nat}
    (hp : parent M c = some p) :
    lowerParent M c =
      if M.height p < M.height c then some p else lowerParent M p := by
  rw [lowerParent]
  split <;> simp_all

theorem lowerParent_eq_topForest (M : RowMountain) (c : Nat) :
    lowerParent M c = M.topForest.parent c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : parent M c with
      | none =>
          rw [lowerParent_of_none M hp]
          exact ((M.topForest_parent_none_iff c).mpr
            ((parent_none_iff M c).mp hp)).symm
      | some p =>
          rw [lowerParent_of_some M hp]
          by_cases hlt : M.height p < M.height c
          · rw [if_pos hlt]
            exact (topForest_parent_of_height_drop M hp hlt).symm
          · rw [if_neg hlt, ih p (parent_left M hp)]
            have hh := parent_height M hp
            exact (topForest_parent_of_same_height M hp (by omega)).symm

theorem lowerParent_some_height (M : RowMountain) {c p : Nat}
    (hp : lowerParent M c = some p) : M.height p + 1 = M.height c := by
  rw [lowerParent_eq_topForest] at hp
  exact M.topForest_parent_height hp

theorem lowerParent_none_iff (M : RowMountain) (c : Nat) :
    lowerParent M c = none ↔ M.height c = 0 := by
  rw [lowerParent_eq_topForest, M.topForest_parent_none_iff]

end OneY.Pseudo

#print axioms OneY.Pseudo.lowerParent_eq_topForest
#print axioms OneY.Pseudo.lowerParent_some_height
