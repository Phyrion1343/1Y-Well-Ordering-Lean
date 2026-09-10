import OneY.ForestBridge
import ZeroY.Forest.Blocker
import ZeroY.Forest.MatrixParents

/-!
# A finite depth frame for an arbitrary leftward forest

At cutoff k, columns strictly below k retain the linear predecessor and
columns at or above k use the given forest. Lowering k by one changes only
that column. Its old candidate chain is still linear, so its new depth
selects exactly the desired parent. The other columns select their unchanged
direct parent. This proves depth regularity; it does not assert blocker S.
-/

namespace OneY.ParentForest

theorem nearestSmaller_depth_parent (F : ParentForest) (c : Nat) :
    (F.nearestSmaller F.depth).parent c = F.parent c := by
  change ZeroY.Forest.nearestSmaller F.parent F.depth c = F.parent c
  cases hp : F.parent c with
  | none =>
      apply (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mpr
      intro p ha
      have hdepth := F.depth_of_parent_none hp
      omega
  | some p =>
      apply ZeroY.Forest.nearestSmaller_eq_of_direct F.parent_left hp
      rw [F.depth_of_parent_some hp]
      omega

end OneY.ParentForest

namespace OneY.ForestFrame

def cutoff (F : ParentForest) (k : Nat) : ParentForest where
  parent c := if c < k then ZeroY.linearParent c else F.parent c
  parent_left := by
    intro c p hp
    split at hp
    · exact ZeroY.linearParent_leftward hp
    · exact F.parent_left hp

theorem cutoff_parent_before (F : ParentForest) {k c : Nat} (hc : c < k) :
    (cutoff F k).parent c = ZeroY.linearParent c := by
  simp only [cutoff, if_pos hc]

theorem cutoff_parent_after (F : ParentForest) {k c : Nat} (hc : k ≤ c) :
    (cutoff F k).parent c = F.parent c := by
  simp only [cutoff, if_neg (by omega : ¬ c < k)]

theorem cutoff_depth_before (F : ParentForest) {k c : Nat} (hc : c < k) :
    (cutoff F k).depth c = c := by
  induction c with
  | zero =>
      apply (cutoff F k).depth_of_parent_none
      rw [cutoff_parent_before F hc]
      rfl
  | succ c ih =>
      have hp : (cutoff F k).parent (c+1) = some c := by
        rw [cutoff_parent_before F hc]
        rfl
      rw [(cutoff F k).depth_of_parent_some hp, ih (by omega)]

theorem cutoff_ancestor_before (F : ParentForest) {k a c : Nat}
    (hc : c < k) (ha : a < c) : (cutoff F k).Ancestor a c := by
  apply ParentForest.ancestor_of_zeroY
  exact ZeroY.Forest.ancestor_transfer_prefix ZeroY.linearParent_leftward hc
    (fun q hq => (cutoff_parent_before F hq).symm)
    (ZeroY.linearParent_ancestor_of_lt ha)

theorem cutoff_step_other (F : ParentForest) (k : Nat) {c : Nat} (hc : c ≠ k) :
    (cutoff F (k+1)).parent c = (cutoff F k).parent c := by
  by_cases hlt : c < k
  · rw [cutoff_parent_before F (by omega : c < k+1), cutoff_parent_before F hlt]
  · rw [cutoff_parent_after F (by omega : k+1 ≤ c), cutoff_parent_after F (by omega : k ≤ c)]

/-- One descending cutoff step is exactly nearest-smaller selection on the
new computed depths, over the old candidate forest. -/
theorem cutoff_step_nearestSmaller (F : ParentForest) (k c : Nat) :
    ((cutoff F (k+1)).nearestSmaller (cutoff F k).depth).parent c =
      (cutoff F k).parent c := by
  change ZeroY.Forest.nearestSmaller (cutoff F (k+1)).parent
    (cutoff F k).depth c = (cutoff F k).parent c
  by_cases hcritical : c = k
  · subst c
    rw [cutoff_parent_after F (Nat.le_refl k)]
    cases hp : F.parent k with
    | none =>
        apply (ZeroY.Forest.nearestSmaller_none_iff (cutoff F (k+1)).parent_left).mpr
        intro p ha
        have hz : (cutoff F k).depth k = 0 :=
          (cutoff F k).depth_of_parent_none
            ((cutoff_parent_after F (Nat.le_refl k)).trans hp)
        omega
    | some p =>
        have hpk := F.parent_left hp
        have hv : (cutoff F k).depth k = p+1 := by
          rw [(cutoff F k).depth_of_parent_some
            ((cutoff_parent_after F (Nat.le_refl k)).trans hp), cutoff_depth_before F hpk]
        apply (ZeroY.Forest.nearestSmaller_some_iff (cutoff F (k+1)).parent_left).mpr
        refine ⟨ParentForest.ancestor_to_zeroY
          (cutoff_ancestor_before F (Nat.lt_succ_self k) hpk), ?_, ?_⟩
        · rw [hv, cutoff_depth_before F hpk]
          omega
        · intro q hq hval
          have hqk := ZeroY.Forest.ancestor_lt (cutoff F (k+1)).parent_left hq
          rw [hv, cutoff_depth_before F hqk] at hval
          omega
  · have he := cutoff_step_other F k hcritical
    cases hp : (cutoff F k).parent c with
    | none =>
        apply (ZeroY.Forest.nearestSmaller_none_iff (cutoff F (k+1)).parent_left).mpr
        intro p ha
        have hz := (cutoff F k).depth_of_parent_none hp
        omega
    | some p =>
        apply ZeroY.Forest.nearestSmaller_eq_of_direct (cutoff F (k+1)).parent_left (he.trans hp)
        rw [(cutoff F k).depth_of_parent_some hp]
        omega

def rowForest (F : ParentForest) (width r : Nat) : ParentForest :=
  cutoff F (width-r)

theorem rowForest_initial_parent (F : ParentForest) {width c : Nat} (hc : c < width) :
    (rowForest F width 0).parent c = ZeroY.linearParent c :=
  cutoff_parent_before F (by omega : c < width-0)

theorem rowForest_initial_depth (F : ParentForest) {width c : Nat} (hc : c < width) :
    (rowForest F width 0).depth c = c :=
  cutoff_depth_before F (by omega : c < width-0)

theorem rowForest_terminal_parent (F : ParentForest) (width c : Nat) :
    (rowForest F width width).parent c = F.parent c :=
  cutoff_parent_after F (by omega : width-width ≤ c)

theorem rowForest_step (F : ParentForest) (width r c : Nat) :
    ((rowForest F width r).nearestSmaller (rowForest F width (r+1)).depth).parent c =
      (rowForest F width (r+1)).parent c := by
  by_cases hr : r < width
  · have he : width-r = (width-(r+1))+1 := by omega
    change ((cutoff F (width-r)).nearestSmaller (cutoff F (width-(r+1))).depth).parent c =
      (cutoff F (width-(r+1))).parent c
    rw [he]
    exact cutoff_step_nearestSmaller F (width-(r+1)) c
  · have he : width-r = 0 := by omega
    have hn : width-(r+1) = 0 := by omega
    change ((cutoff F (width-r)).nearestSmaller (cutoff F (width-(r+1))).depth).parent c =
      (cutoff F (width-(r+1))).parent c
    rw [he, hn]
    exact (cutoff F 0).nearestSmaller_depth_parent c

end OneY.ForestFrame

#print axioms OneY.ForestFrame.cutoff_step_nearestSmaller
#print axioms OneY.ForestFrame.rowForest_step
