import OneY.SparseBlocker
import OneY.NumericRoots

/-!
# Depth regularity of actual sparse difference rows

Replacing zeros by a sentinel is harmless when every zero lies at a root
of the candidate forest. Difference rows have exactly this property.
Thus the old dense nearest-smaller depth invariant applies to their actual
sparse parent graph, including empty cells.
-/

namespace OneY.Numeric

theorem nearestSmaller_none_of_parent_none (F : ParentForest) (v : Nat → Nat)
    {c : Nat} (hc : F.parent c = none) :
    ZeroY.Forest.nearestSmaller F.parent v c = none := by
  apply (ZeroY.Forest.nearestSmaller_none_iff F.parent_left).mpr
  intro p ha
  have h := ParentForest.ancestor_of_zeroY ha
  cases h with
  | direct hp => rw [hc] at hp; contradiction
  | step _ hp => rw [hc] at hp; contradiction

theorem select_depth_eq_filled_of_root_zeros (F : ParentForest) (v : Nat → Nat)
    (hzero : ∀ c, v c = 0 → F.parent c = none) {cap c : Nat}
    (hcap : v c ≤ cap) :
    (select F v).forest.depth c =
      ZeroY.parentDepth (ZeroY.Forest.nearestSmaller F.parent (filledValue cap v)) c := by
  by_cases hz : v c = 0
  · have hs : (select F v).forest.parent c = none := by
      apply (restrictedParent_none_iff F v c).mpr
      intro p ha hp
      change v c ≤ v p
      omega
    rw [(select F v).forest.depth_of_parent_none hs,
      ZeroY.Forest.parentDepth_none
        (nearestSmaller_none_of_parent_none F (filledValue cap v) (hzero c hz))]
  · exact select_depth_eq_filled_depth F v cap (by omega) hcap

/-- Actual sparse selection is recovered by dense nearest-smaller selection
on its computed depths, whenever missing values occur only at candidate roots. -/
theorem select_depth_nearestSmaller (F : ParentForest) (v : Nat → Nat)
    (hzero : ∀ c, v c = 0 → F.parent c = none) (c : Nat) :
    ZeroY.Forest.nearestSmaller F.parent (select F v).forest.depth c =
      (select F v).forest.parent c := by
  obtain ⟨cap, hcap⟩ := exists_value_cap v c
  rw [ZeroY.Forest.nearestSmaller_congr_below
    (fun q hq => select_depth_eq_filled_of_root_zeros F v hzero (hcap q hq)),
    ZeroY.Forest.nearestSmaller_depth_invariant F.parent_left]
  by_cases hz : v c = 0
  · rw [nearestSmaller_none_of_parent_none F (filledValue cap v) (hzero c hz)]
    symm
    apply (restrictedParent_none_iff F v c).mpr
    intro p ha hp
    omega
  · exact (restrictedParent_eq_filled_nearestSmaller F v cap (by omega)
      (hcap c (Nat.le_refl c))).symm

theorem Row.difference_zero_parent_none (a : Row) {c : Nat}
    (hz : a.difference c = 0) : a.forest.parent c = none := by
  cases hp : a.forest.parent c with
  | none => rfl
  | some p =>
      have hpos := (a.difference_pos_iff c).mpr ⟨p, hp⟩
      omega

theorem Row.next_depth_nearestSmaller (a : Row) (c : Nat) :
    ZeroY.Forest.nearestSmaller a.forest.parent a.next.forest.depth c =
      a.next.forest.parent c :=
  select_depth_nearestSmaller a.forest a.difference
    (fun _ hz => a.difference_zero_parent_none hz) c

end OneY.Numeric

#print axioms OneY.Numeric.select_depth_nearestSmaller
#print axioms OneY.Numeric.Row.next_depth_nearestSmaller
