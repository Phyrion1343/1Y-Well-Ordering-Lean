import OneY.Numeric
import ZeroY.Mountain.CommonChain

/-!
# Sparse nearest-smaller comparison

An absent cell is replaced by a sentinel above the current positive target.
This proves comparison of the actual sparse selection; no canonical property
of a newly copied mountain is assumed.
-/

namespace OneY.Numeric

/-- The cap only has to bound the targets being compared, not the whole row. -/
def filledValue (cap : Nat) (v : Nat → Nat) (c : Nat) : Nat :=
  if v c = 0 then cap+1 else v c

theorem filledValue_positive (cap : Nat) (v : Nat → Nat) {c : Nat}
    (hc : 0 < v c) : filledValue cap v c = v c := by
  rw [filledValue, if_neg (by omega)]

theorem filledValue_lt_iff (cap : Nat) (v : Nat → Nat) {c : Nat}
    (hc : 0 < v c) (hCap : v c ≤ cap) (p : Nat) :
    filledValue cap v p < filledValue cap v c ↔ 0 < v p ∧ v p < v c := by
  rw [filledValue_positive cap v hc]
  by_cases hp : v p = 0
  · rw [filledValue, if_pos hp]
    omega
  · rw [filledValue, if_neg hp]
    omega

theorem restrictedParent_eq_filled_nearestSmaller (F : ParentForest)
    (v : Nat → Nat) (cap : Nat) {c : Nat}
    (hc : 0 < v c) (hCap : v c ≤ cap) :
    restrictedParent F v c = ZeroY.Forest.nearestSmaller F.parent (filledValue cap v) c := by
  apply ZeroY.Forest.greatestBelow?_congr
  intro p _
  rw [filledValue_positive cap v hc]
  by_cases hp : v p = 0
  · have hSentinel : ¬ cap+1 < v c := by omega
    simp [filledValue, hp, hSentinel]
  · have hPositive : 0 < v p := by omega
    simp [filledValue, hp, hPositive]

/-- Sparse ancestors remain positive and below the original cap, so equality
of parent searches propagates along the entire computed ancestor chain. -/
theorem select_depth_eq_filled_depth (F : ParentForest) (v : Nat → Nat)
    (cap : Nat) {c : Nat} (hc : 0 < v c) (hCap : v c ≤ cap) :
    (select F v).forest.depth c =
      ZeroY.parentDepth (ZeroY.Forest.nearestSmaller F.parent (filledValue cap v)) c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      have he := restrictedParent_eq_filled_nearestSmaller F v cap hc hCap
      cases hp : restrictedParent F v c with
      | none =>
          have hSparse : (select F v).forest.parent c = none := hp
          have hDense : ZeroY.Forest.nearestSmaller F.parent (filledValue cap v) c = none :=
            he.symm.trans hp
          rw [(select F v).forest.depth_of_parent_none hSparse,
            ZeroY.Forest.parentDepth_none hDense]
      | some p =>
          have hSparse : (select F v).forest.parent c = some p := hp
          have hDense : ZeroY.Forest.nearestSmaller F.parent (filledValue cap v) c = some p :=
            he.symm.trans hp
          have hValues := (restrictedParent_spec F v hp).2
          rw [(select F v).forest.depth_of_parent_some hSparse,
            ZeroY.Forest.parentDepth_some
              (ZeroY.Forest.nearestSmaller_leftward F.parent (filledValue cap v)) hDense]
          rw [ih p (restrictedParent_left F v hp) hValues.1 (by omega)]

/-- Shared candidate chains give monotone depth comparison even in sparse rows.
Equality of depth forces equality of the selected parent. -/
theorem select_common_chain_depth_compare (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p)
    (hValue : v left ≤ v right) :
    (select F v).forest.depth left ≤ (select F v).forest.depth right ∧
      ((select F v).forest.depth left = (select F v).forest.depth right →
        restrictedParent F v left = restrictedParent F v right) := by
  let cap := max (v left) (v right)
  have hLCap : v left ≤ cap := Nat.le_max_left _ _
  have hRCap : v right ≤ cap := Nat.le_max_right _ _
  have hFilled : filledValue cap v left ≤ filledValue cap v right := by
    rw [filledValue_positive cap v hL, filledValue_positive cap v hR]
    exact hValue
  have ht := ZeroY.Forest.nearestSmaller_common_chain_depth_compare F.parent_left hChain hFilled
  rw [← select_depth_eq_filled_depth F v cap hL hLCap,
    ← select_depth_eq_filled_depth F v cap hR hRCap,
    ← restrictedParent_eq_filled_nearestSmaller F v cap hL hLCap,
    ← restrictedParent_eq_filled_nearestSmaller F v cap hR hRCap] at ht
  exact ht

theorem select_parent_eq_of_common_chain_depth_eq (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hChain : ∀ p, ZeroY.Forest.Ancestor F.parent left p ↔
      ZeroY.Forest.Ancestor F.parent right p)
    (hDepth : (select F v).forest.depth left = (select F v).forest.depth right) :
    restrictedParent F v left = restrictedParent F v right := by
  by_cases hValue : v left ≤ v right
  · exact (select_common_chain_depth_compare F v hL hR hChain hValue).2 hDepth
  · exact ((select_common_chain_depth_compare F v hR hL
      (fun p => (hChain p).symm) (by omega)).2 hDepth.symm).symm

theorem select_common_parent_depth_compare (F : ParentForest) (v : Nat → Nat)
    {left right : Nat} (hL : 0 < v left) (hR : 0 < v right)
    (hParent : F.parent left = F.parent right) (hValue : v left ≤ v right) :
    (select F v).forest.depth left ≤ (select F v).forest.depth right ∧
      ((select F v).forest.depth left = (select F v).forest.depth right →
        restrictedParent F v left = restrictedParent F v right) :=
  select_common_chain_depth_compare F v hL hR
    (ZeroY.Forest.ancestor_iff_of_parent_eq hParent) hValue

#print axioms restrictedParent_eq_filled_nearestSmaller
#print axioms select_depth_eq_filled_depth
#print axioms select_common_chain_depth_compare
#print axioms select_parent_eq_of_common_chain_depth_eq

end OneY.Numeric
