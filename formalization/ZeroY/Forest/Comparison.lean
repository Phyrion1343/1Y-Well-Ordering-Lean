import ZeroY.Forest.Stack

/-!
# 同一候选链上的阈值比较

已处理的左侧标签相同，提高当前标签只会提高当前深度；深度相等时父项相同。
这正是逐行比较差分山脉时所需的归纳步。
-/

namespace ZeroY.Forest

open YesMetaZFC.BMS

theorem greatestBelow?_congr {bound : Nat} {left right : Nat → Bool}
    (h : ∀ i, i < bound → left i = right i) :
    greatestBelow? bound left = greatestBelow? bound right := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      simp only [greatestBelow?]
      rw [h bound (by omega)]
      by_cases hb : right bound = true
      · simp [hb]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact ih (fun i hi => h i (by omega))

/-- 当前列及其左侧相同即可保持当前父项。 -/
theorem nearestSmaller_congr_below {parent : ParentMap} {left right : Nat → Nat}
    {target : Nat} (h : ∀ i, i ≤ target → left i = right i) :
    nearestSmaller parent left target = nearestSmaller parent right target := by
  apply greatestBelow?_congr
  intro i hi
  rw [h i (by omega), h target (Nat.le_refl target)]

/-- 候选森林在当前列及其左侧相同，便产生同一候选链。 -/
theorem nearestSmaller_previous_congr_below {left right : ParentMap}
    (hLeft : Leftward left) {target : Nat}
    (h : ∀ i, i ≤ target → left i = right i) (value : Nat → Nat) :
    nearestSmaller left value target = nearestSmaller right value target := by
  unfold nearestSmaller
  rw [ancestorChain_congr_below hLeft h (Nat.le_refl target)]

/-- 严格左向森林的当前深度只依赖当前列及其左侧父边。 -/
theorem parentDepth_congr_below {left right : ParentMap} (hLeft : Leftward left)
    {target : Nat} (h : ∀ i, i ≤ target → left i = right i) :
    parentDepth left target = parentDepth right target := by
  unfold parentDepth
  rw [ancestorChain_congr_below hLeft h (Nat.le_refl target)]

/-- 目标左侧一致时，该范围内的全部深度也一致。 -/
theorem nearestSmaller_depth_congr_prefix {parent : ParentMap}
    {left right : Nat → Nat} {target column : Nat}
    (hPrefix : ∀ i, i < target → left i = right i) (hColumn : column < target) :
    parentDepth (nearestSmaller parent left) column =
      parentDepth (nearestSmaller parent right) column := by
  apply parentDepth_congr_below (nearestSmaller_leftward parent left)
  intro i hi
  apply nearestSmaller_congr_below
  intro j hj
  exact hPrefix j (by omega)

/-- 提高当前阈值不会降低深度；保持深度则必定保持父项。 -/
theorem nearestSmaller_depth_compare {parent : ParentMap} (hLeft : Leftward parent)
    {left right : Nat → Nat} {target : Nat}
    (hPrefix : ∀ i, i < target → left i = right i)
    (hValue : left target ≤ right target) :
    parentDepth (nearestSmaller parent left) target ≤
        parentDepth (nearestSmaller parent right) target ∧
      (parentDepth (nearestSmaller parent left) target =
          parentDepth (nearestSmaller parent right) target →
        nearestSmaller parent left target = nearestSmaller parent right target) := by
  have hLeftNew : Leftward (nearestSmaller parent left) := nearestSmaller_leftward parent left
  have hRightNew : Leftward (nearestSmaller parent right) := nearestSmaller_leftward parent right
  cases hl : nearestSmaller parent left target with
  | none =>
      rw [parentDepth_none hl]
      refine ⟨Nat.zero_le _, ?_⟩
      intro hDepth
      cases hr : nearestSmaller parent right target with
      | none => rfl
      | some q =>
          have hStep := parentDepth_some (parent := nearestSmaller parent right) hRightNew hr
          omega
  | some p =>
      obtain ⟨hpAnc, hpVal, _⟩ := (nearestSmaller_some_iff hLeft).mp hl
      have hpLt := ancestor_lt hLeft hpAnc
      have hpRightVal : right p < right target := by rw [← hPrefix p hpLt]; omega
      cases hr : nearestSmaller parent right target with
      | none =>
          have hNo := (nearestSmaller_none_iff hLeft).mp hr p hpAnc
          omega
      | some q =>
          obtain ⟨hqAnc, _, hqMax⟩ := (nearestSmaller_some_iff hLeft).mp hr
          have hqLt := ancestor_lt hLeft hqAnc
          have hpLe := hqMax p hpAnc hpRightVal
          have hStepLeft := parentDepth_some (parent := nearestSmaller parent left) hLeftNew hl
          have hStepRight := parentDepth_some (parent := nearestSmaller parent right) hRightNew hr
          rcases Nat.eq_or_lt_of_le hpLe with heq | hlt
          · subst q
            have hDepth := nearestSmaller_depth_congr_prefix (parent := parent) hPrefix hpLt
            constructor
            · omega
            · intro _; rfl
          · have hAnc := nearestSmaller_ancestor_of_between hLeft hl hqAnc hlt
            have hDeep := ancestor_depth_lt (parent := nearestSmaller parent left) hLeftNew hAnc
            have hDepth := nearestSmaller_depth_congr_prefix (parent := parent) hPrefix hqLt
            constructor
            · omega
            · intro hEq; omega

/-- 同一森林中，两个目标共用候选链时，也具有相同的阈值比较性质。 -/
theorem nearestSmaller_common_chain_depth_compare {parent : ParentMap}
    (hLeft : Leftward parent) {value : Nat → Nat} {left right : Nat}
    (hChain : ∀ candidate, Ancestor parent left candidate ↔ Ancestor parent right candidate)
    (hValue : value left ≤ value right) :
    parentDepth (nearestSmaller parent value) left ≤
        parentDepth (nearestSmaller parent value) right ∧
      (parentDepth (nearestSmaller parent value) left =
          parentDepth (nearestSmaller parent value) right →
        nearestSmaller parent value left = nearestSmaller parent value right) := by
  have hNew : Leftward (nearestSmaller parent value) := nearestSmaller_leftward parent value
  cases hl : nearestSmaller parent value left with
  | none =>
      rw [parentDepth_none hl]
      refine ⟨Nat.zero_le _, ?_⟩
      intro hDepth
      cases hr : nearestSmaller parent value right with
      | none => rfl
      | some q =>
          have hStep := parentDepth_some (parent := nearestSmaller parent value) hNew hr
          omega
  | some p =>
      obtain ⟨hpAnc, hpVal, _⟩ := (nearestSmaller_some_iff hLeft).mp hl
      have hpRight : Ancestor parent right p := (hChain p).mp hpAnc
      have hpValRight : value p < value right := by omega
      cases hr : nearestSmaller parent value right with
      | none =>
          have hNo := (nearestSmaller_none_iff hLeft).mp hr p hpRight
          omega
      | some q =>
          obtain ⟨hqAnc, _, hqMax⟩ := (nearestSmaller_some_iff hLeft).mp hr
          have hpLe := hqMax p hpRight hpValRight
          have hStepLeft := parentDepth_some (parent := nearestSmaller parent value) hNew hl
          have hStepRight := parentDepth_some (parent := nearestSmaller parent value) hNew hr
          rcases Nat.eq_or_lt_of_le hpLe with heq | hlt
          · subst q
            exact ⟨by omega, fun _ => rfl⟩
          · have hAnc := nearestSmaller_ancestor_of_between hLeft hl ((hChain q).mpr hqAnc) hlt
            have hDeep := ancestor_depth_lt (parent := nearestSmaller parent value) hNew hAnc
            exact ⟨by omega, fun hEq => by omega⟩

/-- 候选链相同且深度相同，父项必相同；无需预先知道原标签的大小方向。 -/
theorem nearestSmaller_eq_of_common_chain_depth_eq {parent : ParentMap}
    (hLeft : Leftward parent) {value : Nat → Nat} {left right : Nat}
    (hChain : ∀ candidate, Ancestor parent left candidate ↔ Ancestor parent right candidate)
    (hDepth : parentDepth (nearestSmaller parent value) left =
      parentDepth (nearestSmaller parent value) right) :
    nearestSmaller parent value left = nearestSmaller parent value right := by
  by_cases hValue : value left ≤ value right
  · exact (nearestSmaller_common_chain_depth_compare hLeft hChain hValue).2 hDepth
  · exact ((nearestSmaller_common_chain_depth_compare hLeft
      (fun candidate => (hChain candidate).symm) (by omega)).2 hDepth.symm).symm

/-- 山脉的局部前缀一致性同时记录数值及候选森林。 -/
def AgreeBelow (left right : Layer) (target : Nat) : Prop :=
  (∀ i, i < target → left.values[i]?.getD 0 = right.values[i]?.getD 0) ∧
    (∀ i, i ≤ target → left.previous i = right.previous i)

theorem layerParent_congr_below {left right : Layer} (hLeft : Leftward left.previous)
    {target : Nat}
    (hValues : ∀ i, i ≤ target → left.values[i]?.getD 0 = right.values[i]?.getD 0)
    (hPrevious : ∀ i, i ≤ target → left.previous i = right.previous i) :
    layerParent left target = layerParent right target := by
  rw [layerParent_eq_nearestSmaller left, layerParent_eq_nearestSmaller right]
  rw [nearestSmaller_congr_below hValues]
  exact nearestSmaller_previous_congr_below hLeft hPrevious _

theorem layerParent_congr_prefix {left right : Layer} (hLeft : Leftward left.previous)
    {target : Nat} (hAgree : AgreeBelow left right target) {column : Nat}
    (hColumn : column < target) : layerParent left column = layerParent right column := by
  apply layerParent_congr_below hLeft
  · intro i hi; exact hAgree.1 i (by omega)
  · intro i hi; exact hAgree.2 i (by omega)

/-- 共用候选链的实际山脉比较步。 -/
theorem layer_depth_compare {left right : Layer} (hLeft : Leftward left.previous)
    {target : Nat} (hAgree : AgreeBelow left right target)
    (hValue : left.values[target]?.getD 0 ≤ right.values[target]?.getD 0) :
    parentDepth (layerParent left) target ≤ parentDepth (layerParent right) target ∧
      (parentDepth (layerParent left) target = parentDepth (layerParent right) target →
        layerParent left target = layerParent right target) := by
  let rightValue : Nat → Nat := fun i => right.values[i]?.getD 0
  have hParents : ∀ i, i ≤ target →
      nearestSmaller left.previous rightValue i = layerParent right i := by
    intro i hi
    rw [layerParent_eq_nearestSmaller right]
    exact nearestSmaller_previous_congr_below hLeft
      (fun j hj => hAgree.2 j (by omega)) rightValue
  have hDepth := parentDepth_congr_below
    (nearestSmaller_leftward left.previous rightValue) hParents
  have hCompare := nearestSmaller_depth_compare hLeft hAgree.1 hValue
  rw [← layerParent_eq_nearestSmaller left] at hCompare
  change parentDepth (layerParent left) target ≤
    parentDepth (nearestSmaller left.previous rightValue) target ∧ _ at hCompare
  rw [hDepth, hParents target (Nat.le_refl target)] at hCompare
  exact hCompare

end ZeroY.Forest
