import ZeroY.Mountain.Termination
import YesMetaZFC.BMS.Ancestor

/-!
# 左向森林中的深度替换

证明采用单调栈的记录最小值刻画：最近较小父项与目标之间的每个候选，
都以该父项为新森林的祖先。因此深度标号不会越过原来的阻挡项。
-/

namespace ZeroY.Forest

open YesMetaZFC.BMS

/-- 每条父边严格指向较小的列号。 -/
def Leftward (parent : ParentMap) : Prop :=
  ∀ {target found}, parent target = some found → found < target

/-- 无燃料的严格祖先关系。 -/
def Ancestor (parent : ParentMap) (target found : Nat) : Prop :=
  Relation.TransGen (fun a b => parent a = some b) target found

theorem ancestor_lt {parent : ParentMap} (hLeft : Leftward parent)
    {target found : Nat} (h : Ancestor parent target found) : found < target := by
  induction h with
  | single h => exact hLeft h
  | tail _ h ih => exact Nat.lt_trans (hLeft h) ih

theorem ancestor_trans {parent : ParentMap} {a b c : Nat}
    (h₁ : Ancestor parent a b) (h₂ : Ancestor parent b c) :
    Ancestor parent a c := Relation.TransGen.trans h₁ h₂

theorem ancestor_of_common_target {parent : ParentMap} (hLeft : Leftward parent)
    {target earlier later : Nat} (hEarlier : Ancestor parent target earlier)
    (hLater : Ancestor parent target later) (hOrder : earlier < later) :
    Ancestor parent later earlier := by
  rcases parentTransGen_comparable hLeft hEarlier hLater with heq | h₁ | h₂
  · omega
  · have := ancestor_lt hLeft h₁
    omega
  · exact h₂

theorem ancestorChain_contains_iff {parent : ParentMap} (hLeft : Leftward parent)
    {target found : Nat} :
    (ancestorChain parent target target).contains found = true ↔
      Ancestor parent target found := by
  constructor
  · intro h
    exact ancestorChain_mem_strictAncestor (by simpa using h)
  · intro h
    simpa using strictAncestor_mem_ancestorChain hLeft (Nat.le_refl target) h

/-- 沿给定森林的祖先链，选择标签严格较小的最近节点。 -/
def nearestSmaller (parent : ParentMap) (value : Nat → Nat) (target : Nat) : Option Nat :=
  greatestBelow? target fun candidate =>
    (ancestorChain parent target target).contains candidate && value candidate < value target

theorem nearestSmaller_leftward (parent : ParentMap) (value : Nat → Nat) :
    Leftward (nearestSmaller parent value) := by
  intro target found h
  exact greatestBelow?_some_lt h

theorem nearestSmaller_some_iff {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target found : Nat} :
    nearestSmaller parent value target = some found ↔
      Ancestor parent target found ∧ value found < value target ∧
        ∀ candidate, Ancestor parent target candidate → value candidate < value target →
          candidate ≤ found := by
  unfold nearestSmaller
  rw [greatestBelow?_eq_some_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ancestorChain_contains_iff hLeft]
  constructor
  · rintro ⟨_, ⟨hAnc, hVal⟩, hMax⟩
    exact ⟨hAnc, hVal, fun candidate hA hV =>
      hMax candidate (ancestor_lt hLeft hA) ⟨hA, hV⟩⟩
  · rintro ⟨hAnc, hVal, hMax⟩
    exact ⟨ancestor_lt hLeft hAnc, ⟨hAnc, hVal⟩,
      fun candidate _ h => hMax candidate h.1 h.2⟩

theorem nearestSmaller_none_iff {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target : Nat} :
    nearestSmaller parent value target = none ↔
      ∀ candidate, Ancestor parent target candidate → value target ≤ value candidate := by
  constructor
  · intro h candidate hAnc
    have hNo := (greatestBelow?_eq_none_iff.mp h) candidate (ancestor_lt hLeft hAnc)
    have hMem := (ancestorChain_contains_iff hLeft).mpr hAnc
    simp only [hMem, Bool.true_and, decide_eq_false_iff_not] at hNo
    omega
  · intro h
    apply greatestBelow?_eq_none_iff.mpr
    intro candidate _
    by_cases hAnc : Ancestor parent target candidate
    · have hMem := (ancestorChain_contains_iff hLeft).mpr hAnc
      have hVal := h candidate hAnc
      simp only [hMem, Bool.true_and, decide_eq_false_iff_not]
      omega
    · have hMem : (ancestorChain parent target target).contains candidate = false := by
        cases hc : (ancestorChain parent target target).contains candidate with
        | false => rfl
        | true => exact (hAnc ((ancestorChain_contains_iff hLeft).mp hc)).elim
      simp only [hMem, Bool.false_and]

/-- 左向链在燃料到达当前列号后完全稳定。 -/
theorem ancestorChain_fuel_eq {parent : ParentMap} (hLeft : Leftward parent)
    {target fuel₁ fuel₂ : Nat} (h₁ : target ≤ fuel₁) (h₂ : target ≤ fuel₂) :
    ancestorChain parent target fuel₁ = ancestorChain parent target fuel₂ := by
  induction target using Nat.strongRecOn generalizing fuel₁ fuel₂ with
  | ind target ih =>
      cases hp : parent target with
      | none => cases fuel₁ <;> cases fuel₂ <;> simp [ancestorChain, hp]
      | some p =>
          have hpLt := hLeft hp
          cases fuel₁ with
          | zero => omega
          | succ f₁ =>
            cases fuel₂ with
            | zero => omega
            | succ f₂ =>
              simp only [ancestorChain, hp]
              rw [ih p hpLt (show p ≤ f₁ by omega) (show p ≤ f₂ by omega)]

theorem parentDepth_none {parent : ParentMap} {target : Nat}
    (h : parent target = none) : parentDepth parent target = 0 := by
  cases target <;> simp [parentDepth, ancestorChain, h]

theorem parentDepth_some {parent : ParentMap} (hLeft : Leftward parent)
    {target found : Nat} (h : parent target = some found) :
    parentDepth parent target = parentDepth parent found + 1 := by
  have hLt := hLeft h
  cases target with
  | zero => omega
  | succ target =>
      simp only [parentDepth, ancestorChain, h, List.length_cons]
      rw [ancestorChain_fuel_eq hLeft (show found ≤ target by omega) (Nat.le_refl found)]

theorem ancestor_depth_lt {parent : ParentMap} (hLeft : Leftward parent)
    {target found : Nat} (h : Ancestor parent target found) :
    parentDepth parent found < parentDepth parent target := by
  induction h with
  | single h => rw [parentDepth_some (parent := parent) hLeft h]; omega
  | tail _ h ih =>
      have heq := parentDepth_some (parent := parent) hLeft h
      omega

/-- 若一个候选在整个剩余段上都严格较小，则新父链必定经过它。 -/
theorem ancestor_of_record_minimum {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target found : Nat}
    (hAnc : Ancestor parent target found)
    (hValue : value found < value target)
    (hRecord : ∀ candidate, Ancestor parent target candidate → found < candidate →
      value found < value candidate) :
    Ancestor (nearestSmaller parent value) target found := by
  induction target using Nat.strongRecOn with
  | ind target ih =>
      cases hp : nearestSmaller parent value target with
      | none =>
          have hNo := (nearestSmaller_none_iff hLeft).mp hp found hAnc
          omega
      | some p =>
          obtain ⟨hpAnc, hpVal, hpMax⟩ := (nearestSmaller_some_iff hLeft).mp hp
          have hpLe := hpMax found hAnc hValue
          rcases Nat.eq_or_lt_of_le hpLe with heq | hlt
          · subst p
            exact Relation.TransGen.single hp
          · have hFoundAnc := ancestor_of_common_target hLeft hAnc hpAnc hlt
            have hFoundVal := hRecord p hpAnc hlt
            have hBelow := ih p (ancestor_lt hLeft hpAnc) hFoundAnc hFoundVal
              (fun candidate hc hOrder => hRecord candidate (ancestor_trans hpAnc hc) hOrder)
            exact Relation.TransGen.trans (Relation.TransGen.single hp) hBelow

/-- 最近较小父项与目标之间的每个原链节点，都以该父项为新祖先。 -/
theorem nearestSmaller_ancestor_of_between {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target found candidate : Nat}
    (hParent : nearestSmaller parent value target = some found)
    (hCandidate : Ancestor parent target candidate) (hOrder : found < candidate) :
    Ancestor (nearestSmaller parent value) candidate found := by
  obtain ⟨hFound, hValue, hMax⟩ := (nearestSmaller_some_iff hLeft).mp hParent
  have hBound : ∀ k, Ancestor parent target k → found < k → value target ≤ value k := by
    intro k hk hOrder
    by_cases h : value k < value target
    · have := hMax k hk h
      omega
    · omega
  apply ancestor_of_record_minimum hLeft
    (ancestor_of_common_target hLeft hFound hCandidate hOrder)
  · have := hBound candidate hCandidate hOrder
    omega
  · intro k hk hOrder
    have := hBound k (ancestor_trans hCandidate hk) hOrder
    omega

/-- 单调栈核心定理：以父链深度替换标签，不改变最近较小父图。 -/
theorem nearestSmaller_depth_invariant {parent : ParentMap} (hLeft : Leftward parent)
    (value : Nat → Nat) :
    nearestSmaller parent (parentDepth (nearestSmaller parent value)) =
      nearestSmaller parent value := by
  funext target
  have hNewLeft : Leftward (nearestSmaller parent value) := nearestSmaller_leftward parent value
  cases hp : nearestSmaller parent value target with
  | none =>
      apply (nearestSmaller_none_iff hLeft).mpr
      intro candidate _
      rw [parentDepth_none hp]
      exact Nat.zero_le _
  | some found =>
      obtain ⟨hAnc, _, _⟩ := (nearestSmaller_some_iff hLeft).mp hp
      apply (nearestSmaller_some_iff hLeft).mpr
      refine ⟨hAnc, ?_, ?_⟩
      · rw [parentDepth_some (parent := nearestSmaller parent value) hNewLeft hp]
        omega
      · intro candidate hCandidate hDepth
        by_cases hOrder : found < candidate
        · have hNewAnc := nearestSmaller_ancestor_of_between hLeft hp hCandidate hOrder
          have hLess := ancestor_depth_lt (parent := nearestSmaller parent value) hNewLeft hNewAnc
          have hEq := parentDepth_some (parent := nearestSmaller parent value) hNewLeft hp
          omega
        · omega

/-- 序列范围外的缺省值为零，故无范围 guard 的搜索也必定返回 none。 -/
theorem layerParent_eq_nearestSmaller (layer : Layer) :
    layerParent layer = nearestSmaller layer.previous
      (fun column => layer.values[column]?.getD 0) := by
  funext column
  unfold layerParent
  by_cases hColumn : column < layer.values.length
  · simp only [hColumn, ↓reduceIte, nearestSmaller]
  · simp only [hColumn, ↓reduceIte]
    symm
    apply greatestBelow?_eq_none_iff.mpr
    intro candidate _
    have hValue : layer.values[column]? = none := List.getElem?_eq_none (by omega)
    simp [hValue]

/-- 深度行补零查询恰为总父图的深度，包括原序列范围外的所有列。 -/
theorem depthRow_getD (layer : Layer) (column : Nat) :
    (depthRow layer)[column]?.getD 0 = parentDepth (layerParent layer) column := by
  by_cases hColumn : column < layer.values.length
  · simp [depthRow, hColumn]
  · have hLength : (depthRow layer).length ≤ column := by simp [depthRow]; omega
    have hParent : layerParent layer column = none := by simp [layerParent, hColumn]
    rw [List.getElem?_eq_none hLength, Option.getD_none, parentDepth_none hParent]

/-- 直接面向山脉的栈引理，不要求合法、标准或正值输入。 -/
theorem layerParent_depthRow {layer : Layer} (hLeft : Leftward layer.previous) :
    layerParent ⟨depthRow layer, layer.previous⟩ = layerParent layer := by
  rw [layerParent_eq_nearestSmaller]
  change nearestSmaller layer.previous (fun column => (depthRow layer)[column]?.getD 0) = _
  simp only [depthRow_getD]
  rw [layerParent_eq_nearestSmaller layer]
  exact nearestSmaller_depth_invariant hLeft _

end ZeroY.Forest
