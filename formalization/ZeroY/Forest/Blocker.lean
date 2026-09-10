import ZeroY.Forest.Stack

/-!
# 被跳过父项链中的阻挡节点

若最近较小搜索跳过直接候选 q 而选中 p，则 q 的新父链上存在紧接 p 的
节点 z，且 z 的数值不小于目标。这是结构条件 S 必要性的森林部分。
-/

namespace ZeroY.Forest

open YesMetaZFC.BMS

/-- 最近较小项父图的每条祖先链仍包含在原候选森林中。 -/
theorem nearestSmaller_ancestor_lift {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target found : Nat}
    (h : Ancestor (nearestSmaller parent value) target found) : Ancestor parent target found := by
  induction h with
  | single hp => exact ((nearestSmaller_some_iff hLeft).mp hp).1
  | tail _ hp ih => exact ancestor_trans ih ((nearestSmaller_some_iff hLeft).mp hp).1

/-- 非空父链上的最后一条边给出目标祖先下面的唯一子节点的存在性。 -/
theorem ancestor_exists_last_edge {parent : ParentMap} {target found : Nat}
    (h : Ancestor parent target found) :
    ∃ z, (z = target ∨ Ancestor parent target z) ∧ parent z = some found := by
  cases h with
  | single hp => exact ⟨target, Or.inl rfl, hp⟩
  | tail path hp => exact ⟨_, Or.inr path, hp⟩

/-- 搜索跳过 q 时，q 的新父链中紧接 p 的子项确实阻挡目标。 -/
theorem nearestSmaller_exists_blocker {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target q p : Nat}
    (hQ : parent target = some q)
    (hP : nearestSmaller parent value target = some p) (hDistinct : p ≠ q) :
    ∃ z, (z = q ∨ Ancestor (nearestSmaller parent value) q z) ∧
      nearestSmaller parent value z = some p ∧ value target ≤ value z := by
  obtain ⟨hPAnc, _, hMax⟩ := (nearestSmaller_some_iff hLeft).mp hP
  have hQAnc : Ancestor parent target q := Relation.TransGen.single hQ
  have hPQ : p < q := by
    rcases transGen_head hPAnc with hp | ⟨next, hn, hr⟩
    · have : p = q := Option.some.inj (hp.symm.trans hQ)
      exact (hDistinct this).elim
    · have heq : next = q := Option.some.inj (hn.symm.trans hQ)
      subst next
      exact ancestor_lt hLeft hr
  have hNewAnc := nearestSmaller_ancestor_of_between hLeft hP hQAnc hPQ
  obtain ⟨z, hZPath, hZParent⟩ := ancestor_exists_last_edge hNewAnc
  refine ⟨z, hZPath, hZParent, ?_⟩
  have hZAnc : Ancestor parent target z := by
    rcases hZPath with rfl | hZ
    · exact hQAnc
    · exact ancestor_trans hQAnc (nearestSmaller_ancestor_lift hLeft hZ)
  have hPZ : p < z := nearestSmaller_leftward parent value hZParent
  by_cases hValue : value z < value target
  · have := hMax z hZAnc hValue
    omega
  · omega

/-- 新父链上的祖先是原候选路径中的严格记录最小值。 -/
theorem nearestSmaller_ancestor_record {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target found : Nat}
    (h : Ancestor (nearestSmaller parent value) target found) :
    value found < value target ∧
      ∀ candidate, Ancestor parent target candidate → found < candidate →
        value found < value candidate := by
  induction h with
  | single hp =>
      obtain ⟨_, hVal, hMax⟩ := (nearestSmaller_some_iff hLeft).mp hp
      refine ⟨hVal, ?_⟩
      intro candidate hc hOrder
      by_cases hv : value candidate < value target
      · have := hMax candidate hc hv
        omega
      · omega
  | @tail middle last path hp ih =>
      obtain ⟨_, hVal, hMax⟩ := (nearestSmaller_some_iff hLeft).mp hp
      refine ⟨Nat.lt_trans hVal ih.1, ?_⟩
      intro candidate hc hOrder
      by_cases hm : middle < candidate
      · exact Nat.lt_trans hVal (ih.2 candidate hc hm)
      · rcases Nat.eq_or_lt_of_le (show candidate ≤ middle by omega) with heq | hlt
        · subst candidate; exact hVal
        · have hMiddleAnc := nearestSmaller_ancestor_lift hLeft path
          have hcMiddle := ancestor_of_common_target hLeft hc hMiddleAnc hlt
          by_cases hv : value candidate < value middle
          · have := hMax candidate hcMiddle hv
            omega
          · omega

/-- 左向父链上的边可用严格左侧的逐点等式替换。 -/
theorem ancestor_transfer_prefix {left right : ParentMap} (hLeft : Leftward left)
    {bound target found : Nat} (hTarget : target < bound)
    (hPrefix : ∀ i, i < bound → left i = right i)
    (h : Ancestor left target found) : Ancestor right target found := by
  induction h with
  | single hp => exact Relation.TransGen.single ((hPrefix _ hTarget).symm.trans hp)
  | @tail middle last path hp ih =>
      have hMiddleLt := ancestor_lt hLeft path
      exact Relation.TransGen.trans ih
        (Relation.TransGen.single ((hPrefix middle (by omega)).symm.trans hp))

/-- 直接父项限制所有原候选都位于 q 或 q 的严格祖先中。 -/
theorem ancestor_eq_or_below_parent {parent : ParentMap} {target q candidate : Nat}
    (hParent : parent target = some q) (h : Ancestor parent target candidate) :
    candidate = q ∨ Ancestor parent q candidate := by
  rcases transGen_head h with hd | ⟨next, hn, hr⟩
  · exact Or.inl (Option.some.inj (hd.symm.trans hParent))
  · have heq : next = q := Option.some.inj (hn.symm.trans hParent)
    subst next
    exact Or.inr hr

/--
已处理前缀的父图正确时，位于 q 父链上的阻挡 z 与 Vp<Vi≤Vz
就足以恢复当前最近较小父项；当前结果并未作为假设。
-/
theorem nearestSmaller_eq_of_blocker {candidateParent prefixParent : ParentMap}
    (hCandidateLeft : Leftward candidateParent) (hPrefixLeft : Leftward prefixParent)
    {value : Nat → Nat} {target q p z : Nat}
    (hQ : candidateParent target = some q)
    (hPAnc : Ancestor candidateParent target p)
    (hPrefix : ∀ i, i < target → prefixParent i = nearestSmaller candidateParent value i)
    (hZ : z = q ∨ Ancestor prefixParent q z)
    (hZParent : prefixParent z = some p)
    (hLower : value p < value target) (hUpper : value target ≤ value z) :
    nearestSmaller candidateParent value target = some p := by
  have hQLt := hCandidateLeft hQ
  have hZLe : z ≤ q := by
    rcases hZ with rfl | hZ
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (ancestor_lt hPrefixLeft hZ)
  have hZLt : z < target := by omega
  have hZParentNew : nearestSmaller candidateParent value z = some p :=
    (hPrefix z hZLt).symm.trans hZParent
  have hZNew : z = q ∨ Ancestor (nearestSmaller candidateParent value) q z := by
    rcases hZ with rfl | hZ
    · exact Or.inl rfl
    · exact Or.inr (ancestor_transfer_prefix hPrefixLeft hQLt hPrefix hZ)
  have hZAnc : Ancestor candidateParent target z := by
    rcases hZNew with rfl | hZNew
    · exact Relation.TransGen.single hQ
    · exact ancestor_trans (Relation.TransGen.single hQ)
        (nearestSmaller_ancestor_lift hCandidateLeft hZNew)
  apply (nearestSmaller_some_iff hCandidateLeft).mpr
  refine ⟨hPAnc, hLower, ?_⟩
  intro candidate hc hCandidateValue
  by_cases hOrder : p < candidate
  · have hBound : value z ≤ value candidate := by
      by_cases hz : candidate < z
      · have hcZ := ancestor_of_common_target hCandidateLeft hc hZAnc hz
        obtain ⟨_, _, hMax⟩ := (nearestSmaller_some_iff hCandidateLeft).mp hZParentNew
        by_cases hv : value candidate < value z
        · have := hMax candidate hcZ hv
          omega
        · omega
      · rcases Nat.eq_or_lt_of_le (show z ≤ candidate by omega) with heq | hlt
        · subst candidate; exact Nat.le_refl _
        · rcases ancestor_eq_or_below_parent hQ hc with rfl | hcQ
          · rcases hZNew with heq | hZNew
            · omega
            · exact Nat.le_of_lt (nearestSmaller_ancestor_record hCandidateLeft hZNew).1
          · rcases hZNew with heq | hZNew
            · subst z
              have := ancestor_lt hCandidateLeft hcQ
              omega
            · exact Nat.le_of_lt
                ((nearestSmaller_ancestor_record hCandidateLeft hZNew).2 candidate hcQ hlt)
    omega
  · omega

/-- 直接候选已经严格较小时，无须任何阻挡条件。 -/
theorem nearestSmaller_eq_of_direct {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {target p : Nat} (hParent : parent target = some p)
    (hValue : value p < value target) : nearestSmaller parent value target = some p := by
  apply (nearestSmaller_some_iff hLeft).mpr
  refine ⟨Relation.TransGen.single hParent, hValue, ?_⟩
  intro candidate hc _
  rcases ancestor_eq_or_below_parent hParent hc with rfl | hc
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (ancestor_lt hLeft hc)

/-- 以旧标签生成的父图给定时，阻挡充分性可直接消费左侧已恢复父图。 -/
theorem nearestSmaller_eq_of_old_blocker {parent : ParentMap} (hLeft : Leftward parent)
    {oldValue value : Nat → Nat} {target q p z : Nat}
    (hQ : parent target = some q) (hOld : nearestSmaller parent oldValue target = some p)
    (hPrefix : ∀ i, i < target →
      nearestSmaller parent oldValue i = nearestSmaller parent value i)
    (hZ : z = q ∨ Ancestor (nearestSmaller parent oldValue) q z)
    (hZParent : nearestSmaller parent oldValue z = some p)
    (hLower : value p < value target) (hUpper : value target ≤ value z) :
    nearestSmaller parent value target = some p :=
  nearestSmaller_eq_of_blocker hLeft (nearestSmaller_leftward parent oldValue) hQ
    ((nearestSmaller_some_iff hLeft).mp hOld).1 hPrefix hZ hZParent hLower hUpper

end ZeroY.Forest
