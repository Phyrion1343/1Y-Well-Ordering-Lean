import ZeroY.Mountain.SumInverse
import YesMetaZFC.BMS.Ancestor

/-!
# 合法山脉的根

不变量只记录前层父图左向、当前值为正，以及前层森林的根在当前层值为 1。
这些条件由每个合法初始式满足，并由实际差分步骤保持。因此每层“无父项”
恰好等价于当前值为 1，随后可以无附加假设地使用逐行求和逆定理。
-/

namespace ZeroY

open YesMetaZFC.BMS

/-- 严格左向边的任意非空链仍然严格左向。 -/
theorem leftParent_transGen_lt {parent : ParentMap}
    (hLeft : ∀ {column found}, parent column = some found → found < column)
    {column found : Nat}
    (hPath : Relation.TransGen (fun larger smaller =>
      parent larger = some smaller) column found) : found < column := by
  induction hPath with
  | single edge => exact hLeft edge
  | tail path edge ih => exact Nat.lt_trans (hLeft edge) ih

/-- 左向父图的任意节点都能沿有限父链到达一个根。 -/
theorem leftParent_exists_root (parent : ParentMap)
    (hLeft : ∀ {column found}, parent column = some found → found < column)
    (column : Nat) :
    ∃ root, root ≤ column ∧ parent root = none ∧
      (root = column ∨ Relation.TransGen (fun larger smaller =>
        parent larger = some smaller) column root) := by
  induction column using Nat.strongRecOn with
  | ind column ih =>
      cases hParent : parent column with
      | none => exact ⟨column, Nat.le_refl _, hParent, Or.inl rfl⟩
      | some found =>
          have hFound := hLeft hParent
          rcases ih found hFound with ⟨root, hRootLe, hRoot, hPath⟩
          refine ⟨root, by omega, hRoot, Or.inr ?_⟩
          rcases hPath with rfl | hPath
          · exact Relation.TransGen.single hParent
          · exact Relation.TransGen.trans (Relation.TransGen.single hParent) hPath

/-- 由实际山脉迭代保持的局部不变量。 -/
structure Layer.RootInvariant (layer : Layer) : Prop where
  positive : layer.Positive
  leftward : ∀ {column found}, layer.previous column = some found → found < column
  rootsOne : ∀ column, column < layer.values.length →
    layer.previous column = none → layer.values[column]?.getD 0 = 1

theorem linearParent_leftward {column found : Nat}
    (hParent : linearParent column = some found) : found < column := by
  cases column with
  | zero => simp [linearParent] at hParent
  | succ column => simp only [linearParent, Option.some.injEq] at hParent; omega

/-- 所有合法式都满足初始不变量，不需要标准生成性。 -/
theorem legal_initial_rootInvariant {values : Sequence} (hLegal : Legal values) :
    (Layer.mk values linearParent).RootInvariant := by
  refine ⟨hLegal.1, fun hParent => linearParent_leftward hParent, ?_⟩
  intro column hColumn hParent
  cases column with
  | succ column => simp [linearParent] at hParent
  | zero =>
      rcases hLegal.2 with hEmpty | hHead
      · simp [hEmpty] at hColumn
      · cases values with
        | nil => simp at hColumn
        | cons first rest => simpa using hHead

/-- 任意正值层中，值为 1 的列不可能有更小正值父项。 -/
theorem layerParent_none_of_value_one {layer : Layer} (hPositive : layer.Positive)
    {column : Nat} (hColumn : column < layer.values.length)
    (hOne : layer.values[column]?.getD 0 = 1) :
    layerParent layer column = none := by
  cases hParent : layerParent layer column with
  | none => rfl
  | some found =>
      have hFound : found < layer.values.length :=
        Nat.lt_trans (layerParent_some_lt hParent) hColumn
      have hPositiveFound := positive_getD hPositive hFound
      have hLess := layerParent_some_value_lt hParent
      omega

/-- 不变量保证每个大于 1 的值都能找到一个祖先根作为合格候选。 -/
theorem layerParent_none_iff_value_one {layer : Layer} (hInv : layer.RootInvariant)
    {column : Nat} (hColumn : column < layer.values.length) :
    layerParent layer column = none ↔ layer.values[column]?.getD 0 = 1 := by
  constructor
  · intro hNone
    rcases leftParent_exists_root layer.previous hInv.leftward column with
      ⟨root, hRootLe, hRootNone, hPath⟩
    have hRootValid : root < layer.values.length := by omega
    have hRootOne := hInv.rootsOne root hRootValid hRootNone
    rcases hPath with rfl | hPath
    · exact hRootOne
    · have hRootLt : root < column := leftParent_transGen_lt hInv.leftward hPath
      have hMember := strictAncestor_mem_ancestorChain hInv.leftward
        (Nat.le_refl column) hPath
      have hSearch := hNone
      unfold layerParent at hSearch
      rw [if_pos hColumn] at hSearch
      have hNotEligible := greatestBelow?_eq_none_iff.mp hSearch root hRootLt
      have hPositiveColumn := positive_getD hInv.positive hColumn
      have hContains : (ancestorChain layer.previous column column).contains root = true :=
        List.contains_iff_mem.mpr hMember
      simp only [hContains, Bool.true_and, decide_eq_false_iff_not] at hNotEligible
      omega
  · exact layerParent_none_of_value_one hInv.positive hColumn

/-- 差分实际使前层根取 1，所以该根不变量由每一步保持。 -/
theorem nextLayer_rootInvariant (layer : Layer) :
    (nextLayer layer).RootInvariant := by
  refine ⟨nextLayer_positive layer, fun hParent => layerParent_some_lt hParent, ?_⟩
  intro column hColumn hNone
  have hColumnOld : column < layer.values.length := by simpa using hColumn
  change layerParent layer column = none at hNone
  rw [nextLayer_getD hColumnOld, hNone]

/-- 无截断的实际逐层山脉在每层均满足根不变量。 -/
theorem layerAfter_rootInvariant {layer : Layer} (hInv : layer.RootInvariant) (steps : Nat) :
    (layerAfter steps layer).RootInvariant := by
  induction steps generalizing layer with
  | zero => exact hInv
  | succ steps ih => exact ih (nextLayer_rootInvariant layer)

theorem legal_layerAfter_rootInvariant {values : Sequence} (hLegal : Legal values)
    (steps : Nat) :
    (layerAfter steps ⟨values, linearParent⟩).RootInvariant :=
  layerAfter_rootInvariant (legal_initial_rootInvariant hLegal) steps

/-- 合法式所产生的每个实际层，根恰好是值为 1 的列。 -/
theorem legal_layerAfter_parent_none_iff {values : Sequence} (hLegal : Legal values)
    (steps : Nat) {column : Nat}
    (hColumn : column < (layerAfter steps ⟨values, linearParent⟩).values.length) :
    layerParent (layerAfter steps ⟨values, linearParent⟩) column = none ↔
      (layerAfter steps ⟨values, linearParent⟩).values[column]?.getD 0 = 1 :=
  layerParent_none_iff_value_one (legal_layerAfter_rootInvariant hLegal steps) hColumn

/-- 在实际山脉不变量下，差分和求和确实互逆。 -/
theorem rootInvariant_sumRow_nextLayer {layer : Layer} (hInv : layer.RootInvariant) :
    sumRow (layerParent layer) (nextLayer layer).values = layer.values :=
  sumRow_nextLayer (fun _ hColumn hNone =>
    (layerParent_none_iff_value_one hInv hColumn).mp hNone)

/-- 对所有合法输入及所有层，不附加未证的根条件。 -/
theorem legal_layerAfter_sumRow_nextLayer {values : Sequence} (hLegal : Legal values)
    (steps : Nat) :
    sumRow (layerParent (layerAfter steps ⟨values, linearParent⟩))
      (nextLayer (layerAfter steps ⟨values, linearParent⟩)).values =
        (layerAfter steps ⟨values, linearParent⟩).values :=
  rootInvariant_sumRow_nextLayer (legal_layerAfter_rootInvariant hLegal steps)

/-- 从任意实际层反向求和整座父图塔，精确恢复初始行。 -/
theorem sumRow_layerAfter_foldr {layer : Layer} (hInv : layer.RootInvariant)
    (steps : Nat) :
    (List.range steps).foldr
      (fun row upper => sumRow (layerParent (layerAfter row layer)) upper)
      (layerAfter steps layer).values = layer.values := by
  induction steps generalizing layer with
  | zero => rfl
  | succ steps ih =>
      simp only [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, layerAfter]
      rw [ih (nextLayer_rootInvariant layer), rootInvariant_sumRow_nextLayer hInv]

end ZeroY
