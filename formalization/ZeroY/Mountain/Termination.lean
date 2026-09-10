import ZeroY.Mountain
import YesMetaZFC.BMS.Parent

/-!
# 山脉有限性与计算燃料

本文件只要求每层数值为正，不要求前驱图来自标准式，甚至不要求该图左向。
父项搜索自身保证父项位于左侧。每个非全 1 层的最大值严格下降，故输入
最大值给出的燃料充足；继续增加燃料不会改变编码所记录的山脉。
-/

namespace ZeroY

/-- 当前行的全部数值严格为正。 -/
def Layer.Positive (layer : Layer) : Prop :=
  ∀ value ∈ layer.values, 0 < value

theorem layerParent_some_column_valid {layer : Layer} {column parent : Nat}
    (hParent : layerParent layer column = some parent) :
    column < layer.values.length := by
  unfold layerParent at hParent
  split at hParent
  · assumption
  · simp at hParent

theorem layerParent_some_lt {layer : Layer} {column parent : Nat}
    (hParent : layerParent layer column = some parent) : parent < column := by
  unfold layerParent at hParent
  split at hParent
  · exact YesMetaZFC.BMS.greatestBelow?_some_lt hParent
  · simp at hParent

theorem layerParent_some_value_lt {layer : Layer} {column parent : Nat}
    (hParent : layerParent layer column = some parent) :
    layer.values[parent]?.getD 0 < layer.values[column]?.getD 0 := by
  unfold layerParent at hParent
  split at hParent
  · have hEligible := YesMetaZFC.BMS.greatestBelow?_some_satisfies hParent
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hEligible
    exact hEligible.2
  · simp at hParent

@[simp]
theorem nextLayer_length (layer : Layer) :
    (nextLayer layer).values.length = layer.values.length := by
  simp [nextLayer]

theorem positive_getD {layer : Layer} (hPositive : layer.Positive)
    {column : Nat} (hColumn : column < layer.values.length) :
    0 < layer.values[column]?.getD 0 := by
  simpa [List.getElem?_eq_getElem hColumn] using
    hPositive _ (List.getElem_mem hColumn)

/-- 差值严格为正；这个结论甚至不要求原行正值。 -/
theorem nextLayer_positive (layer : Layer) :
    (nextLayer layer).Positive := by
  intro value hMember
  obtain ⟨column, hColumn, hValue⟩ := List.exists_of_mem_mapIdx hMember
  cases hParent : layerParent layer column with
  | none =>
      simp only [hParent] at hValue
      omega
  | some parent =>
      have hLess := layerParent_some_value_lt hParent
      simp only [List.getElem?_eq_getElem hColumn, Option.getD_some] at hLess
      simp only [hParent] at hValue
      rw [← hValue]
      omega

private theorem foldl_max_le_iff (values : List Nat) (initial bound : Nat) :
    values.foldl max initial ≤ bound ↔
      initial ≤ bound ∧ ∀ value ∈ values, value ≤ bound := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, ih, Nat.max_le, List.mem_cons]
      constructor
      · rintro ⟨⟨hInitial, hHead⟩, hTail⟩
        exact ⟨hInitial, fun value hMem => hMem.elim (fun h => h ▸ hHead) (hTail value)⟩
      · rintro ⟨hInitial, hAll⟩
        exact ⟨⟨hInitial, hAll head (Or.inl rfl)⟩,
          fun value hMem => hAll value (Or.inr hMem)⟩

theorem maxValue_le_iff (values : Sequence) (bound : Nat) :
    maxValue values ≤ bound ↔ ∀ value ∈ values, value ≤ bound := by
  simp [maxValue, foldl_max_le_iff]

theorem le_maxValue {values : Sequence} {value : Nat} (hMember : value ∈ values) :
    value ≤ maxValue values :=
  (maxValue_le_iff values (maxValue values)).mp (Nat.le_refl _) value hMember

theorem all_ones_of_maxValue_le_one {layer : Layer} (hPositive : layer.Positive)
    (hBound : maxValue layer.values ≤ 1) :
    layer.values.all (fun value => value == 1) = true := by
  simp only [List.all_eq_true, beq_iff_eq]
  intro value hMember
  have hLower := hPositive value hMember
  have hUpper := (maxValue_le_iff _ _).mp hBound value hMember
  omega

/-- 非终止层的最大值至少为 2。 -/
theorem one_lt_maxValue_of_not_all_ones {layer : Layer} (hPositive : layer.Positive)
    (hNotDone : layer.values.all (fun value => value == 1) ≠ true) :
    1 < maxValue layer.values := by
  by_cases hLt : 1 < maxValue layer.values
  · exact hLt
  · exact (hNotDone (all_ones_of_maxValue_le_one hPositive (by omega))).elim

/-- 每个非全 1 层都严格降低数值最大值。 -/
theorem nextLayer_maxValue_lt {layer : Layer} (hPositive : layer.Positive)
    (hNotDone : layer.values.all (fun value => value == 1) ≠ true) :
    maxValue (nextLayer layer).values < maxValue layer.values := by
  have hMax := one_lt_maxValue_of_not_all_ones hPositive hNotDone
  suffices hBound : maxValue (nextLayer layer).values ≤ maxValue layer.values - 1 by
    omega
  apply (maxValue_le_iff _ _).mpr
  intro value hMember
  obtain ⟨column, hColumn, hValue⟩ := List.exists_of_mem_mapIdx hMember
  cases hParent : layerParent layer column with
  | none =>
      simp only [hParent] at hValue
      omega
  | some parent =>
      have hParentValid : parent < layer.values.length :=
        Nat.lt_trans (layerParent_some_lt hParent) hColumn
      have hParentPositive := positive_getD hPositive hParentValid
      have hOldBound := le_maxValue (List.getElem_mem hColumn)
      simp only [hParent] at hValue
      omega

/-- 燃料至少达到初始最大值后，任意继续加大燃料都不改变结果。 -/
theorem mountainRows_fuel_stable {layer : Layer} (hPositive : layer.Positive)
    {fuel : Nat} (hFuel : maxValue layer.values ≤ fuel) (extra : Nat) :
    mountainRows (fuel + extra) layer = mountainRows fuel layer := by
  induction fuel generalizing layer with
  | zero =>
      have hDone := all_ones_of_maxValue_le_one hPositive (by omega)
      cases extra <;> simp [mountainRows, hDone]
  | succ fuel ih =>
      by_cases hDone : layer.values.all (fun value => value == 1) = true
      · simp [mountainRows, hDone, Nat.succ_add]
      · have hNextBound : maxValue (nextLayer layer).values ≤ fuel := by
          have := nextLayer_maxValue_lt hPositive hDone
          omega
        simpa only [Nat.succ_add, mountainRows, hDone, Bool.false_eq_true, ↓reduceIte] using
          congrArg (List.cons (depthRow layer))
            (ih (nextLayer_positive layer) hNextBound)

/-- `encodeRaw` 中选择的最大值燃料足以覆盖完整山脉。 -/
theorem mountainRows_maxValue_sufficient {layer : Layer} (hPositive : layer.Positive)
    (extra : Nat) :
    mountainRows (maxValue layer.values + extra) layer =
      mountainRows (maxValue layer.values) layer :=
  mountainRows_fuel_stable hPositive (Nat.le_refl _) extra

/-- 合法性所含的正值条件已经足够，不需要标准生成性。 -/
theorem legal_mountainRows_maxValue_sufficient {values : Sequence}
    (hLegal : Legal values) (extra : Nat) :
    mountainRows (maxValue values + extra) ⟨values, linearParent⟩ =
      mountainRows (maxValue values) ⟨values, linearParent⟩ :=
  mountainRows_maxValue_sufficient (layer := ⟨values, linearParent⟩) hLegal.1 extra

/-- 全 1 层继续作差仍是全 1 层。 -/
theorem nextLayer_all_ones {layer : Layer}
    (hDone : layer.values.all (fun value => value == 1) = true) :
    (nextLayer layer).values.all (fun value => value == 1) = true := by
  have hAll : ∀ value ∈ layer.values, value = 1 := by
    simpa only [List.all_eq_true, beq_iff_eq] using hDone
  simp only [List.all_eq_true, beq_iff_eq]
  intro value hMember
  obtain ⟨column, hColumn, hValue⟩ := List.exists_of_mem_mapIdx hMember
  cases hParent : layerParent layer column with
  | none => simpa only [hParent] using hValue.symm
  | some parent =>
      have hParentValid : parent < layer.values.length :=
        Nat.lt_trans (layerParent_some_lt hParent) hColumn
      have hLess := layerParent_some_value_lt hParent
      simp only [List.getElem?_eq_getElem hColumn,
        List.getElem?_eq_getElem hParentValid, Option.getD_some] at hLess
      rw [hAll _ (List.getElem_mem hColumn), hAll _ (List.getElem_mem hParentValid)] at hLess
      omega

/-- 无截断的逐层迭代，用于表述直接的终止上界。 -/
def layerAfter : Nat → Layer → Layer
  | 0, layer => layer
  | steps + 1, layer => layerAfter steps (nextLayer layer)

theorem layerAfter_all_ones_of_all_ones {layer : Layer}
    (hDone : layer.values.all (fun value => value == 1) = true) (steps : Nat) :
    (layerAfter steps layer).values.all (fun value => value == 1) = true := by
  induction steps generalizing layer with
  | zero => exact hDone
  | succ steps ih => exact ih (nextLayer_all_ones hDone)

/-- 正值山脉在至多输入最大值次迭代后进入全 1 层。 -/
theorem layerAfter_all_ones {layer : Layer} (hPositive : layer.Positive)
    {steps : Nat} (hSteps : maxValue layer.values ≤ steps) :
    (layerAfter steps layer).values.all (fun value => value == 1) = true := by
  induction steps generalizing layer with
  | zero =>
      exact all_ones_of_maxValue_le_one (layer := layer) hPositive (by omega)
  | succ steps ih =>
      by_cases hDone : layer.values.all (fun value => value == 1) = true
      · exact layerAfter_all_ones_of_all_ones hDone (steps + 1)
      · apply ih (nextLayer_positive layer)
        have := nextLayer_maxValue_lt hPositive hDone
        omega

theorem legal_layerAfter_all_ones {values : Sequence} (hLegal : Legal values) :
    (layerAfter (maxValue values) ⟨values, linearParent⟩).values.all
      (fun value => value == 1) = true :=
  layerAfter_all_ones (layer := ⟨values, linearParent⟩) hLegal.1 (Nat.le_refl _)

end ZeroY
