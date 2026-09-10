import ZeroY.Expansion.Conjugacy

/-!
# 原前缀保持与新首列减一

0-Y 的完整坏部展开保留删尾前缀；存在新副本时，第一个新列的数值
恰是原末项减一。证明由实际 BM4 父图复制与有限求和塔完成。
-/

namespace ZeroY

open YesMetaZFC.BMS

/-- 任意高度的求和只依赖当前列及其左侧父图。 -/
theorem decodeTower_getD_of_parent_prefix {left right : Matrix} {bound : Nat}
    (hLeft : bound ≤ left.length) (hRight : bound ≤ right.length)
    (hParent : ∀ row column, column < bound → parent row left column = parent row right column)
    (row fuel : Nat) {column : Nat} (hColumn : column < bound) :
    (decodeTower left row fuel)[column]?.getD 0 = (decodeTower right row fuel)[column]?.getD 0 := by
  induction fuel generalizing row column with
  | zero =>
      simp only [decodeTower, List.getElem?_replicate_of_lt (show column < left.length by omega),
        List.getElem?_replicate_of_lt (show column < right.length by omega)]
  | succ fuel ih =>
      induction column using Nat.strongRecOn with
      | ind column ihColumn =>
          rw [decodeTower, sumRow_getD (parent := parent row left) (fun hp => parent_some_lt hp)
            (by simp only [decodeTower_length]; omega)]
          rw [decodeTower, sumRow_getD (parent := parent row right) (fun hp => parent_some_lt hp)
            (by simp only [decodeTower_length]; omega)]
          rw [← hParent row column hColumn]
          cases hp : parent row left column with
          | none => exact ih (row + 1) hColumn
          | some p =>
              simp only
              have hpLt := parent_some_lt hp
              rw [ih (row + 1) hColumn]
              exact congrArg (fun n => (decodeTower right (row + 1) fuel)[column]?.getD 0 + n)
                (ihColumn p hpLt (by omega))

theorem decodeTower_expand_prefix {array : ValidArray} (context : ExpansionContext array)
    (index row fuel : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    (decodeTower (array.expand index).raw row fuel)[column]?.getD 0 =
      (decodeTower array.raw row fuel)[column]?.getD 0 := by
  apply decodeTower_getD_of_parent_prefix
    (bound := context.lastIndex) ?_ ?_ (fun r c hc => BMS.parent_expand_prefix context index r hc)
    row fuel hColumn
  · rw [context.length_expand, Nat.succ_mul]
    simp only [ExpansionContext.blockLength]
    have := context.parentColumn_lt_lastIndex
    omega
  · rw [context.array_length]; omega

theorem expandYRaw_getD_prefix_of_context (s : Expr) (context : ExpansionContext (encode s))
    (count : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    (expandYRaw s.values count)[column]?.getD 0 = s.values[column]?.getD 0 := by
  let fuel := maxValue s.values + trimHeight ((encode s).expand count).raw
  have hHeight : trimHeight ((encode s).expand count).raw ≤ fuel := by dsimp [fuel]; omega
  have hValue : maxValue s.values ≤ 0 + fuel := by dsimp [fuel]; omega
  have h := decodeTower_expand_prefix context count 0 fuel hColumn
  rw [decodeTower_eq_decodeRaw_of_fuel _ hHeight,
    decodeRaw_expand_encode_of_context s context count,
    decodeTower_encode_mountain s 0 fuel hValue] at h
  exact h

/-- 完整坏部展开精确保留原来的删尾前缀。 -/
theorem expandYRaw_take_last_of_context (s : Expr) (context : ExpansionContext (encode s))
    (count : Nat) :
    (expandYRaw s.values count).take context.lastIndex = s.values.take context.lastIndex := by
  have hLength : context.lastIndex ≤ (expandYRaw s.values count).length := by
    rw [← decodeRaw_expand_encode_of_context s context count, decodeRaw_length,
      context.length_expand, Nat.succ_mul]
    simp only [ExpansionContext.blockLength]
    have := context.parentColumn_lt_lastIndex
    omega
  have hOriginal : context.lastIndex ≤ s.values.length := by
    have h := context.array_length
    rw [encode_length] at h
    omega
  apply List.ext_getElem (by simp only [List.length_take, Nat.min_eq_left hLength,
    Nat.min_eq_left hOriginal])
  intro column hLeft hRight
  have hc : column < context.lastIndex := by
    simp only [List.length_take] at hLeft
    omega
  have h := expandYRaw_getD_prefix_of_context s context count hc
  have hL : column < (expandYRaw s.values count).length := by omega
  have hR : column < s.values.length := by omega
  simpa only [List.getElem_take, List.getElem?_eq_getElem hL,
    List.getElem?_eq_getElem hR, Option.getD_some] using h

theorem first_copy_root_eq_last {array : ValidArray} (context : ExpansionContext array) :
    context.copyPosition 1 0 = context.lastIndex := by
  simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart, Nat.one_mul, Nat.add_zero,
    ExpansionContext.blockLength]
  have := context.parentColumn_lt_lastIndex
  omega

theorem parent_last_none_above {array : ValidArray} (context : ExpansionContext array)
    {row : Nat} (hRow : context.maximalRow < row) : parent row array.raw context.lastIndex = none := by
  have hSearch := context.maximal_row_eq
  unfold maximalParentRow at hSearch
  rw [context.array_length] at hSearch
  simp only at hSearch
  cases hp : parent row array.raw context.lastIndex with
  | none => rfl
  | some p =>
      have hBound := parent_some_row_lt_column_height hp
      have hMax := greatestBelow?_some_isGreatest hSearch row hBound (by simp [hp])
      omega

/-- 第一个新坏根在最大活动行的求和值比原末列恰少一。 -/
theorem decodeTower_newroot_add_one {array : ValidArray} (context : ExpansionContext array)
    {count row fuel : Nat} (hCount : 0 < count) (hRow : row ≤ context.maximalRow)
    (hFuel : context.maximalRow < row + fuel) :
    (decodeTower array.raw row fuel)[context.lastIndex]?.getD 0 =
      (decodeTower (array.expand count).raw row fuel)[context.lastIndex]?.getD 0 + 1 := by
  have hOriginal : context.lastIndex < array.raw.length := by rw [context.array_length]; omega
  have hExpanded : context.lastIndex < (array.expand count).raw.length := by
    rw [← first_copy_root_eq_last context]
    exact context.copyPosition_lt_length hCount context.blockLength_pos
  induction fuel generalizing row with
  | zero => omega
  | succ fuel ih =>
      by_cases hTop : row = context.maximalRow
      · subst row
        have hCopy := decodeTower_copyColumn_high context count hCount
          context.parentColumn_lt_lastIndex (Nat.le_refl context.maximalRow) (fuel + 1)
        have hCopyPosition : BMS.copyColumn context 1 context.parentColumn = context.lastIndex := by
          rw [BMS.copyColumn_bad context 1 (Nat.le_refl _), Nat.sub_self, first_copy_root_eq_last]
        rw [hCopyPosition] at hCopy
        rw [hCopy]
        conv => lhs; rw [decodeTower, sumRow_getD (parent := parent context.maximalRow array.raw)
          (fun hp => parent_some_lt hp) (by simpa only [decodeTower_length] using hOriginal),
          context.parent_eq]
        simp only
        rw [decodeTower_getD_of_parent_none array.raw (context.maximalRow + 1) fuel hOriginal
          (parent_last_none_above context (by omega))]
        change 1 + (decodeTower array.raw context.maximalRow (fuel + 1))[context.parentColumn]?.getD 0 = _
        exact Nat.add_comm _ _
      · have hLow : row < context.maximalRow := by omega
        have hParents : parent row (array.expand count).raw context.lastIndex =
            parent row array.raw context.lastIndex := by
          rw [← first_copy_root_eq_last context,
            BMS.parent_copied_root_low_of_le context hCount (by omega) hLow]
          have hZero : BMS.copyColumn context 0 = id := by
            funext column
            simp only [BMS.copyColumn, Nat.zero_mul, Nat.add_zero]
            split <;> rfl
          simp only [Nat.sub_self, hZero, Option.map_id, first_copy_root_eq_last]
          rfl
        rw [decodeTower, sumRow_getD (parent := parent row array.raw)
          (fun hp => parent_some_lt hp) (by simpa only [decodeTower_length] using hOriginal)]
        rw [decodeTower, sumRow_getD (parent := parent row (array.expand count).raw)
          (fun hp => parent_some_lt hp) (by simpa only [decodeTower_length] using hExpanded), hParents]
        cases hp : parent row array.raw context.lastIndex with
        | none => exact ih (by omega) (by omega)
        | some p =>
            simp only
            have hUpper := ih (row := row + 1) (by omega) (by omega)
            have hPrefix := decodeTower_expand_prefix context count row (fuel + 1) (parent_some_lt hp)
            change (sumRow (parent row (array.expand count).raw)
              (decodeTower (array.expand count).raw (row + 1) fuel))[p]?.getD 0 =
              (sumRow (parent row array.raw) (decodeTower array.raw (row + 1) fuel))[p]?.getD 0 at hPrefix
            omega

/-- 新首列的实际 0-Y 数值恰等于旧末项减一。 -/
theorem expandYRaw_newroot_of_context (s : Expr) (context : ExpansionContext (encode s))
    {count : Nat} (hCount : 0 < count) :
    (expandYRaw s.values count)[context.lastIndex]?.getD 0 =
      s.values[context.lastIndex]?.getD 0 - 1 := by
  let fuel := context.maximalRow + 1 + maxValue s.values + trimHeight ((encode s).expand count).raw
  have hHeight : trimHeight ((encode s).expand count).raw ≤ fuel := by dsimp [fuel]; omega
  have hValue : maxValue s.values ≤ 0 + fuel := by dsimp [fuel]; omega
  have hFuel : context.maximalRow < 0 + fuel := by dsimp [fuel]; omega
  have h := decodeTower_newroot_add_one context hCount (Nat.zero_le _) hFuel
  rw [decodeTower_eq_decodeRaw_of_fuel _ hHeight,
    decodeRaw_expand_encode_of_context s context count,
    decodeTower_encode_mountain s 0 fuel hValue] at h
  change s.values[context.lastIndex]?.getD 0 =
    (expandYRaw s.values count)[context.lastIndex]?.getD 0 + 1 at h
  omega

/-- 非空合法式无活动行，当且仅当其末项为 1。 -/
theorem expansionSite_none_iff_last_one (s : Expr) (hNonempty : s.values ≠ []) :
    expansionSite s.values = none ↔ s.values[s.values.length - 1]?.getD 0 = 1 := by
  have hPositive : 0 < s.values.length := List.length_pos_iff.mpr hNonempty
  have hLast : s.values.length - 1 < s.values.length := by omega
  have hArrayLength : (encode s).raw.length = (s.values.length - 1) + 1 := by
    rw [encode_length]
    omega
  constructor
  · intro hNone
    have hMaximal := (expansionSite_none_iff s).mp hNone
    have hParent : parent 0 (encode s).raw (s.values.length - 1) = none := by
      cases hp : parent 0 (encode s).raw (s.values.length - 1) with
      | none => rfl
      | some p =>
          unfold maximalParentRow at hMaximal
          rw [hArrayLength] at hMaximal
          simp only at hMaximal
          have hBound := parent_some_row_lt_column_height hp
          have hFalse := greatestBelow?_eq_none_iff.mp hMaximal 0 hBound
          simp only [hp, Option.isSome_some, Bool.true_eq_false] at hFalse
    rw [bms_parent_encode_mountain] at hParent
    exact (layerParent_none_iff_value_one (legal_initial_rootInvariant s.legal) hLast).mp hParent
  · intro hOne
    have hParent : parent 0 (encode s).raw (s.values.length - 1) = none := by
      rw [bms_parent_encode_mountain]
      exact (layerParent_none_iff_value_one (legal_initial_rootInvariant s.legal) hLast).mpr hOne
    have hAll : ∀ row, parent row (encode s).raw (s.values.length - 1) = none := by
      intro row
      induction row with
      | zero => exact hParent
      | succ row ih => exact parent_succ_none_of_none (encode s).raw ih
    apply (expansionSite_none_iff s).mpr
    unfold maximalParentRow
    rw [hArrayLength]
    simp only
    apply greatestBelow?_eq_none_iff.mpr
    intro row _
    simp only [hAll row, Option.isSome_none]

end ZeroY
