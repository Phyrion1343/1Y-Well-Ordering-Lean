import ZeroY.Expansion
import ZeroY.Image
import YesMetaZFC.BMS.Decomposition

/-!
# 两个独立展开算法选择同一最高活动行

山脉算法按输入最大值搜索，BM4 按矩阵列高搜索。这里证明两个有限上界
覆盖的非空父项集合完全相同，因此搜索结果相同。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem bms_parent_encode_mountain (s : Expr) (row : Nat) :
    parent row (encode s).raw = mountainParent s.values row := by
  rw [encode_raw_eq_encodeRaw, parent_encodeRaw s.legal]
  rfl

theorem mountainParent_none_of_maxValue_le {s : Sequence} (hLegal : Legal s)
    {row : Nat} (hRow : maxValue s ≤ row) (column : Nat) :
    mountainParent s row column = none := by
  exact layerParent_none_of_all_ones
    (layerAfter_all_ones (layer := ⟨s, linearParent⟩) hLegal.1 hRow) column

theorem parent_some_row_lt_column_height {array : Matrix} {row column found : Nat}
    (hParent : parent row array column = some found) :
    row < (array[column]?.map List.length).getD 0 := by
  obtain ⟨_, value, _, hEntry, _⟩ := parent_some_entry_lt hParent
  unfold entry? at hEntry
  cases hColumn : array[column]? with
  | none => simp [hColumn] at hEntry
  | some source =>
      simp only [hColumn, Option.bind_some] at hEntry
      simpa [hColumn] using (List.getElem?_eq_some_iff.mp hEntry).1

theorem greatestBelow?_eq_of_support {first second : Nat} {predicate : Nat → Bool}
    (hFirst : ∀ row, predicate row = true → row < first)
    (hSecond : ∀ row, predicate row = true → row < second) :
    greatestBelow? first predicate = greatestBelow? second predicate := by
  cases hSearch : greatestBelow? first predicate with
  | none =>
      symm
      apply greatestBelow?_eq_none_iff.mpr
      intro row _
      cases hValue : predicate row with
      | false => rfl
      | true => simpa only [hValue] using
          greatestBelow?_eq_none_iff.mp hSearch row (hFirst row hValue)
  | some row =>
      symm
      apply greatestBelow?_eq_some_iff.mpr
      have hValue := greatestBelow?_some_satisfies hSearch
      refine ⟨hSecond row hValue, hValue, ?_⟩
      intro candidate _ hCandidate
      exact greatestBelow?_some_isGreatest hSearch candidate
        (hFirst candidate hCandidate) hCandidate

theorem maximalParentRow_encode (s : Expr) :
    maximalParentRow (encode s).raw =
      greatestBelow? (maxValue s.values)
        (fun row => (mountainParent s.values row (s.values.length - 1)).isSome) := by
  have hLength := encode_length s
  cases hValuesLength : s.values.length with
  | zero =>
      have hEmpty : s.values = [] := List.length_eq_zero_iff.mp hValuesLength
      have hArrayLength : (encode s).raw.length = 0 := hLength.trans hValuesLength
      simp only [maximalParentRow, hArrayLength, hEmpty, maxValue,
        List.foldl_nil, greatestBelow?]
  | succ last =>
      have hArrayLength : (encode s).raw.length = last + 1 := hLength.trans hValuesLength
      simp only [maximalParentRow, hArrayLength, Nat.add_sub_cancel,
        bms_parent_encode_mountain]
      apply greatestBelow?_eq_of_support
      · intro row hSome
        cases hParent : mountainParent s.values row last with
        | none => simp [hParent] at hSome
        | some found =>
            apply parent_some_row_lt_column_height
            simpa only [bms_parent_encode_mountain] using hParent
      · intro row hSome
        by_cases hRow : row < maxValue s.values
        · exact hRow
        · have hNone := mountainParent_none_of_maxValue_le s.legal
            (Nat.le_of_not_gt hRow) last
          simp [hNone] at hSome

theorem expansionSite_eq_bms (s : Expr) :
    expansionSite s.values =
      (maximalParentRow (encode s).raw).bind fun row =>
        (parent row (encode s).raw ((encode s).raw.length - 1)).map
          (fun root => (row, root)) := by
  simp only [expansionSite, maximalParentRow_encode, bms_parent_encode_mountain, encode_length]

theorem expansionSite_of_context (s : Expr) (context : ExpansionContext (encode s)) :
    expansionSite s.values = some (context.maximalRow, context.parentColumn) := by
  rw [expansionSite_eq_bms, context.maximal_row_eq, Option.bind_some,
    context.array_length, Nat.add_sub_cancel, context.parent_eq]
  rfl

theorem expansionSite_none_iff (s : Expr) :
    expansionSite s.values = none ↔ maximalParentRow (encode s).raw = none := by
  constructor
  · intro hNone
    cases hMaximal : maximalParentRow (encode s).raw with
    | none => rfl
    | some row =>
        obtain ⟨context⟩ := exists_expansionContext_of_maximalParentRow_eq_some hMaximal
        rw [expansionSite_of_context s context] at hNone
        contradiction
  · intro hNone
    rw [expansionSite_eq_bms, hNone]
    rfl

end ZeroY
