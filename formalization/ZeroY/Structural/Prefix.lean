import ZeroY.BMS.PaddedDescent

/-!
# 结构判据的规范化与前缀保持

公共尾零行不影响父项。任何列前缀内部的父项、阻挡节点和后缀比较均保留。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem bms_parent_none_of_trimHeight_le {array : Matrix} {row : Nat}
    (hRow : trimHeight array ≤ row) (column : Nat) : parent row array column = none := by
  cases hParent : parent row array column with
  | none => rfl
  | some p =>
      rcases parent_some_entry_lt hParent with ⟨left, right, _, hEntry, hLess⟩
      have := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry (by omega)
      omega

theorem bms_parent_trimZeroRows (array : Matrix) (row column : Nat) :
    parent row (trimZeroRows array) column = parent row array column := by
  by_cases hRow : row < trimHeight array
  · exact parent_trimZeroRows_of_lt array hRow column
  · rw [parent_trimZeroRows_eq_none_of_le array (by omega) column,
      bms_parent_none_of_trimHeight_le (by omega) column]

theorem bms_isAncestor_trimZeroRows (array : Matrix) (row ancestor column : Nat) :
    isAncestor (trimZeroRows array) row ancestor column = isAncestor array row ancestor column := by
  apply isAncestor_congr_below
  intro index _
  exact bms_parent_trimZeroRows array row index

theorem previousParent_trimZeroRows (array : Matrix) (row column : Nat) :
    previousParent (trimZeroRows array) row column = previousParent array row column := by
  cases row with
  | zero => rfl
  | succ row => exact bms_parent_trimZeroRows array row column

theorem columnEntry_suffix (array : Matrix) (column start row : Nat) :
    columnEntry (columnSuffix array column start) row = matrixEntry array column (start + row) := by
  simp [columnSuffix, columnEntry, matrixEntry, List.getElem?_drop]

theorem columnSuffix_trimZeroRows (array : Matrix) (column start : Nat) :
    ColumnEq (columnSuffix (trimZeroRows array) column start) (columnSuffix array column start) := by
  intro row
  simp only [columnEntry_suffix, matrixEntry_trimZeroRows]

namespace ColumnLe

theorem of_eq_of_le {a b c : List Nat} (hEq : ColumnEq a b) (hLe : ColumnLe b c) :
    ColumnLe a c := by
  rcases hLe with h | h
  · exact Or.inl (ColumnEq.trans hEq h)
  · exact Or.inr (ColumnLt.of_eq_of_lt hEq h)

theorem of_le_of_eq {a b c : List Nat} (hLe : ColumnLe a b) (hEq : ColumnEq b c) :
    ColumnLe a c := by
  rcases hLe with h | h
  · exact Or.inl (ColumnEq.trans h hEq)
  · exact Or.inr (ColumnLt.of_lt_of_eq h hEq)

theorem trans {a b c : List Nat} (hAB : ColumnLe a b) (hBC : ColumnLe b c) : ColumnLe a c := by
  rcases hAB with hEq | hLt
  · exact of_eq_of_le hEq hBC
  · rcases hBC with hEq | hNext
    · exact Or.inr (ColumnLt.of_lt_of_eq hLt hEq)
    · exact Or.inr (ColumnLt.trans hLt hNext)

end ColumnLe

theorem depthRegular_trimZeroRows {array : Matrix} (hRegular : DepthRegular array) :
    DepthRegular (trimZeroRows array) := by
  intro row column hColumn
  rw [length_trimZeroRows] at hColumn
  rw [bms_parent_trimZeroRows]
  have h := hRegular row column hColumn
  cases hParent : parent row array column with
  | none => simpa only [hParent, matrixEntry_trimZeroRows] using h
  | some p => simpa only [hParent, matrixEntry_trimZeroRows] using h

theorem blockerCondition_trimZeroRows {array : Matrix} (hBlocker : BlockerCondition array) :
    BlockerCondition (trimZeroRows array) := by
  intro row column q p hColumn hPrevious hParent hNe
  rw [length_trimZeroRows] at hColumn
  rw [previousParent_trimZeroRows] at hPrevious
  rw [bms_parent_trimZeroRows] at hParent
  rcases hBlocker row column q p hColumn hPrevious hParent hNe with ⟨z, hChain, hZ, hLe⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [bms_isAncestor_trimZeroRows] using hChain
  · simpa only [bms_parent_trimZeroRows] using hZ
  · exact ColumnLe.of_le_of_eq
      (ColumnLe.of_eq_of_le (columnSuffix_trimZeroRows array column (row + 1)) hLe)
      (ColumnEq.symm (columnSuffix_trimZeroRows array z (row + 1)))

theorem structural_trimZeroRows {array : Matrix} (hStructural : Structural array) :
    Structural (trimZeroRows array) :=
  ⟨depthRegular_trimZeroRows hStructural.1, blockerCondition_trimZeroRows hStructural.2⟩

theorem matrixEntry_take {array : Matrix} {count column : Nat} (hColumn : column < count)
    (row : Nat) : matrixEntry (array.take count) column row = matrixEntry array column row := by
  simp only [matrixEntry, List.getElem?_take_of_lt hColumn]

theorem bms_parent_take {array : Matrix} {count column : Nat}
    (hColumn : column < (array.take count).length) (row : Nat) :
    parent row (array.take count) column = parent row array column := by
  have hCount : column < count := Nat.lt_of_lt_of_le hColumn (List.length_take_le _ _)
  have hLength : column < array.length := by
    rw [List.length_take] at hColumn
    omega
  apply parent_eq_of_entry?_eq_below hColumn hLength
  intro earlier hEarlier entryRow
  simp only [entry?, List.getElem?_take_of_lt (by omega : earlier < count)]

theorem bms_isAncestor_take {array : Matrix} {count column : Nat}
    (hColumn : column < (array.take count).length) (row ancestor : Nat) :
    isAncestor (array.take count) row ancestor column = isAncestor array row ancestor column := by
  apply isAncestor_congr_below
  intro index hIndex
  exact bms_parent_take (by omega) row

theorem previousParent_take {array : Matrix} {count column : Nat}
    (hColumn : column < (array.take count).length) (row : Nat) :
    previousParent (array.take count) row column = previousParent array row column := by
  cases row with
  | zero => rfl
  | succ row => exact bms_parent_take hColumn row

theorem previousParent_some_lt {array : Matrix} {row column p : Nat}
    (hParent : previousParent array row column = some p) : p < column := by
  cases row with
  | zero =>
      cases column with
      | zero => simp [previousParent, linearParent] at hParent
      | succ column => simp only [previousParent, linearParent, Option.some.injEq] at hParent; omega
  | succ row => exact parent_some_lt hParent

theorem depthRegular_take {array : Matrix} (hRegular : DepthRegular array) (count : Nat) :
    DepthRegular (array.take count) := by
  intro row column hColumn
  have hBound : column < array.length ∧ column < count := by
    rw [List.length_take] at hColumn
    omega
  rw [bms_parent_take hColumn]
  have h := hRegular row column hBound.1
  cases hParent : parent row array column with
  | none => simpa only [hParent, matrixEntry_take hBound.2] using h
  | some p =>
      have hp := parent_some_lt hParent
      simpa only [hParent, matrixEntry_take hBound.2, matrixEntry_take (by omega : p < count)] using h

theorem blockerCondition_take {array : Matrix} (hBlocker : BlockerCondition array) (count : Nat) :
    BlockerCondition (array.take count) := by
  intro row column q p hColumn hPrevious hParent hNe
  have hBound : column < array.length ∧ column < count := by
    rw [List.length_take] at hColumn
    omega
  rw [previousParent_take hColumn] at hPrevious
  rw [bms_parent_take hColumn] at hParent
  rcases hBlocker row column q p hBound.1 hPrevious hParent hNe with ⟨z, hChain, hZ, hLe⟩
  have hQ : q < column := previousParent_some_lt hPrevious
  have hZColumn : z < column := by
    rcases hChain with rfl | hAncestor
    · exact hQ
    · exact Nat.lt_trans (isAncestor_lt hAncestor) hQ
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [bms_isAncestor_take (by omega : q < (array.take count).length)] using hChain
  · simpa only [bms_parent_take (by omega : z < (array.take count).length)] using hZ
  · simpa only [columnSuffix, List.getElem?_take_of_lt hBound.2,
      List.getElem?_take_of_lt (by omega : z < count)] using hLe

theorem structural_take {array : Matrix} (hStructural : Structural array) (count : Nat) :
    Structural (array.take count) :=
  ⟨depthRegular_take hStructural.1 count, blockerCondition_take hStructural.2 count⟩

theorem structural_trimmed_take {array : Matrix} (hStructural : Structural array) (count : Nat) :
    Structural (trimZeroRows (array.take count)) :=
  structural_trimZeroRows (structural_take hStructural count)

theorem structural_expand_zero {array : ValidArray} (hStructural : Structural array.raw) :
    Structural (array.expand 0).raw := by
  rw [array.raw_expand_zero]
  exact structural_trimmed_take hStructural _

theorem structural_expand_of_no_maximal {array : ValidArray}
    (hStructural : Structural array.raw) (hMaximal : maximalParentRow array.raw = none)
    (index : Nat) : Structural (array.expand index).raw := by
  have hEqual : array.expand index = array.expand 0 := by
    apply ValidArray.ext
    simp [ValidArray.raw_expand, YesMetaZFC.BMS.expand, expandRaw, hMaximal]
  rw [hEqual]
  exact structural_expand_zero hStructural

end ZeroY
