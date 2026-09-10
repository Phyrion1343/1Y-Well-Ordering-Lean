import ZeroY.Structural.ExpansionParents

/-!
# 展开副本的补零坐标公式
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

theorem uniformHeight_valid (array : ValidArray) : UniformHeight (trimHeight array.raw) array.raw := by
  rcases rectangular_iff_exists_uniformHeight.mp array.rectangular_eq with ⟨height, hUniform⟩
  have h := uniformHeight_trimZeroRows hUniform
  rwa [array.trimmed_eq] at h

theorem matrixEntry_zero_of_height_le {array : Matrix} {height : Nat}
    (hUniform : UniformHeight height array) {row : Nat} (hRow : height ≤ row) (column : Nat) :
    matrixEntry array column row = 0 := by
  rw [matrixEntry_eq_entry_getD]
  cases hEntry : entry? array column row with
  | none => rfl
  | some value =>
      have := row_lt_uniformHeight_of_entry?_eq_some hUniform hEntry
      omega

theorem maximalRow_lt_height {array : ValidArray} (context : ExpansionContext array) :
    context.maximalRow < trimHeight array.raw := by
  rcases parent_some_entry_lt context.parent_eq with ⟨_, right, _, hEntry, hLess⟩
  exact row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry (by omega)

def rowIncrement {array : ValidArray} (context : ExpansionContext array) (row : Nat) : Nat :=
  matrixEntry array.raw context.lastIndex row - matrixEntry array.raw context.parentColumn row

/-- 任意有效副本的补零条目，精确对应 BM4 的加量公式。 -/
theorem matrixEntry_copied {array : ValidArray} (context : ExpansionContext array)
    {index copy localColumn : Nat} (hCopy : copy ≤ index)
    (hLocal : localColumn < context.blockLength) (row : Nat) :
    matrixEntry (array.expand index).raw (context.copyPosition copy localColumn) row =
      matrixEntry array.raw (context.parentColumn + localColumn) row +
        if ascending array.raw context.maximalRow context.parentColumn localColumn row then
          copy * rowIncrement context row else 0 := by
  change matrixEntry (trimZeroRows (expandRaw array.raw index)) _ _ = _
  rw [matrixEntry_trimZeroRows]
  by_cases hRow : row < trimHeight array.raw
  · have hUniform := uniformHeight_valid array
    rcases context.exists_badPart_entry hUniform hLocal hRow with
      ⟨column, value, hColumn, hValue⟩
    rcases context.exists_badPart_entry hUniform context.blockLength_pos hRow with
      ⟨firstColumn, firstValue, hFirstColumn, hFirstValue⟩
    rcases exists_entry_of_uniformHeight hUniform
      (by rw [context.array_length]; omega : context.lastIndex < array.raw.length) hRow with
      ⟨lastValue, hLastValue⟩
    have hSource : entry? array.raw (context.parentColumn + localColumn) row = some value := by
      rw [← context.entry?_badPart hLocal]
      simp [entry?, hColumn, hValue]
    have hFirst : entry? array.raw context.parentColumn row = some firstValue := by
      have h := context.entry?_badPart (row := row) context.blockLength_pos
      simp only [Nat.add_zero] at h
      rw [← h]
      simp [entry?, hFirstColumn, hFirstValue]
    have hFirstHead : (context.badPart.head?.getD [])[row]? = some firstValue := by
      rw [List.head?_eq_getElem?, hFirstColumn]
      exact hFirstValue
    have hLastGetD := ExpansionContext.getD_getElem?_of_entry?_eq_some array.raw hLastValue
    simp only [matrixEntry_eq_entry_getD, rowIncrement,
      context.entry?_expandRaw_copy hCopy hLocal,
      ExpansionContext.entry?_copyBlock _ _ _ _ _ _ _ _ _ _ hColumn hValue,
      matrixEntry_eq_entry_getD, hSource, hFirst, hLastValue,
      ExpansionContext.copiedValue, hFirstHead, hLastGetD, Option.getD_some]
    split <;> simp
  · have hUniform := uniformHeight_valid array
    have hExpanded := uniformHeight_expandRaw (index := index) hUniform
    have hNotAscending : ascending array.raw context.maximalRow context.parentColumn localColumn row = false := by
      have := maximalRow_lt_height context
      simp [ascending, show ¬ row < context.maximalRow by omega]
    rw [matrixEntry_zero_of_height_le hExpanded (by omega),
      matrixEntry_zero_of_height_le hUniform (by omega), hNotAscending]
    simp

theorem matrixEntry_expand_prefix {array : ValidArray} (context : ExpansionContext array)
    (index row : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    matrixEntry (array.expand index).raw column row = matrixEntry array.raw column row := by
  change matrixEntry (trimZeroRows (expandRaw array.raw index)) column row = _
  rw [matrixEntry_trimZeroRows, matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD,
    context.entry?_expandRaw_eq_of_lt_lastIndex index hColumn]

theorem rowIncrement_pos {array : ValidArray} (context : ExpansionContext array)
    {row : Nat} (hRow : row < context.maximalRow) : 0 < rowIncrement context row := by
  have hAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  rcases ancestor_entries_lt hAncestor with ⟨left, right, hLeft, hRight, hLess⟩
  simpa only [rowIncrement, matrixEntry_eq_entry_getD, hLeft, hRight, Option.getD_some] using
    Nat.sub_pos_of_lt hLess

theorem suffix_copyColumn_high {array : ValidArray} (context : ExpansionContext array)
    {index copy source start : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hStart : context.maximalRow ≤ start) :
    ColumnEq (columnSuffix (array.expand index).raw (copyColumn context copy source) start)
      (columnSuffix array.raw source start) := by
  intro row
  simp only [columnEntry_suffix]
  by_cases hGood : source < context.parentColumn
  · rw [copyColumn_good context copy hGood, matrixEntry_expand_prefix context index _ hSource]
  · have hLocal : source - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    have hNotAscending : ascending array.raw context.maximalRow context.parentColumn
        (source - context.parentColumn) (start + row) = false := by
      simp [ascending, show ¬ start + row < context.maximalRow by omega]
    rw [copyColumn_bad context copy (by omega), matrixEntry_copied context hCopy hLocal,
      hNotAscending]
    have : context.parentColumn + (source - context.parentColumn) = source := by omega
    rw [this]
    simp

/-- 父项位于好部的非坏根节点，其当前行以上的整个后缀都不提升。 -/
theorem suffix_copyColumn_parent_good {array : ValidArray} (context : ExpansionContext array)
    {index copy source parentColumn row : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hNonroot : source ≠ context.parentColumn)
    (hParent : parent row array.raw source = some parentColumn)
    (hGood : parentColumn < context.parentColumn) :
    ColumnEq (columnSuffix (array.expand index).raw (copyColumn context copy source) (row + 1))
      (columnSuffix array.raw source (row + 1)) := by
  intro offset
  simp only [columnEntry_suffix]
  by_cases hSourceGood : source < context.parentColumn
  · rw [copyColumn_good context copy hSourceGood, matrixEntry_expand_prefix context index _ hSource]
  · have hLocal : source - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    have hSourceEq : context.parentColumn + (source - context.parentColumn) = source := by omega
    have hNoAncestor : isAncestor array.raw (row + 1 + offset) context.parentColumn source = false := by
      cases hAncestor : isAncestor array.raw (row + 1 + offset) context.parentColumn source with
      | false => rfl
      | true =>
          have hLower := isAncestor_of_lt_row (by omega : row < row + 1 + offset) hAncestor
          have := ancestor_le_parent hParent hLower
          omega
    have hNotAscending : ascending array.raw context.maximalRow context.parentColumn
        (source - context.parentColumn) (row + 1 + offset) = false := by
      simp [ascending, hSourceEq, hNoAncestor, show source - context.parentColumn ≠ 0 by omega]
    rw [copyColumn_bad context copy (column := source) (by omega),
      matrixEntry_copied context hCopy hLocal, hNotAscending, hSourceEq]
    simp

theorem suffix_expand_prefix {array : ValidArray} (context : ExpansionContext array)
    (index start : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    ColumnEq (columnSuffix (array.expand index).raw column start) (columnSuffix array.raw column start) := by
  intro row
  simp only [columnEntry_suffix, matrixEntry_expand_prefix context index _ hColumn]

/-- 将原末列保留为比较用的虚拟副本时，下一坏根在最大父行以下与它相等。 -/
theorem newroot_entry_eq_ghost_below {array : ValidArray} (context : ExpansionContext array)
    {index copy row : Nat} (hCopy : copy + 1 ≤ index) (hRow : row < context.maximalRow) :
    matrixEntry (array.expand index).raw (context.copyPosition (copy + 1) 0) row =
      matrixEntry array.raw context.lastIndex row + copy * rowIncrement context row := by
  have hAscending : ascending array.raw context.maximalRow context.parentColumn 0 row = true := by
    simp [ascending, hRow]
  rw [matrixEntry_copied context hCopy context.blockLength_pos row, hAscending]
  simp only [Nat.add_zero]
  have hDelta := rowIncrement_pos context hRow
  unfold rowIncrement at hDelta ⊢
  simp only [Nat.add_mul, Nat.one_mul]
  simp <;> omega

theorem newroot_entry_lt_ghost_at {array : ValidArray} (context : ExpansionContext array)
    {index copy : Nat} (hCopy : copy + 1 ≤ index) :
    matrixEntry (array.expand index).raw (context.copyPosition (copy + 1) 0) context.maximalRow <
      matrixEntry array.raw context.lastIndex context.maximalRow := by
  have hAscending : ascending array.raw context.maximalRow context.parentColumn 0 context.maximalRow = false := by
    simp [ascending]
  rw [matrixEntry_copied context hCopy context.blockLength_pos context.maximalRow, hAscending]
  simp only [Nat.add_zero]
  rcases parent_some_entry_lt context.parent_eq with ⟨left, right, hLeft, hRight, hLess⟩
  simp only [matrixEntry_eq_entry_getD, hLeft, hRight, Option.getD_some]
  simp <;> omega

end ZeroY.BMS
