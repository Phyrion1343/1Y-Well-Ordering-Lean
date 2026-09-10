import ZeroY.Structural.BlockerExpansion
import ZeroY.Structural.CopyOrder

/-!
# 任意结构矩阵在 BM4 展开下封闭

同块比较保序与直接父项复制共同处理阻挡条件；不存在标准性或展开共轭前提。
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

theorem suffix_copyColumn_eq_lifted {array : ValidArray} (context : ExpansionContext array)
    {index copy source : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hBad : context.parentColumn ≤ source) (start : Nat) :
    ColumnEq (columnSuffix (array.expand index).raw (copyColumn context copy source) start)
      (liftedSuffix context copy source start) := by
  have hLocal : source - context.parentColumn < context.blockLength := by
    simp only [ExpansionContext.blockLength]
    omega
  have hSourceEq : context.parentColumn + (source - context.parentColumn) = source := by omega
  intro row
  rw [columnEntry_suffix, liftedSuffix_entry, copyColumn_bad context copy hBad,
    matrixEntry_copied context hCopy hLocal, hSourceEq]
  rfl

/-- 新块首列在最大父行处严格小于前一块的虚拟末列，之前各行相等。 -/
theorem newroot_suffix_lt_ghost {array : ValidArray} (context : ExpansionContext array)
    {index copy row : Nat} (hCopy : copy + 1 ≤ index) (hRow : row < context.maximalRow) :
    ColumnLt (columnSuffix (array.expand index).raw (context.copyPosition (copy + 1) 0) (row + 1))
      (liftedSuffix context copy context.lastIndex (row + 1)) := by
  refine ⟨context.maximalRow - (row + 1), ?_, ?_⟩
  · intro earlier hEarlier
    have hLower : row + 1 + earlier < context.maximalRow := by omega
    rw [columnEntry_suffix, liftedSuffix_entry, newroot_entry_eq_ghost_below context hCopy hLower]
    have hAncestor := isAncestor_of_lt_row hLower (direct_parent_isAncestor context.parent_eq)
    have hLast : context.parentColumn + (context.lastIndex - context.parentColumn) = context.lastIndex := by
      have := context.parentColumn_lt_lastIndex
      omega
    have hAscending : ascending array.raw context.maximalRow context.parentColumn
        (context.lastIndex - context.parentColumn) (row + 1 + earlier) = true := by
      simp [ascending, hLower, hLast, hAncestor]
    simp [liftedEntry, hAscending]
  · have hAt : row + 1 + (context.maximalRow - (row + 1)) = context.maximalRow := by omega
    rw [columnEntry_suffix, liftedSuffix_entry, hAt]
    have hAscending : ascending array.raw context.maximalRow context.parentColumn
        (context.lastIndex - context.parentColumn) context.maximalRow = false := by
      simp [ascending]
    simpa only [liftedEntry, hAscending, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
      newroot_entry_lt_ghost_at context hCopy

/-- 低行非首列的父项在坏部时，原阻挡节点移到同一复制块。 -/
theorem blockerAt_copied_parent_bad {array : ValidArray} (hStructural : Structural array.raw)
    (context : ExpansionContext array) {index copy source row oldP : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hOldP : parent row array.raw source = some oldP) (hBad : context.parentColumn ≤ oldP) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  have hParentLt := parent_some_lt hOldP
  have hSourceBad : context.parentColumn < source := by omega
  have hNonroot : source ≠ context.parentColumn := by omega
  intro q p hQ hP hDistinct
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP] at hP
  simp only [Option.map_some, Option.some.injEq] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldDistinct : oldP ≠ oldQ := by
        intro hEqual
        apply hDistinct
        rw [← hP, ← hQ, hEqual]
      obtain ⟨z, hZPath, hZParent, hZLe⟩ := hStructural.2 row source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
      have hOldQLt := previousParent_some_lt hOldQ
      have hZLt : z < source := by
        rcases hZPath with rfl | hZPath
        · exact hOldQLt
        · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
      have hPZ := parent_some_lt hZParent
      have hZBad : context.parentColumn < z := by omega
      refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
      · rcases hZPath with rfl | hZPath
        · exact Or.inl hQ
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
          exact hZPath
      · rw [parent_copyColumn_nonroot context hCopy (by omega) (by omega) row, hZParent]
        simpa only [Option.map_some] using congrArg some hP
      · have hLifted := liftedSuffix_le_of_common_parent context hStructural.1
          (by rw [context.array_length]; omega) (by rw [context.array_length]; omega)
          hSourceBad hZBad (hOldP.trans hZParent.symm) hZLe copy
        exact ColumnLe.of_le_of_eq
          (ColumnLe.of_eq_of_le (suffix_copyColumn_eq_lifted context hCopy hSource (by omega) (row + 1)) hLifted)
          (ColumnEq.symm (suffix_copyColumn_eq_lifted context hCopy (by omega) (by omega) (row + 1)))

/-- 低行新坏根的阻挡来自前一块；虚拟末列在最大父行处严格压住它。 -/
theorem blockerAt_copied_root_below {array : ValidArray} (hStructural : Structural array.raw)
    (context : ExpansionContext array) {index copy row : Nat}
    (hCopy : copy + 1 ≤ index) (hRow : row < context.maximalRow) :
    BlockerAt (array.expand index).raw row (context.copyPosition (copy + 1) 0) := by
  intro q p hQ hP hDistinct
  rw [previousParent_copied_root_low context hCopy (Nat.le_of_lt hRow)] at hQ
  rw [parent_copied_root_low_of_le context hCopy (by omega) hRow] at hP
  simp only [Nat.add_sub_cancel] at hP
  cases hOldQ : previousParent array.raw row context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw context.lastIndex with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
          have hOldDistinct : oldP ≠ oldQ := by
            intro hEqual
            apply hDistinct
            rw [← hP, ← hQ, hEqual]
          obtain ⟨z, hZPath, hZParent, hZLe⟩ := hStructural.2 row context.lastIndex oldQ oldP
            (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
          have hOldQLt := previousParent_some_lt hOldQ
          have hZLt : z < context.lastIndex := by
            rcases hZPath with rfl | hZPath
            · exact hOldQLt
            · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
          have hRootAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
          have hOldPBad := ancestor_le_parent hOldP hRootAncestor
          have hPZ := parent_some_lt hZParent
          have hZBad : context.parentColumn < z := by omega
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hZPath with rfl | hZPath
            · exact Or.inl hQ
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context (by omega) hZLt hOldQLt]
              exact hZPath
          · rw [parent_copyColumn_nonroot context (by omega) hZLt (by omega) row, hZParent]
            simpa only [Option.map_some] using congrArg some hP
          · have hLifted := liftedSuffix_le_of_common_parent context hStructural.1
              (by rw [context.array_length]; omega) (by rw [context.array_length]; omega)
              context.parentColumn_lt_lastIndex hZBad (hOldP.trans hZParent.symm) hZLe copy
            exact ColumnLe.of_le_of_eq
              (ColumnLe.trans (Or.inr (newroot_suffix_lt_ghost context hCopy hRow)) hLifted)
              (ColumnEq.symm (suffix_copyColumn_eq_lifted context (by omega) hZLt (by omega) (row + 1)))

theorem blockerCondition_expand_of_context {array : ValidArray} (hStructural : Structural array.raw)
    (context : ExpansionContext array) (index : Nat) : BlockerCondition (array.expand index).raw := by
  intro row column q p hColumn hQ hP hDistinct
  have hAt : BlockerAt (array.expand index).raw row column := by
    by_cases hPrefix : column < context.lastIndex
    · exact blockerAt_expand_prefix hStructural.2 context index row hPrefix
    · have hNotGood : context.parentColumn ≤ column := by
        have := context.parentColumn_lt_lastIndex
        omega
      rcases context.exists_copyPosition_of_not_good hColumn hNotGood with
        ⟨copy, localColumn, hCopy, hLocal, rfl⟩
      have hSource : context.parentColumn + localColumn < context.lastIndex := by
        simp only [ExpansionContext.blockLength] at hLocal
        omega
      by_cases hZero : localColumn = 0
      · subst localColumn
        cases copy with
        | zero =>
            simp only [ExpansionContext.copyPosition_zero, Nat.add_zero] at hPrefix
            exact False.elim (hPrefix context.parentColumn_lt_lastIndex)
        | succ copy =>
            by_cases hLow : row < context.maximalRow
            · exact blockerAt_copied_root_below hStructural context hCopy hLow
            · by_cases hEqual : row = context.maximalRow
              · subst row
                exact blockerAt_copied_root_at hStructural.2 context hCopy
              · have hAbove := blockerAt_copied_above hStructural.2 context hCopy
                  context.parentColumn_lt_lastIndex (by omega : context.maximalRow < row)
                rw [copyColumn_bad context (copy + 1) (Nat.le_refl _), Nat.sub_self] at hAbove
                exact hAbove
      · rw [← copyColumn_local context copy localColumn]
        have hNonroot : context.parentColumn + localColumn ≠ context.parentColumn := by omega
        by_cases hLow : row < context.maximalRow
        · cases hOldP : parent row array.raw (context.parentColumn + localColumn) with
          | none =>
              intro q p _ hP _
              rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP] at hP
              contradiction
          | some oldP =>
              by_cases hGood : oldP < context.parentColumn
              · exact blockerAt_copied_parent_good hStructural.2 context hCopy hSource
                  hNonroot hLow hOldP hGood
              · exact blockerAt_copied_parent_bad hStructural context hCopy hSource hOldP (by omega)
        · exact blockerAt_copied_nonroot_high hStructural.2 context hCopy hSource hNonroot (by omega)
  exact hAt q p hQ hP hDistinct

theorem blockerCondition_expand {array : ValidArray} (hStructural : Structural array.raw) (index : Nat) :
    BlockerCondition (array.expand index).raw := by
  cases hMaximal : maximalParentRow array.raw with
  | none => exact (structural_expand_of_no_maximal hStructural hMaximal index).2
  | some maximalRow =>
      let context := Classical.choice (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
      exact blockerCondition_expand_of_context hStructural context index

/-- 任意 I+S 矩阵在每一个 BM4 展开指标下仍满足 I+S。 -/
theorem structural_expand {array : ValidArray} (hStructural : Structural array.raw) (index : Nat) :
    Structural (array.expand index).raw :=
  ⟨depthRegular_expand hStructural.1 index, blockerCondition_expand hStructural index⟩

end ZeroY.BMS
