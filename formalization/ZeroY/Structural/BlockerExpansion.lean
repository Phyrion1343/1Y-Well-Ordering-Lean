import ZeroY.Structural.DepthExpansion

/-!
# 展开阻挡条件的复制
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

def BlockerAt (array : Matrix) (row column : Nat) : Prop :=
  ∀ q p, previousParent array row column = some q → parent row array column = some p →
    p ≠ q → ∃ z, (z = q ∨ isAncestor array row z q = true) ∧
      parent row array z = some p ∧
      ColumnLe (columnSuffix array column (row + 1)) (columnSuffix array z (row + 1))

theorem blockerAt_expand_prefix {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) (index row : Nat) {column : Nat}
    (hColumn : column < context.lastIndex) : BlockerAt (array.expand index).raw row column := by
  intro q p hQ hP hDistinct
  have hPrevious : previousParent (array.expand index).raw row column = previousParent array.raw row column := by
    cases row with
    | zero => rfl
    | succ row => exact parent_expand_prefix context index row hColumn
  rw [hPrevious] at hQ
  rw [parent_expand_prefix context index row hColumn] at hP
  obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker row column q p
    (by rw [context.array_length]; omega) hQ hP hDistinct
  have hQLt := previousParent_some_lt hQ
  have hZLt : z < column := by
    rcases hZPath with rfl | hZPath
    · exact hQLt
    · exact Nat.lt_trans (isAncestor_lt hZPath) hQLt
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [isAncestor_expand_prefix context index row _ (by omega : q < context.lastIndex)] using hZPath
  · rw [parent_expand_prefix context index row (by omega)]
    exact hZParent
  · exact ColumnLe.of_le_of_eq
      (ColumnLe.of_eq_of_le (suffix_expand_prefix context index (row + 1) hColumn) hZLe)
      (ColumnEq.symm (suffix_expand_prefix context index (row + 1) (by omega)))

theorem previousParent_copyColumn_nonroot {array : ValidArray} (context : ExpansionContext array)
    {index copy source : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hNonroot : source ≠ context.parentColumn) (row : Nat) :
    previousParent (array.expand index).raw row (copyColumn context copy source) =
      (previousParent array.raw row source).map (copyColumn context copy) := by
  cases row with
  | succ row => exact parent_copyColumn_nonroot context hCopy hSource hNonroot row
  | zero =>
      cases source with
      | zero =>
          have hGood : 0 < context.parentColumn := by omega
          simp [previousParent, copyColumn_good context copy hGood, linearParent]
      | succ source =>
          by_cases hGood : source + 1 < context.parentColumn
          · simp [previousParent, copyColumn_good context copy hGood,
              copyColumn_good context copy (by omega : source < context.parentColumn), linearParent]
          · have hBad : ¬ source < context.parentColumn := by omega
            simp only [previousParent, copyColumn, hGood, hBad, ↓reduceIte,
              Nat.succ_add, linearParent, Option.map_some]

theorem previousParent_copyColumn_high {array : ValidArray} (context : ExpansionContext array)
    {index copy source row : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hRow : context.maximalRow < row) :
    previousParent (array.expand index).raw row (copyColumn context copy source) =
      (previousParent array.raw row source).map (copyColumn context copy) := by
  cases row with
  | zero => omega
  | succ row => exact parent_copyColumn_high context hCopy hSource (by omega)

theorem previousParent_copied_root_low {array : ValidArray} (context : ExpansionContext array)
    {index copy row : Nat} (hCopy : copy + 1 ≤ index) (hRow : row ≤ context.maximalRow) :
    previousParent (array.expand index).raw row (context.copyPosition (copy + 1) 0) =
      (previousParent array.raw row context.lastIndex).map (copyColumn context copy) := by
  cases row with
  | succ row =>
      exact parent_copied_root_low_of_le context hCopy (by omega) (by omega)
  | zero =>
      have hLastPositive : 0 < context.lastIndex := Nat.zero_lt_of_lt context.parentColumn_lt_lastIndex
      have hLastEq : context.lastIndex - 1 + 1 = context.lastIndex := by omega
      have hPredBad : context.parentColumn ≤ context.lastIndex - 1 := by
        have := context.parentColumn_lt_lastIndex
        omega
      have hNewEq : context.copyPosition (copy + 1) 0 =
          copyColumn context copy (context.lastIndex - 1) + 1 := by
        rw [copyColumn_bad context copy hPredBad]
        simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart, Nat.add_mul,
          Nat.one_mul, Nat.add_zero, ExpansionContext.blockLength]
        omega
      change linearParent (context.copyPosition (copy + 1) 0) =
        (linearParent context.lastIndex).map (copyColumn context copy)
      rw [hNewEq]
      have hOld : linearParent context.lastIndex = some (context.lastIndex - 1) := by
        rw [← hLastEq]
        rfl
      rw [hOld]
      rfl

/-- 非边界复制条件：当前与前一行父项均按同一列嵌入复制。 -/
theorem blockerAt_copied_high {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) {index copy source row : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hRow : context.maximalRow ≤ row)
    (hPrevious : previousParent (array.expand index).raw row (copyColumn context copy source) =
      (previousParent array.raw row source).map (copyColumn context copy)) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  intro q p hQ hP hDistinct
  rw [hPrevious] at hQ
  rw [parent_copyColumn_high context hCopy hSource hRow] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw source with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
          have hOldDistinct : oldP ≠ oldQ := by
            intro hEqual
            apply hDistinct
            rw [← hP, ← hQ, hEqual]
          obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker row source oldQ oldP
            (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
          have hOldQLt := previousParent_some_lt hOldQ
          have hZLt : z < source := by
            rcases hZPath with rfl | hZPath
            · exact hOldQLt
            · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hZPath with rfl | hZPath
            · exact Or.inl hQ
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
              exact hZPath
          · rw [parent_copyColumn_high context hCopy (by omega) hRow, hZParent]
            simpa only [Option.map_some] using congrArg some hP
          · exact ColumnLe.of_le_of_eq
              (ColumnLe.of_eq_of_le (suffix_copyColumn_high context hCopy hSource (by omega)) hZLe)
              (ColumnEq.symm (suffix_copyColumn_high context hCopy (by omega) (by omega)))

theorem blockerAt_copied_nonroot_high {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) {index copy source row : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hNonroot : source ≠ context.parentColumn) (hRow : context.maximalRow ≤ row) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) :=
  blockerAt_copied_high hBlocker context hCopy hSource hRow
    (previousParent_copyColumn_nonroot context hCopy hSource hNonroot row)

theorem blockerAt_copied_above {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) {index copy source row : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hRow : context.maximalRow < row) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) :=
  blockerAt_copied_high hBlocker context hCopy hSource (Nat.le_of_lt hRow)
    (previousParent_copyColumn_high context hCopy hSource hRow)

/-- 最大活动行的新坏根以紧邻前一块坏根作阻挡；两者上方后缀相等。 -/
theorem blockerAt_copied_root_at {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) {index copy : Nat} (hCopy : copy + 1 ≤ index) :
    BlockerAt (array.expand index).raw context.maximalRow (context.copyPosition (copy + 1) 0) := by
  intro q p hQ hP _
  rw [previousParent_copied_root_low context hCopy (Nat.le_refl _)] at hQ
  rw [parent_copied_root_high_of_le context hCopy (Nat.le_refl _)] at hP
  cases hOldQ : previousParent array.raw context.maximalRow context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldQLt := previousParent_some_lt hOldQ
      have hRootPath : context.parentColumn = oldQ ∨
          isAncestor array.raw context.maximalRow context.parentColumn oldQ = true := by
        by_cases hEqual : context.parentColumn = oldQ
        · exact Or.inl hEqual
        · obtain ⟨z, hZPath, hZParent, _⟩ := hBlocker context.maximalRow context.lastIndex
            oldQ context.parentColumn (by rw [context.array_length]; omega)
            hOldQ context.parent_eq hEqual
          apply Or.inr
          rcases hZPath with rfl | hZPath
          · exact direct_parent_isAncestor hZParent
          · exact isAncestor_trans (direct_parent_isAncestor hZParent) hZPath
      refine ⟨copyColumn context copy context.parentColumn, ?_, ?_, ?_⟩
      · rcases hRootPath with hEqual | hPath
        · exact Or.inl ((congrArg (copyColumn context copy) hEqual).trans hQ)
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context (by omega)
            context.parentColumn_lt_lastIndex hOldQLt]
          exact hPath
      · rw [copyColumn_bad context copy (Nat.le_refl _), Nat.sub_self,
          parent_copied_root_high_of_le context (by omega) (Nat.le_refl _)]
        exact hP
      · have hLeft := suffix_copyColumn_high context hCopy
          context.parentColumn_lt_lastIndex (start := context.maximalRow + 1) (by omega)
        have hRight := suffix_copyColumn_high context (show copy ≤ index by omega)
          context.parentColumn_lt_lastIndex (start := context.maximalRow + 1) (by omega)
        rw [copyColumn_bad context (copy + 1) (Nat.le_refl _), Nat.sub_self] at hLeft
        exact Or.inl (ColumnEq.trans hLeft (ColumnEq.symm hRight))

theorem zero_root_path_copy {array : ValidArray} (context : ExpansionContext array)
    {index copy row source : Nat} (hCopy : copy ≤ index) (hRow : row < context.maximalRow)
    (hSource : source < context.lastIndex)
    (hPath : context.parentColumn = source ∨ isAncestor array.raw row context.parentColumn source = true) :
    context.parentColumn = copyColumn context copy source ∨
      isAncestor (array.expand index).raw row context.parentColumn (copyColumn context copy source) = true := by
  cases copy with
  | zero =>
      rw [copyColumn_zero]
      simpa only [isAncestor_expand_prefix context index row _ hSource] using hPath
  | succ copy =>
      have hFirst := context.first_copy_ancestor_of_lt (expansionIndex := index)
        (earlierCopy := 0) hCopy (by omega) hRow
      simp only [ExpansionContext.copyPosition_zero, Nat.add_zero] at hFirst
      apply Or.inr
      rcases hPath with hEqual | hAncestor
      · rw [← hEqual, copyColumn_bad context (copy + 1) (Nat.le_refl _), Nat.sub_self]
        exact hFirst
      · have hCopied := (isAncestor_copyColumn context hCopy context.parentColumn_lt_lastIndex hSource row).symm
        rw [hAncestor, copyColumn_bad context (copy + 1) (column := context.parentColumn) (Nat.le_refl _),
          Nat.sub_self] at hCopied
        exact isAncestor_trans hFirst hCopied.symm

/-- 低行非首列的父项在好部时，后缀不提升；跨块坏根阻挡回到第零坏根。 -/
theorem blockerAt_copied_parent_good {array : ValidArray} (hBlocker : BlockerCondition array.raw)
    (context : ExpansionContext array) {index copy source row oldP : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hNonroot : source ≠ context.parentColumn) (hRow : row < context.maximalRow)
    (hOldP : parent row array.raw source = some oldP) (hGood : oldP < context.parentColumn) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  intro q p hQ hP hDistinct
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP,
    Option.map_some, copyColumn_good context copy hGood] at hP
  have hPEq : oldP = p := Option.some.inj hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldDistinct : oldP ≠ oldQ := by
        intro hEqual
        apply hDistinct
        rw [← hPEq, ← hQ, ← hEqual, copyColumn_good context copy hGood]
      obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker row source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
      have hOldQLt := previousParent_some_lt hOldQ
      have hZLt : z < source := by
        rcases hZPath with rfl | hZPath
        · exact hOldQLt
        · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
      have hSourceSuffix := suffix_copyColumn_parent_good context hCopy hSource hNonroot hOldP hGood
      by_cases hRoot : z = context.parentColumn
      · subst z
        refine ⟨context.parentColumn, ?_, ?_, ?_⟩
        · rw [← hQ]
          exact zero_root_path_copy context hCopy hRow (by omega) hZPath
        · rw [parent_expand_prefix context index row context.parentColumn_lt_lastIndex, hZParent, hPEq]
        · exact ColumnLe.of_le_of_eq (ColumnLe.of_eq_of_le hSourceSuffix hZLe)
            (ColumnEq.symm (suffix_expand_prefix context index (row + 1) context.parentColumn_lt_lastIndex))
      · refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
        · rcases hZPath with rfl | hZPath
          · exact Or.inl hQ
          · apply Or.inr
            rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
            exact hZPath
        · rw [parent_copyColumn_nonroot context hCopy (by omega) hRoot row, hZParent,
            Option.map_some, copyColumn_good context copy hGood, hPEq]
        · exact ColumnLe.of_le_of_eq (ColumnLe.of_eq_of_le hSourceSuffix hZLe)
            (ColumnEq.symm (suffix_copyColumn_parent_good context hCopy (by omega) hRoot hZParent hGood))

end ZeroY.BMS
