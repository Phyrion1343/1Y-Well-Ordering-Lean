import ZeroY.Structural.ExpansionCoordinates

/-!
# BM4 展开保持深度正规性
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

def RegularAt (array : Matrix) (row column : Nat) : Prop :=
  match parent row array column with
  | none => matrixEntry array column row = 0
  | some p => matrixEntry array column row = matrixEntry array p row + 1

theorem ascending_false_of_no_root_ancestor {array : ValidArray}
    (context : ExpansionContext array) {row localColumn : Nat} (hPositive : 0 < localColumn)
    (hAncestor : isAncestor array.raw row context.parentColumn
      (context.parentColumn + localColumn) = false) :
    ascending array.raw context.maximalRow context.parentColumn localColumn row = false := by
  simp [ascending, hAncestor, show localColumn ≠ 0 by omega]

theorem regularAt_copied_nonroot {array : ValidArray} (hRegular : DepthRegular array.raw)
    (context : ExpansionContext array) {index copy localColumn : Nat}
    (hCopy : copy ≤ index) (hPositive : 0 < localColumn)
    (hLocal : localColumn < context.blockLength) (row : Nat) :
    RegularAt (array.expand index).raw row (context.copyPosition copy localColumn) := by
  have hTarget : context.parentColumn + localColumn < context.lastIndex := by
    simp only [ExpansionContext.blockLength] at hLocal
    omega
  have hOld := hRegular row (context.parentColumn + localColumn)
    (by rw [context.array_length]; omega)
  unfold RegularAt
  rw [parent_copied_nonroot_of_le context hCopy row hPositive hLocal]
  cases hParent : parent row array.raw (context.parentColumn + localColumn) with
  | none =>
      have hNoRoot : isAncestor array.raw row context.parentColumn
          (context.parentColumn + localColumn) = false :=
        isAncestor_eq_false_of_parent_none hParent
      have hNotAscending := ascending_false_of_no_root_ancestor context hPositive hNoRoot
      simp only [hParent] at hOld
      simp only [Option.map_none]
      rw [matrixEntry_copied context hCopy hLocal row, hNotAscending, if_neg Bool.false_ne_true]
      omega
  | some p =>
      simp only [hParent] at hOld
      simp only [Option.map_some]
      have hp : p < context.lastIndex := Nat.lt_trans (parent_some_lt hParent) hTarget
      by_cases hGood : p < context.parentColumn
      · have hNoRoot : isAncestor array.raw row context.parentColumn
            (context.parentColumn + localColumn) = false := by
          cases hAncestor : isAncestor array.raw row context.parentColumn
              (context.parentColumn + localColumn) with
          | false => rfl
          | true => have := ancestor_le_parent hParent hAncestor; omega
        have hNotAscending := ascending_false_of_no_root_ancestor context hPositive hNoRoot
        rw [copyColumn_good context copy hGood, matrixEntry_expand_prefix context index row hp,
          matrixEntry_copied context hCopy hLocal row, hNotAscending, if_neg Bool.false_ne_true]
        omega
      · have hpLocal : p - context.parentColumn < context.blockLength := by
          simp only [ExpansionContext.blockLength]
          omega
        have hSourceEq : context.parentColumn + (p - context.parentColumn) = p := by omega
        have hAscending : ascending array.raw context.maximalRow context.parentColumn
            (p - context.parentColumn) row =
          ascending array.raw context.maximalRow context.parentColumn localColumn row := by
          apply ExpansionContext.ascending_eq_of_ancestor
          rw [hSourceEq]
          exact direct_parent_isAncestor hParent
        rw [copyColumn_bad context copy (by omega),
          matrixEntry_copied context hCopy hpLocal row,
          matrixEntry_copied context hCopy hLocal row, hSourceEq, hAscending]
        omega

theorem regularAt_copied_root_high {array : ValidArray} (hRegular : DepthRegular array.raw)
    (context : ExpansionContext array) {index copy row : Nat}
    (hCopy : copy ≤ index) (hRow : context.maximalRow ≤ row) :
    RegularAt (array.expand index).raw row (context.copyPosition copy 0) := by
  have hRoot := context.parentColumn_lt_lastIndex
  have hOld := hRegular row context.parentColumn (by rw [context.array_length]; omega)
  have hNotAscending : ascending array.raw context.maximalRow context.parentColumn 0 row = false := by
    simp [ascending, show ¬ row < context.maximalRow by omega]
  unfold RegularAt
  rw [parent_copied_root_high_of_le context hCopy hRow]
  cases hParent : parent row array.raw context.parentColumn with
  | none =>
      simp only [hParent] at hOld
      rw [matrixEntry_copied context hCopy context.blockLength_pos row, hNotAscending]
      simpa using hOld
  | some p =>
      simp only [hParent] at hOld
      have hp : p < context.lastIndex := Nat.lt_trans (parent_some_lt hParent) hRoot
      change matrixEntry (array.expand index).raw (context.copyPosition copy 0) row =
        matrixEntry (array.expand index).raw p row + 1
      rw [matrixEntry_copied context hCopy context.blockLength_pos row, hNotAscending,
        matrixEntry_expand_prefix context index row hp]
      simpa using hOld

theorem regularAt_copied_root_low {array : ValidArray} (hRegular : DepthRegular array.raw)
    (context : ExpansionContext array) {index copy row : Nat}
    (hCopy : copy + 1 ≤ index) (hRow : row < context.maximalRow) :
    RegularAt (array.expand index).raw row (context.copyPosition (copy + 1) 0) := by
  have hRootAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  have hOld := hRegular row context.lastIndex (by rw [context.array_length]; omega)
  have hNewAscending : ascending array.raw context.maximalRow context.parentColumn 0 row = true := by
    simp [ascending, hRow]
  unfold RegularAt
  rw [parent_copied_root_low_of_le context hCopy (by omega) hRow]
  simp only [Nat.add_sub_cancel]
  cases hParent : parent row array.raw context.lastIndex with
  | none =>
      rw [isAncestor_eq_false_of_parent_none hParent] at hRootAncestor
      contradiction
  | some p =>
      simp only [hParent] at hOld
      simp only [Option.map_some]
      have hpLower := ancestor_le_parent hParent hRootAncestor
      have hpUpper := parent_some_lt hParent
      have hpLocal : p - context.parentColumn < context.blockLength := by
        simp only [ExpansionContext.blockLength]
        omega
      have hSourceEq : context.parentColumn + (p - context.parentColumn) = p := by omega
      have hLastEq : context.parentColumn + context.blockLength = context.lastIndex := by
        have := context.parentColumn_lt_lastIndex
        simp only [ExpansionContext.blockLength]
        omega
      have hTargetAscending : ascending array.raw context.maximalRow context.parentColumn
          context.blockLength row = true := by
        simp [ascending, hRow, hLastEq, hRootAncestor]
      have hParentAscending : ascending array.raw context.maximalRow context.parentColumn
          (p - context.parentColumn) row = true := by
        apply ExpansionContext.ascending_of_ancestor_of_ascending _ _ _ _ hTargetAscending
        rw [hSourceEq, hLastEq]
        exact direct_parent_isAncestor hParent
      rw [copyColumn_bad context copy hpLower,
        matrixEntry_copied context (by omega) hpLocal row,
        matrixEntry_copied context hCopy context.blockLength_pos row,
        hParentAscending, hNewAscending]
      simp only [↓reduceIte, Nat.add_zero, hSourceEq, Nat.add_mul, Nat.one_mul]
      have hDelta := rowIncrement_pos context hRow
      unfold rowIncrement at hDelta ⊢
      omega

/-- 深度正规性单独在展开下封闭，不需要阻挡条件。 -/
theorem depthRegular_expand {array : ValidArray} (hRegular : DepthRegular array.raw) (index : Nat) :
    DepthRegular (array.expand index).raw := by
  cases hMaximal : maximalParentRow array.raw with
  | none =>
      have hEqual : (array.expand index).raw =
          trimZeroRows (array.raw.take (array.raw.length - 1)) := by
        rw [ValidArray.raw_expand]
        unfold YesMetaZFC.BMS.expand expandRaw
        cases hSize : array.raw.length with
        | zero =>
            have hNil : array.raw = [] := List.length_eq_zero_iff.mp hSize
            simp [hNil, trimZeroRows]
        | succ lastIndex => simp [hMaximal]
      rw [hEqual]
      exact depthRegular_trimZeroRows (depthRegular_take hRegular _)
  | some maximalRow =>
      let context := Classical.choice (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
      intro row column hColumn
      by_cases hPrefix : column < context.lastIndex
      · rw [parent_expand_prefix context index row hPrefix]
        have hOld := hRegular row column (by rw [context.array_length]; omega)
        cases hParent : parent row array.raw column with
        | none => simpa only [hParent, matrixEntry_expand_prefix context index row hPrefix] using hOld
        | some p =>
            have hp := Nat.lt_trans (parent_some_lt hParent) hPrefix
            simpa only [hParent, matrixEntry_expand_prefix context index row hPrefix,
              matrixEntry_expand_prefix context index row hp] using hOld
      · have hNotGood : context.parentColumn ≤ column := by
          have := context.parentColumn_lt_lastIndex
          omega
        rcases context.exists_copyPosition_of_not_good hColumn hNotGood with
          ⟨copy, localColumn, hCopy, hLocal, rfl⟩
        by_cases hZero : localColumn = 0
        · subst localColumn
          by_cases hLow : row < context.maximalRow
          · cases copy with
            | zero =>
                simp only [ExpansionContext.copyPosition_zero, Nat.add_zero] at hPrefix
                exact False.elim (hPrefix context.parentColumn_lt_lastIndex)
            | succ copy => exact regularAt_copied_root_low hRegular context hCopy hLow
          · exact regularAt_copied_root_high hRegular context hCopy (by omega)
        · exact regularAt_copied_nonroot hRegular context hCopy (by omega) hLocal row

end ZeroY.BMS
