import ZeroY.Structural.ExpansionParents
import ZeroY.Expansion

/-!
# BM4 父项与独立 0-Y 展开的复制规则一致
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

theorem copiedMountainParent_at_copy {array : ValidArray} (context : ExpansionContext array)
    (parent : ParentMap) {copy localColumn : Nat} (hCopy : 0 < copy)
    (hLocal : localColumn < context.blockLength) :
    copiedMountainParent parent context.parentColumn context.lastIndex
      (context.copyPosition copy localColumn) =
    if localColumn = 0 then (parent context.lastIndex).map (copyColumn context (copy - 1))
    else (parent (context.parentColumn + localColumn)).map (copyColumn context copy) := by
  have hOffset : context.copyPosition copy localColumn - context.parentColumn =
      localColumn + copy * context.blockLength := by
    simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart]
    omega
  have hAfter : ¬ context.copyPosition copy localColumn < context.lastIndex := by
    have hOne := Nat.mul_le_mul_right context.blockLength hCopy
    have hBound := context.parentColumn_lt_lastIndex
    simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart,
      ExpansionContext.blockLength, Nat.one_mul] at *
    omega
  have hDiv : (context.copyPosition copy localColumn - context.parentColumn) /
      context.blockLength = copy := by
    rw [hOffset, Nat.add_mul_div_right _ _ context.blockLength_pos,
      Nat.div_eq_of_lt hLocal, Nat.zero_add]
  have hMod : (context.copyPosition copy localColumn - context.parentColumn) %
      context.blockLength = localColumn := by
    rw [hOffset, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hLocal]
  simp only [ExpansionContext.blockLength] at hDiv hMod
  simp only [copiedMountainParent, hAfter, ↓reduceIte, hDiv, hMod]
  by_cases hZero : localColumn = 0
  · subst localColumn
    simp only [Nat.add_zero, ↓reduceIte]
    rfl
  · have hNe : context.parentColumn + localColumn ≠ context.parentColumn := by omega
    simp only [hNe, hZero, ↓reduceIte]
    rfl

/-- 最大活动行以下，BM4 实际重算的父图就是 HTML 边界复制规则。 -/
theorem parent_expand_eq_copiedMountainParent {array : ValidArray}
    (context : ExpansionContext array) {index row column : Nat}
    (hRow : row < context.maximalRow) (hColumn : column < (array.expand index).raw.length) :
    parent row (array.expand index).raw column =
      copiedMountainParent (parent row array.raw) context.parentColumn context.lastIndex column := by
  by_cases hPrefix : column < context.lastIndex
  · rw [parent_expand_prefix context index row hPrefix]
    simp [copiedMountainParent, hPrefix]
  · have hNotGood : context.parentColumn ≤ column := by
      have := context.parentColumn_lt_lastIndex
      omega
    rcases context.exists_copyPosition_of_not_good hColumn hNotGood with
      ⟨copy, localColumn, hCopy, hLocal, rfl⟩
    have hCopyPositive : 0 < copy := by
      cases copy with
      | zero =>
          simp only [ExpansionContext.copyPosition_zero] at hPrefix
          simp only [ExpansionContext.blockLength] at hLocal
          omega
      | succ copy => omega
    rw [copiedMountainParent_at_copy context _ hCopyPositive hLocal]
    by_cases hZero : localColumn = 0
    · subst localColumn
      rw [if_pos rfl]
      exact parent_copied_root_low_of_le context hCopy hCopyPositive hRow
    · rw [if_neg hZero]
      exact parent_copied_nonroot_of_le context hCopy row (by omega) hLocal

end ZeroY.BMS
