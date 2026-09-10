import ZeroY.Forest.Comparison
import ZeroY.Mountain.Roots
import ZeroY.BMS.PaddedDescent

/-!
# 一般矩形矩阵的父图桥

缺失的行在所有列同时缺失，因此补零比较与原 Option 条目比较一致。
本文件不要求矩阵来自编码，也不要求标准生成性。
-/

namespace ZeroY

open YesMetaZFC.BMS

private theorem matrix_comparison_of_rectangular {array : Matrix}
    (hRect : rectangular array = true) {candidate target : Nat}
    (hC : candidate < array.length) (hT : target < array.length) (row : Nat) :
    (match entry? array candidate row, entry? array target row with
      | some left, some right => decide (left < right)
      | _, _ => false) = decide (matrixEntry array candidate row < matrixEntry array target row) := by
  obtain ⟨height, hUniform⟩ := rectangular_iff_exists_uniformHeight.mp hRect
  rw [matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD]
  cases hCE : entry? array candidate row with
  | none =>
      cases hTE : entry? array target row with
      | none => rfl
      | some value =>
          have hRow := row_lt_uniformHeight_of_entry?_eq_some hUniform hTE
          obtain ⟨other, ho⟩ := exists_entry_of_uniformHeight hUniform hC hRow
          rw [hCE] at ho
          contradiction
  | some value =>
      cases hTE : entry? array target row with
      | none =>
          have hRow := row_lt_uniformHeight_of_entry?_eq_some hUniform hCE
          obtain ⟨other, ho⟩ := exists_entry_of_uniformHeight hUniform hT hRow
          rw [hTE] at ho
          contradiction
      | some other => rfl

theorem linearParent_ancestor_of_lt {target found : Nat} (h : found < target) :
    Forest.Ancestor linearParent target found := by
  induction target with
  | zero => omega
  | succ target ih =>
      by_cases heq : found = target
      · subst found; exact Relation.TransGen.single rfl
      · exact Relation.TransGen.trans (Relation.TransGen.single rfl) (ih (by omega))

/-- 任意矩形矩阵的实际 BM4 父图等于补零标签上的森林搜索，包括范围外列。 -/
theorem parent_eq_nearestSmaller {array : Matrix} (hRect : rectangular array = true) (row : Nat) :
    parent row array = Forest.nearestSmaller (previousParent array row)
      (fun column => matrixEntry array column row) := by
  funext target
  by_cases hTarget : target < array.length
  · rw [parent_eq_greatestBelow?, if_pos hTarget]
    unfold Forest.nearestSmaller
    apply Forest.greatestBelow?_congr
    intro candidate hCandidate
    have hC : candidate < array.length := by omega
    cases row with
    | zero =>
        have hContains : (ancestorChain linearParent target target).contains candidate = true :=
          (Forest.ancestorChain_contains_iff (fun h => linearParent_leftward h)).mpr
            (linearParent_ancestor_of_lt hCandidate)
        change (match entry? array candidate 0, entry? array target 0 with
          | some left, some right => decide (left < right)
          | _, _ => false) = ((ancestorChain linearParent target target).contains candidate && _)
        rw [hContains, Bool.true_and]
        exact matrix_comparison_of_rectangular hRect hC hTarget 0
    | succ row =>
        simp only [parentEligible, isAncestor]
        congr 1
        exact matrix_comparison_of_rectangular hRect hC hTarget (row + 1)
  · rw [parent_eq_greatestBelow?, if_neg hTarget]
    symm
    apply greatestBelow?_eq_none_iff.mpr
    intro candidate _
    have hZero : matrixEntry array target row = 0 := by
      simp [matrixEntry, columnEntry, List.getElem?_eq_none (show array.length ≤ target by omega)]
    simp [hZero]

/-- 条件 I 的递推式等价于各条目的实际父链深度。 -/
theorem depthRegular_eq_parentDepth {array : Matrix} (hI : DepthRegular array)
    (row column : Nat) (hColumn : column < array.length) :
    matrixEntry array column row = parentDepth (parent row array) column := by
  induction column using Nat.strongRecOn with
  | ind column ih =>
      have hEq := hI row column hColumn
      cases hp : parent row array column with
      | none =>
          simp only [hp] at hEq
          rw [Forest.parentDepth_none hp]
          exact hEq
      | some p =>
          have hpLt := parent_some_lt hp
          simp only [hp] at hEq
          rw [hEq, ih p hpLt (by omega)]
          exact (Forest.parentDepth_some (parent := parent row array)
            (fun h => parent_some_lt h) hp).symm

end ZeroY
