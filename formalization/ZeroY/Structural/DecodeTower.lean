import ZeroY.Reversible
import ZeroY.Structural.Prefix
import ZeroY.Mountain.CommonChain

/-!
# 从矩阵父图反向求和的分层塔

本文件中的每层使用给定矩阵的父图；在结构识别之前，不预设这些父图已经
等于数值山脉重新计算的父图。
-/

namespace ZeroY

open YesMetaZFC.BMS

private def towerSumStep (parent : ParentMap) (acc : Sequence) (value : Nat) : Sequence :=
  acc ++ [match parent acc.length with
    | none => value
    | some column => value + acc[column]?.getD 0]

private theorem towerSumFold_getD (parent : ParentMap) (remaining acc : Sequence)
    (column : Nat) (hColumn : column < acc.length) :
    (remaining.foldl (towerSumStep parent) acc)[column]?.getD 0 = acc[column]?.getD 0 := by
  induction remaining generalizing acc with
  | nil => rfl
  | cons value remaining ih =>
      rw [List.foldl_cons, ih _ (by simp [towerSumStep]; omega)]
      simp [towerSumStep, List.getElem?_append_left hColumn]

/-- 求和输出在每个输入前缀上的坐标保持不变。 -/
theorem sumRow_getD_prefix (parent : ParentMap) (upper : Sequence) {count column : Nat}
    (hColumn : column < (upper.take count).length) :
    (sumRow parent upper)[column]?.getD 0 =
      (sumRow parent (upper.take count))[column]?.getD 0 := by
  conv => lhs; rw [← List.take_append_drop count upper]
  unfold sumRow
  rw [List.foldl_append]
  apply towerSumFold_getD parent (upper.drop count)
  change column < (sumRow parent (upper.take count)).length
  simpa only [sumRow_length] using hColumn

/-- 逐列求和程序确实满足其数学递推，而非只验证逆过程。 -/
theorem sumRow_getD {parent : ParentMap} (hLeft : Forest.Leftward parent)
    {upper : Sequence} {column : Nat} (hColumn : column < upper.length) :
    (sumRow parent upper)[column]?.getD 0 =
      match parent column with
      | none => upper[column]?.getD 0
      | some found => upper[column]?.getD 0 + (sumRow parent upper)[found]?.getD 0 := by
  have hPrefixLength : (sumRow parent (upper.take column)).length = column := by
    simp [sumRow_length, List.length_take, Nat.min_eq_left (by omega : column ≤ upper.length)]
  rw [sumRow_getD_prefix parent upper
    (count := column + 1) (by simp [List.length_take]; omega)]
  rw [List.take_succ_eq_append_getElem hColumn, sumRow_append_singleton, hPrefixLength]
  rw [List.getElem?_append_right (by omega :
    (sumRow parent (upper.take column)).length ≤ column)]
  rw [hPrefixLength, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  cases hParent : parent column with
  | none => simp [List.getElem?_eq_getElem hColumn]
  | some found =>
      simp only
      have hFound : found < column := hLeft hParent
      rw [← sumRow_getD_prefix parent upper (count := column)
        (by simp [List.length_take]; omega), List.getElem?_eq_getElem hColumn]
      rfl

/-- 从给定行起逐行向下求和；fuel 只控制高行起点，尚不假定父图规范。 -/
def decodeTower (array : Matrix) (row : Nat) : Nat → Sequence
  | 0 => List.replicate array.length 1
  | fuel + 1 => sumRow (parent row array) (decodeTower array (row + 1) fuel)

theorem decodeTower_length (array : Matrix) (row fuel : Nat) :
    (decodeTower array row fuel).length = array.length := by
  induction fuel generalizing row with
  | zero => simp [decodeTower]
  | succ fuel ih => simpa [decodeTower, sumRow_length] using ih (row + 1)

theorem decodeTower_positive (array : Matrix) (row fuel : Nat) :
    ∀ value ∈ decodeTower array row fuel, 0 < value := by
  induction fuel generalizing row with
  | zero => exact (replicate_one_legal array.length).1
  | succ fuel ih => exact sumRow_positive _ _ (ih (row + 1))

theorem decodeTower_getD_positive (array : Matrix) (row fuel : Nat)
    {column : Nat} (hColumn : column < array.length) :
    0 < (decodeTower array row fuel)[column]?.getD 0 := by
  exact positive_getD (layer := ⟨decodeTower array row fuel, linearParent⟩)
    (decodeTower_positive array row fuel) (by simpa [decodeTower_length] using hColumn)

/-- 高行父边必须沿低行祖先链，因此前一行无父项时本行也无父项。 -/
theorem parent_succ_none_of_none (array : Matrix) {row column : Nat}
    (hParent : parent row array column = none) : parent (row + 1) array column = none := by
  apply parent_eq_none_iff.mpr
  apply Or.inr
  intro candidate hCandidate
  simp only [parentEligible, isAncestor_eq_false_of_parent_none hParent, Bool.false_and]

/-- 给定矩阵当前行无父项的列，在当前行及所有高行解码值均为 1。 -/
theorem decodeTower_getD_of_parent_none (array : Matrix) (row fuel : Nat)
    {column : Nat} (hColumn : column < array.length)
    (hParent : parent row array column = none) :
    (decodeTower array row fuel)[column]?.getD 0 = 1 := by
  induction fuel generalizing row with
  | zero => simp [decodeTower, hColumn]
  | succ fuel ih =>
      rw [decodeTower, sumRow_getD (fun h => parent_some_lt h)
        (by simpa [decodeTower_length] using hColumn), hParent]
      exact ih (row + 1) (parent_succ_none_of_none array hParent)

/-- 给定父森林与求和行组成的层满足根不变量，无须假定结构条件 S。 -/
theorem decodeTower_rootInvariant (array : Matrix) (row fuel : Nat) :
    (Layer.mk (decodeTower array row fuel) (previousParent array row)).RootInvariant := by
  refine ⟨decodeTower_positive array row fuel,
    fun h => previousParent_some_lt h, ?_⟩
  intro column hColumn hNone
  have hValid : column < array.length := by simpa [decodeTower_length] using hColumn
  cases row with
  | zero =>
      cases column with
      | zero =>
          exact decodeTower_getD_of_parent_none array 0 fuel hValid (bms_parent_first 0 array)
      | succ column => simp [previousParent, linearParent] at hNone
  | succ row =>
      exact decodeTower_getD_of_parent_none array (row + 1) fuel hValid
        (parent_succ_none_of_none array hNone)

/-- 解码塔与原始 foldr 实现完全一致。 -/
theorem decodeTower_eq_foldr (array : Matrix) (row fuel : Nat) :
    decodeTower array row fuel = (List.range fuel).foldr
      (fun offset upper => sumRow (parent (row + offset) array) upper)
      (List.replicate array.length 1) := by
  induction fuel generalizing row with
  | zero => rfl
  | succ fuel ih =>
      simp only [decodeTower, ih, List.range_succ_eq_map, List.foldr_cons, List.foldr_map,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

theorem decodeTower_eq_decodeRaw (array : Matrix) :
    decodeTower array 0 (trimHeight array) = decodeRaw array := by
  simp [decodeTower_eq_foldr, decodeRaw]

/-- 一旦当前搜索恢复给定父图，实际差分恰好回到解码塔的上一行。 -/
theorem nextLayer_decodeTower (array : Matrix) (row fuel : Nat)
    (hParent : layerParent ⟨decodeTower array row (fuel + 1), previousParent array row⟩ =
      parent row array) :
    nextLayer ⟨decodeTower array row (fuel + 1), previousParent array row⟩ =
      ⟨decodeTower array (row + 1) fuel, previousParent array (row + 1)⟩ := by
  have hValues : (nextLayer
      ⟨decodeTower array row (fuel + 1), previousParent array row⟩).values =
        decodeTower array (row + 1) fuel := by
    apply List.ext_getElem (by simp [nextLayer_length, decodeTower_length])
    intro column hLeft hRight
    have hValid : column < array.length := by simpa [decodeTower_length] using hRight
    have hColumn : column < (decodeTower array row (fuel + 1)).length := by
      simpa [decodeTower_length] using hValid
    have hNext := nextLayer_getD
      (layer := ⟨decodeTower array row (fuel + 1), previousParent array row⟩) hColumn
    rw [hParent] at hNext
    have hResult : (nextLayer
        ⟨decodeTower array row (fuel + 1), previousParent array row⟩).values[column]?.getD 0 =
          (decodeTower array (row + 1) fuel)[column]?.getD 0 := by
      rw [hNext]
      cases hp : parent row array column with
      | none =>
          exact (decodeTower_getD_of_parent_none array (row + 1) fuel hValid
            (parent_succ_none_of_none array hp)).symm
      | some found =>
          simp only [decodeTower]
          rw [sumRow_getD (parent := parent row array) (fun h => parent_some_lt h)
            (by simpa [decodeTower_length] using hValid), hp]
          simp only
          omega
    simpa only [List.getElem?_eq_getElem hLeft, List.getElem?_eq_getElem hRight,
      Option.getD_some] using hResult
  change Layer.mk _ (layerParent _) = Layer.mk _ (parent row array)
  rw [hParent]
  simp only [nextLayer, hParent] at hValues
  exact congrArg (fun values => Layer.mk values (parent row array)) hValues

end ZeroY
