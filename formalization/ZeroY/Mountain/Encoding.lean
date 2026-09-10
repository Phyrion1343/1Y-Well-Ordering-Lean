import ZeroY.Mountain.Termination
import ZeroY.MatrixOrder
import ZeroY.Encode

/-!
# 山脉行与编码坐标

将有限行列表转置为列矩阵，并把补零后的每个编码坐标对应到无截断的
`layerAfter` 迭代。这一步不使用父图深度不变或往返定理。
-/

namespace ZeroY

def matrixOfRows (width : Nat) (rows : List (List Nat)) : Matrix :=
  (List.range width).map fun column => rows.map fun row => row[column]?.getD 0

theorem encodeRaw_eq_matrixOfRows (s : Sequence) :
    encodeRaw s = matrixOfRows s.length
      (mountainRows (maxValue s) ⟨s, linearParent⟩) := rfl

theorem matrixOfRows_length (width : Nat) (rows : List (List Nat)) :
    (matrixOfRows width rows).length = width := by
  simp [matrixOfRows]

theorem matrixEntry_matrixOfRows {width column : Nat} (rows : List (List Nat))
    (hColumn : column < width) (row : Nat) :
    matrixEntry (matrixOfRows width rows) column row =
      ((rows[row]?.getD [])[column]?.getD 0) := by
  simp only [matrixEntry, columnEntry, matrixOfRows, List.getElem?_map,
    List.getElem?_range hColumn, Option.map_some, Option.getD_some]
  cases rows[row]? <;> simp

theorem layerAfter_length (steps : Nat) (layer : Layer) :
    (layerAfter steps layer).values.length = layer.values.length := by
  induction steps generalizing layer with
  | zero => rfl
  | succ steps ih => simpa [layerAfter] using ih (nextLayer layer)

theorem layerAfter_positive (steps : Nat) {layer : Layer} (hPositive : layer.Positive) :
    (layerAfter steps layer).Positive := by
  induction steps generalizing layer with
  | zero => exact hPositive
  | succ steps ih => exact ih (nextLayer_positive layer)

theorem layerParent_none_of_all_ones {layer : Layer}
    (hOnes : layer.values.all (fun value => value == 1) = true) (column : Nat) :
    layerParent layer column = none := by
  have hAll : ∀ value ∈ layer.values, value = 1 := by
    simpa only [List.all_eq_true, beq_iff_eq] using hOnes
  cases hParent : layerParent layer column with
  | none => rfl
  | some p =>
      have hColumn := layerParent_some_column_valid hParent
      have hP := Nat.lt_trans (layerParent_some_lt hParent) hColumn
      have hLess := layerParent_some_value_lt hParent
      simp only [List.getElem?_eq_getElem hColumn, List.getElem?_eq_getElem hP,
        Option.getD_some] at hLess
      rw [hAll _ (List.getElem_mem hColumn), hAll _ (List.getElem_mem hP)] at hLess
      omega

theorem parentDepth_eq_zero_of_none {parent : ParentMap} {column : Nat}
    (hParent : parent column = none) : parentDepth parent column = 0 := by
  cases column <;> simp [parentDepth, YesMetaZFC.BMS.ancestorChain, hParent]

theorem depthRow_getD {layer : Layer} {column : Nat}
    (hColumn : column < layer.values.length) :
    (depthRow layer)[column]?.getD 0 = parentDepth (layerParent layer) column := by
  simp [depthRow, List.getElem?_range hColumn]

/-- 终止层以上的补零坐标也等于实际父链深度。 -/
theorem mountainRows_getD_depth {layer : Layer} (hPositive : layer.Positive)
    {fuel : Nat} (hFuel : maxValue layer.values ≤ fuel)
    {column : Nat} (hColumn : column < layer.values.length) (row : Nat) :
    (((mountainRows fuel layer)[row]?.getD [])[column]?.getD 0) =
      parentDepth (layerParent (layerAfter row layer)) column := by
  induction fuel generalizing layer row with
  | zero =>
      have hDone := all_ones_of_maxValue_le_one hPositive (by omega)
      have hAfter := layerAfter_all_ones_of_all_ones hDone row
      rw [parentDepth_eq_zero_of_none (layerParent_none_of_all_ones hAfter column)]
      simp [mountainRows]
  | succ fuel ih =>
      by_cases hDone : layer.values.all (fun value => value == 1) = true
      · have hAfter := layerAfter_all_ones_of_all_ones hDone row
        rw [parentDepth_eq_zero_of_none (layerParent_none_of_all_ones hAfter column)]
        simp [mountainRows, hDone]
      · have hNext : maxValue (nextLayer layer).values ≤ fuel := by
          have := nextLayer_maxValue_lt hPositive hDone
          omega
        cases row with
        | zero =>
            simpa [mountainRows, hDone, layerAfter] using depthRow_getD hColumn
        | succ row =>
            simpa [mountainRows, hDone, layerAfter] using
              ih (nextLayer_positive layer) hNext (by simpa using hColumn) row

theorem encodeRaw_entry_depth {s : Sequence} (hLegal : Legal s)
    {column : Nat} (hColumn : column < s.length) (row : Nat) :
    matrixEntry (encodeRaw s) column row =
      parentDepth (layerParent (layerAfter row ⟨s, linearParent⟩)) column := by
  rw [encodeRaw_eq_matrixOfRows, matrixEntry_matrixOfRows _ hColumn]
  exact mountainRows_getD_depth (layer := ⟨s, linearParent⟩) hLegal.1
    (Nat.le_refl _) hColumn row

end ZeroY
