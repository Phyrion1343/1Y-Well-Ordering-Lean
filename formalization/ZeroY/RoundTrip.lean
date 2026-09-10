import ZeroY.Mountain.Roots
import ZeroY.Mountain.Encoding
import ZeroY.Forest.Stack
import ZeroY.BMS.PaddedDescent

/-!
# 对全部合法式的解码编码往返

将编码矩阵每一行的 BM4 父图识别为实际山脉父图，然后从矩阵的支撑高度
反向逐行求和。整个论证不使用标准生成性。
-/

namespace ZeroY

open YesMetaZFC.BMS

private theorem greatestBelow_congr {bound : Nat} {p q : Nat → Bool}
    (h : ∀ candidate, candidate < bound → p candidate = q candidate) :
    greatestBelow? bound p = greatestBelow? bound q := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      simp only [greatestBelow?, h bound (by omega)]
      split
      · rfl
      · exact ih (fun candidate hc => h candidate (by omega))

private theorem linearParent_ancestor_of_lt {target found : Nat} (h : found < target) :
    Forest.Ancestor linearParent target found := by
  induction target with
  | zero => omega
  | succ target ih =>
      by_cases heq : found = target
      · subst found
        exact Relation.TransGen.single rfl
      · exact Relation.TransGen.trans (Relation.TransGen.single rfl) (ih (by omega))

private theorem linearParent_contains {target found : Nat} (h : found < target) :
    (ancestorChain linearParent target target).contains found = true :=
  (Forest.ancestorChain_contains_iff (fun h => linearParent_leftward h)).mpr
    (linearParent_ancestor_of_lt h)

theorem entry_matrixOfRows {width column : Nat} (rows : List (List Nat))
    (hColumn : column < width) (row : Nat) :
    entry? (matrixOfRows width rows) column row =
      rows[row]?.map (fun values => values[column]?.getD 0) := by
  simp [entry?, matrixOfRows, List.getElem?_range hColumn]

private theorem matrixOfRows_comparison {width candidate target : Nat}
    (rows : List (List Nat)) (hCandidate : candidate < width) (hTarget : target < width)
    (row : Nat) :
    (match entry? (matrixOfRows width rows) candidate row,
      entry? (matrixOfRows width rows) target row with
      | some left, some right => decide (left < right)
      | _, _ => false) =
      decide (matrixEntry (matrixOfRows width rows) candidate row <
        matrixEntry (matrixOfRows width rows) target row) := by
  rw [entry_matrixOfRows rows hCandidate row, entry_matrixOfRows rows hTarget row,
    matrixEntry_matrixOfRows rows hCandidate row, matrixEntry_matrixOfRows rows hTarget row]
  cases rows[row]? <;> simp

private theorem matrixEntry_outside {array : Matrix} {column : Nat}
    (hColumn : array.length ≤ column) (row : Nat) : matrixEntry array column row = 0 := by
  simp [matrixEntry, List.getElem?_eq_none hColumn, columnEntry]

private theorem nearestSmaller_value_zero (previous : ParentMap) (value : Nat → Nat)
    (column : Nat) (hZero : value column = 0) :
    Forest.nearestSmaller previous value column = none := by
  apply greatestBelow?_eq_none_iff.mpr
  intro candidate _
  simp [hZero]

/-- 转置矩阵的首行搜索等于线性森林上的补零数值搜索。 -/
theorem parent_matrixOfRows_zero (width : Nat) (rows : List (List Nat)) :
    parent 0 (matrixOfRows width rows) =
      Forest.nearestSmaller linearParent (fun column =>
        matrixEntry (matrixOfRows width rows) column 0) := by
  funext target
  by_cases hTarget : target < width
  · simp only [parent, matrixOfRows_length, hTarget, ↓reduceIte, Forest.nearestSmaller]
    apply greatestBelow_congr
    intro candidate hCandidate
    rw [linearParent_contains hCandidate, Bool.true_and]
    exact matrixOfRows_comparison rows (by omega) hTarget 0
  · rw [nearestSmaller_value_zero _ _ target
      (matrixEntry_outside (by simpa [matrixOfRows_length] using Nat.le_of_not_gt hTarget) 0)]
    simp [parent, matrixOfRows_length, hTarget]

/-- 转置矩阵的高行搜索等于前行父森林上的补零数值搜索。 -/
theorem parent_matrixOfRows_succ (width : Nat) (rows : List (List Nat)) (row : Nat) :
    parent (row + 1) (matrixOfRows width rows) =
      Forest.nearestSmaller (parent row (matrixOfRows width rows)) (fun column =>
        matrixEntry (matrixOfRows width rows) column (row + 1)) := by
  funext target
  by_cases hTarget : target < width
  · simp only [parent, matrixOfRows_length, hTarget, ↓reduceIte, Forest.nearestSmaller]
    apply greatestBelow_congr
    intro candidate hCandidate
    congr 1
    exact matrixOfRows_comparison (candidate := candidate) rows (by omega) hTarget (row + 1)
  · rw [nearestSmaller_value_zero _ _ target
      (matrixEntry_outside (by simpa [matrixOfRows_length] using Nat.le_of_not_gt hTarget) (row + 1))]
    simp [parent, matrixOfRows_length, hTarget]

/-- 编码的整行补零标签，连同范围外列，都等于实际山脉父链深度。 -/
theorem encodeRaw_row_eq_depth {s : Sequence} (hLegal : Legal s) (row : Nat) :
    (fun column => matrixEntry (encodeRaw s) column row) =
      parentDepth (layerParent (layerAfter row ⟨s, linearParent⟩)) := by
  funext column
  by_cases hColumn : column < s.length
  · exact encodeRaw_entry_depth hLegal hColumn row
  · rw [matrixEntry_outside (by simpa [encodeRaw_length] using Nat.le_of_not_gt hColumn) row]
    symm
    apply parentDepth_eq_zero_of_none
    simp [layerParent, layerAfter_length, hColumn]

private theorem layerAfter_succ_previous (row : Nat) (layer : Layer) :
    (layerAfter (row + 1) layer).previous = layerParent (layerAfter row layer) := by
  induction row generalizing layer with
  | zero => rfl
  | succ row ih => exact ih (nextLayer layer)

/-- BM4 对编码矩阵重新计算的父图，逐行精确等于原始山脉父图。 -/
theorem parent_encodeRaw {s : Sequence} (hLegal : Legal s) (row : Nat) :
    parent row (encodeRaw s) = layerParent (layerAfter row ⟨s, linearParent⟩) := by
  have hDepth (row : Nat) :
      Forest.nearestSmaller (layerAfter row ⟨s, linearParent⟩).previous
        (parentDepth (layerParent (layerAfter row ⟨s, linearParent⟩))) =
          layerParent (layerAfter row ⟨s, linearParent⟩) := by
    rw [Forest.layerParent_eq_nearestSmaller]
    exact Forest.nearestSmaller_depth_invariant
      (legal_layerAfter_rootInvariant hLegal row).leftward _
  induction row with
  | zero =>
      rw [encodeRaw_eq_matrixOfRows, parent_matrixOfRows_zero]
      change Forest.nearestSmaller linearParent
        (fun column => matrixEntry (encodeRaw s) column 0) = _
      rw [encodeRaw_row_eq_depth hLegal 0]
      exact hDepth 0
  | succ row ih =>
      rw [encodeRaw_eq_matrixOfRows, parent_matrixOfRows_succ]
      change Forest.nearestSmaller (parent row (encodeRaw s))
        (fun column => matrixEntry (encodeRaw s) column (row + 1)) = _
      rw [ih, encodeRaw_row_eq_depth hLegal (row + 1), ← layerAfter_succ_previous]
      exact hDepth (row + 1)

/-- 支撑高度及其上方的补零坐标全部为零。 -/
theorem matrixEntry_zero_of_trimHeight_le (array : Matrix) {row : Nat}
    (hRow : trimHeight array ≤ row) (column : Nat) : matrixEntry array column row = 0 := by
  rw [matrixEntry_eq_entry_getD]
  cases hEntry : entry? array column row with
  | none => rfl
  | some value =>
      have hZero : value = 0 := by
        apply Classical.byContradiction
        intro hNonzero
        have := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry hNonzero
        omega
      simp [hZero]

/-- 编码矩阵的支撑高度处，实际山脉已经到达全 1 行。 -/
theorem layerAfter_encodeRaw_trimHeight {s : Sequence} (hLegal : Legal s) :
    (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩).values =
      List.replicate s.length 1 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨layerAfter_length _ _, ?_⟩
  intro value hValue
  obtain ⟨column, hColumn, hValueEq⟩ := List.getElem_of_mem hValue
  have hOriginal : column < s.length := by simpa [layerAfter_length] using hColumn
  have hDepth : parentDepth
      (layerParent (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩)) column = 0 := by
    rw [← encodeRaw_entry_depth hLegal hOriginal]
    exact matrixEntry_zero_of_trimHeight_le _ (Nat.le_refl _) _
  have hParent : layerParent
      (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩) column = none := by
    cases hp : layerParent
        (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩) column with
    | none => rfl
    | some found =>
        have hSucc := Forest.parentDepth_some
          (parent := layerParent (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩))
          (fun h => layerParent_some_lt h) hp
        omega
  have hOne := (legal_layerAfter_parent_none_iff hLegal _ hColumn).mp hParent
  simpa only [List.getElem?_eq_getElem hColumn, Option.getD_some, hValueEq] using hOne

/-- 全称 F(D(s)) = s；包含空式和任意非标准合法式。 -/
theorem decodeRaw_encodeRaw {s : Sequence} (hLegal : Legal s) :
    decodeRaw (encodeRaw s) = s := by
  unfold decodeRaw
  simp only [parent_encodeRaw hLegal, encodeRaw_length]
  rw [← layerAfter_encodeRaw_trimHeight hLegal]
  exact sumRow_layerAfter_foldr (legal_initial_rootInvariant hLegal) _

private theorem parent_none_of_trimHeight_le (array : Matrix) {row : Nat}
    (hRow : trimHeight array ≤ row) (column : Nat) : parent row array column = none := by
  cases hp : parent row array column with
  | none => rfl
  | some found =>
      obtain ⟨left, right, _, hRight, hLess⟩ := parent_some_entry_lt hp
      have hNonzero : right ≠ 0 := by omega
      have := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hRight hNonzero
      omega

/-- 删除公共尾零行不改变任何行的父图。 -/
theorem parent_trimZeroRows_all (array : Matrix) (row : Nat) :
    parent row (trimZeroRows array) = parent row array := by
  funext column
  by_cases hRow : row < trimHeight array
  · exact parent_trimZeroRows_of_lt array hRow column
  · rw [parent_trimZeroRows_eq_none_of_le array (by omega) column,
      parent_none_of_trimHeight_le array (by omega) column]

/-- 解码与公共尾零行归一化相容。 -/
theorem decodeRaw_trimZeroRows (array : Matrix) :
    decodeRaw (trimZeroRows array) = decodeRaw array := by
  simp only [decodeRaw, trimHeight_trimZeroRows, length_trimZeroRows, parent_trimZeroRows_all]

/-- 与规范矩阵载体相接的实际表达式往返定理。 -/
theorem decode_encode (s : Expr) : decode (encode s) = s := by
  apply Expr.ext
  change decodeRaw (trimZeroRows (encodeRaw s.values)) = s.values
  rw [decodeRaw_trimZeroRows]
  exact decodeRaw_encodeRaw s.legal

/-- 因为有实际左逆，规范矩阵编码在全部合法表达式上单射。 -/
theorem encode_injective : Function.Injective encode := by
  intro left right hEqual
  have hDecoded := congrArg decode hEqual
  simpa only [decode_encode] using hDecoded

end ZeroY
