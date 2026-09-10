import ZeroY.OrderEmbedding

/-!
# 同一候选链上不同列的完整比较

同一座合法山脉中，若两列共用候选祖先链，它们当前数值的顺序恰好对应
后续深度列的补零字典序。该结论不要求两列位置相邻或表达式为标准式。
-/

namespace ZeroY

open Forest

theorem Forest.ancestor_iff_of_parent_eq {parent : ParentMap} {left right : Nat}
    (hParent : parent left = parent right) (candidate : Nat) :
    Ancestor parent left candidate ↔ Ancestor parent right candidate := by
  constructor <;> intro h
  · rcases YesMetaZFC.BMS.transGen_head h with hd | ⟨next, hn, hr⟩
    · exact Relation.TransGen.single (hParent.symm.trans hd)
    · exact Relation.TransGen.trans (Relation.TransGen.single (hParent.symm.trans hn)) hr
  · rcases YesMetaZFC.BMS.transGen_head h with hd | ⟨next, hn, hr⟩
    · exact Relation.TransGen.single (hParent.trans hd)
    · exact Relation.TransGen.trans (Relation.TransGen.single (hParent.trans hn)) hr

/-- 山脉在一列上的完整有限深度列；共同尾零按 ColumnEq 识别。 -/
def mountainColumn (layer : Layer) (column : Nat) : List Nat :=
  (mountainRows (maxValue layer.values) layer).map fun row => row[column]?.getD 0

theorem mountainColumn_entry_depth {layer : Layer} (hPositive : layer.Positive)
    {column : Nat} (hColumn : column < layer.values.length) (row : Nat) :
    columnEntry (mountainColumn layer column) row =
      parentDepth (layerParent (layerAfter row layer)) column := by
  have hEntry := mountainRows_getD_depth hPositive (Nat.le_refl _) hColumn row
  rw [← hEntry]
  unfold columnEntry mountainColumn
  rw [List.getElem?_map]
  cases (mountainRows (maxValue layer.values) layer)[row]? <;> rfl

theorem layer_common_chain_depth_compare {layer : Layer} (hLeft : Leftward layer.previous)
    {left right : Nat}
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate)
    (hValue : layer.values[left]?.getD 0 ≤ layer.values[right]?.getD 0) :
    parentDepth (layerParent layer) left ≤ parentDepth (layerParent layer) right ∧
      (parentDepth (layerParent layer) left = parentDepth (layerParent layer) right →
        layerParent layer left = layerParent layer right) := by
  rw [layerParent_eq_nearestSmaller layer]
  exact nearestSmaller_common_chain_depth_compare hLeft hChain hValue

/-- 共链且数值相等时，两列全部后续深度相等。 -/
theorem layer_common_chain_depth_eq {layer : Layer} (hInv : layer.RootInvariant)
    {left right : Nat} (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate)
    (hValue : layer.values[left]?.getD 0 = layer.values[right]?.getD 0) (row : Nat) :
    parentDepth (layerParent (layerAfter row layer)) left =
      parentDepth (layerParent (layerAfter row layer)) right := by
  induction row generalizing layer with
  | zero =>
      have hLR := (layer_common_chain_depth_compare hInv.leftward hChain (Nat.le_of_eq hValue)).1
      have hRL := (layer_common_chain_depth_compare hInv.leftward
        (fun c => (hChain c).symm) (Nat.le_of_eq hValue.symm)).1
      exact Nat.le_antisymm hLR hRL
  | succ row ih =>
      obtain ⟨hLR, hParentOfEq⟩ := layer_common_chain_depth_compare hInv.leftward hChain
        (Nat.le_of_eq hValue)
      have hRL := (layer_common_chain_depth_compare hInv.leftward
        (fun c => (hChain c).symm) (Nat.le_of_eq hValue.symm)).1
      have hParent := hParentOfEq (Nat.le_antisymm hLR hRL)
      apply ih (nextLayer_rootInvariant layer) (by simpa using hL) (by simpa using hR)
      · exact ancestor_iff_of_parent_eq hParent
      · rw [nextLayer_getD hL, nextLayer_getD hR, hParent, hValue]

/-- 共链严格比较在有限行内首次产生同方向深度差。 -/
theorem layer_common_chain_first_difference {layer : Layer} (hInv : layer.RootInvariant)
    {left right : Nat} (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate)
    (hValue : layer.values[left]?.getD 0 < layer.values[right]?.getD 0) :
    ∃ row,
      (∀ earlier, earlier < row →
        parentDepth (layerParent (layerAfter earlier layer)) left =
          parentDepth (layerParent (layerAfter earlier layer)) right) ∧
      parentDepth (layerParent (layerAfter row layer)) left <
        parentDepth (layerParent (layerAfter row layer)) right := by
  generalize hSize : layer.values[left]?.getD 0 = size
  induction size using Nat.strongRecOn generalizing layer with
  | ind size ih =>
      obtain ⟨hDepthLe, hParentOfEq⟩ := layer_common_chain_depth_compare hInv.leftward hChain
        (Nat.le_of_lt hValue)
      rcases Nat.eq_or_lt_of_le hDepthLe with hEq | hLt
      · have hParentEq := hParentOfEq hEq
        cases hp : layerParent layer left with
        | none =>
            have hLOne := (layerParent_none_iff_value_one hInv hL).mp hp
            have hROne := (layerParent_none_iff_value_one hInv hR).mp (hParentEq.symm.trans hp)
            omega
        | some p =>
            have hpR := hParentEq.symm.trans hp
            have hpLt := layerParent_some_lt hp
            have hpPositive := positive_getD hInv.positive (show p < layer.values.length by omega)
            have hpSmaller := layerParent_some_value_lt hp
            have hNextLeft := nextLayer_getD hL
            have hNextRight := nextLayer_getD hR
            simp only [hp] at hNextLeft
            simp only [hpR] at hNextRight
            have hNextSize : (nextLayer layer).values[left]?.getD 0 < size := by
              rw [hNextLeft, ← hSize]
              exact Nat.sub_lt_of_pos_le hpPositive (Nat.le_of_lt hpSmaller)
            have hNextValue : (nextLayer layer).values[left]?.getD 0 <
                (nextLayer layer).values[right]?.getD 0 := by
              rw [hNextLeft, hNextRight]
              exact Nat.sub_lt_sub_right (Nat.le_of_lt hpSmaller) hValue
            obtain ⟨row, hEarlier, hLess⟩ := ih _ hNextSize (nextLayer_rootInvariant layer)
              (by simpa using hL) (by simpa using hR)
              (ancestor_iff_of_parent_eq hParentEq) hNextValue rfl
            refine ⟨row + 1, ?_, hLess⟩
            intro earlier he
            cases earlier with
            | zero => exact hEq
            | succ earlier => exact hEarlier earlier (by omega)
      · exact ⟨0, by intro earlier h; omega, hLt⟩

theorem mountainColumn_eq_of_common_chain_value_eq {layer : Layer}
    (hInv : layer.RootInvariant) {left right : Nat}
    (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate)
    (hValue : layer.values[left]?.getD 0 = layer.values[right]?.getD 0) :
    ColumnEq (mountainColumn layer left) (mountainColumn layer right) := by
  intro row
  rw [mountainColumn_entry_depth hInv.positive hL, mountainColumn_entry_depth hInv.positive hR]
  exact layer_common_chain_depth_eq hInv hL hR hChain hValue row

theorem mountainColumn_lt_of_common_chain_value_lt {layer : Layer}
    (hInv : layer.RootInvariant) {left right : Nat}
    (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate)
    (hValue : layer.values[left]?.getD 0 < layer.values[right]?.getD 0) :
    ColumnLt (mountainColumn layer left) (mountainColumn layer right) := by
  obtain ⟨row, hEarlier, hLess⟩ := layer_common_chain_first_difference hInv hL hR hChain hValue
  refine ⟨row, ?_, ?_⟩
  · intro earlier he
    rw [mountainColumn_entry_depth hInv.positive hL, mountainColumn_entry_depth hInv.positive hR]
    exact hEarlier earlier he
  · rw [mountainColumn_entry_depth hInv.positive hL, mountainColumn_entry_depth hInv.positive hR]
    exact hLess

/-- 共链两列的严格数值比较与完整深度列严格比较等价。 -/
theorem mountainColumn_lt_iff_of_common_chain {layer : Layer}
    (hInv : layer.RootInvariant) {left right : Nat}
    (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate) :
    ColumnLt (mountainColumn layer left) (mountainColumn layer right) ↔
      layer.values[left]?.getD 0 < layer.values[right]?.getD 0 := by
  constructor
  · intro h
    by_cases hv : layer.values[left]?.getD 0 < layer.values[right]?.getD 0
    · exact hv
    · by_cases heq : layer.values[left]?.getD 0 = layer.values[right]?.getD 0
      · have hc := mountainColumn_eq_of_common_chain_value_eq hInv hL hR hChain heq
        exact (ColumnLt.irrefl _ (ColumnLt.of_lt_of_eq h hc.symm)).elim
      · have hReverse := mountainColumn_lt_of_common_chain_value_lt hInv hR hL
          (fun c => (hChain c).symm) (by omega)
        exact (ColumnLt.irrefl _ (ColumnLt.trans h hReverse)).elim
  · exact mountainColumn_lt_of_common_chain_value_lt hInv hL hR hChain

/-- 共链两列的非严格比较亦等价。 -/
theorem mountainColumn_le_iff_of_common_chain {layer : Layer}
    (hInv : layer.RootInvariant) {left right : Nat}
    (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate) :
    ColumnLe (mountainColumn layer left) (mountainColumn layer right) ↔
      layer.values[left]?.getD 0 ≤ layer.values[right]?.getD 0 := by
  constructor
  · rintro (hEq | hLt)
    · by_cases hValue : layer.values[left]?.getD 0 ≤ layer.values[right]?.getD 0
      · exact hValue
      · have hReverse := mountainColumn_lt_of_common_chain_value_lt hInv hR hL
          (fun c => (hChain c).symm) (by omega)
        exact (ColumnLt.irrefl _ (ColumnLt.of_eq_of_lt hEq hReverse)).elim
    · exact Nat.le_of_lt ((mountainColumn_lt_iff_of_common_chain hInv hL hR hChain).mp hLt)
  · intro hValue
    rcases Nat.eq_or_lt_of_le hValue with heq | hlt
    · exact Or.inl (mountainColumn_eq_of_common_chain_value_eq hInv hL hR hChain heq)
    · exact Or.inr (mountainColumn_lt_of_common_chain_value_lt hInv hL hR hChain hlt)

theorem mountainColumn_eq_iff_of_common_chain {layer : Layer}
    (hInv : layer.RootInvariant) {left right : Nat}
    (hL : left < layer.values.length) (hR : right < layer.values.length)
    (hChain : ∀ candidate, Ancestor layer.previous left candidate ↔
      Ancestor layer.previous right candidate) :
    ColumnEq (mountainColumn layer left) (mountainColumn layer right) ↔
      layer.values[left]?.getD 0 = layer.values[right]?.getD 0 := by
  constructor
  · intro hEq
    have hLR := (mountainColumn_le_iff_of_common_chain hInv hL hR hChain).mp (Or.inl hEq)
    have hRL := (mountainColumn_le_iff_of_common_chain hInv hR hL
      (fun c => (hChain c).symm)).mp (Or.inl hEq.symm)
    exact Nat.le_antisymm hLR hRL
  · exact mountainColumn_eq_of_common_chain_value_eq hInv hL hR hChain

theorem layerAfter_add (first second : Nat) (layer : Layer) :
    layerAfter (first + second) layer = layerAfter second (layerAfter first layer) := by
  induction first generalizing layer with
  | zero => simp [layerAfter]
  | succ first ih => simpa only [Nat.succ_add, layerAfter] using ih (nextLayer layer)

theorem columnEntry_columnSuffix (array : Matrix) (column row index : Nat) :
    columnEntry (columnSuffix array column row) index = matrixEntry array column (row + index) := by
  simp [columnEntry, columnSuffix, matrixEntry]

/-- 编码列的任意后缀正是对应层开始的深度列，按共同尾零识别。 -/
theorem encode_suffix_eq_mountainColumn (s : Expr) {column : Nat}
    (hColumn : column < s.values.length) (row : Nat) :
    ColumnEq (columnSuffix (encode s).raw column row)
      (mountainColumn (layerAfter row ⟨s.values, linearParent⟩) column) := by
  intro index
  rw [columnEntry_columnSuffix, encode_entry_depth s hColumn]
  rw [mountainColumn_entry_depth (legal_layerAfter_rootInvariant s.legal row).positive
    (by simpa [layerAfter_length] using hColumn), layerAfter_add]

theorem ColumnLt.congr_iff {a b c d : List Nat} (hA : ColumnEq a c) (hB : ColumnEq b d) :
    ColumnLt a b ↔ ColumnLt c d := by
  constructor
  · intro h; exact ColumnLt.of_eq_of_lt hA.symm (ColumnLt.of_lt_of_eq h hB)
  · intro h; exact ColumnLt.of_eq_of_lt hA (ColumnLt.of_lt_of_eq h hB.symm)

theorem ColumnLe.congr_iff {a b c d : List Nat} (hA : ColumnEq a c) (hB : ColumnEq b d) :
    ColumnLe a b ↔ ColumnLe c d := by
  constructor
  · rintro (hEq | hLt)
    · exact Or.inl (hA.symm.trans (hEq.trans hB))
    · exact Or.inr ((ColumnLt.congr_iff hA hB).mp hLt)
  · rintro (hEq | hLt)
    · exact Or.inl (hA.trans (hEq.trans hB.symm))
    · exact Or.inr ((ColumnLt.congr_iff hA hB).mpr hLt)

/-- 实际编码中，同前层父项的两列，后缀严格比较等于该层数值比较。 -/
theorem encode_suffix_lt_iff_of_previous_eq (s : Expr) (row : Nat) {left right : Nat}
    (hL : left < s.values.length) (hR : right < s.values.length)
    (hPrevious : (layerAfter row ⟨s.values, linearParent⟩).previous left =
      (layerAfter row ⟨s.values, linearParent⟩).previous right) :
    ColumnLt (columnSuffix (encode s).raw left row) (columnSuffix (encode s).raw right row) ↔
      (layerAfter row ⟨s.values, linearParent⟩).values[left]?.getD 0 <
        (layerAfter row ⟨s.values, linearParent⟩).values[right]?.getD 0 := by
  rw [ColumnLt.congr_iff (encode_suffix_eq_mountainColumn s hL row)
    (encode_suffix_eq_mountainColumn s hR row)]
  exact mountainColumn_lt_iff_of_common_chain (legal_layerAfter_rootInvariant s.legal row)
    (by simpa [layerAfter_length] using hL) (by simpa [layerAfter_length] using hR)
    (ancestor_iff_of_parent_eq hPrevious)

/-- 实际编码中同前层父项的非严格后缀比较；这是结构条件 S 的比较接口。 -/
theorem encode_suffix_le_iff_of_previous_eq (s : Expr) (row : Nat) {left right : Nat}
    (hL : left < s.values.length) (hR : right < s.values.length)
    (hPrevious : (layerAfter row ⟨s.values, linearParent⟩).previous left =
      (layerAfter row ⟨s.values, linearParent⟩).previous right) :
    ColumnLe (columnSuffix (encode s).raw left row) (columnSuffix (encode s).raw right row) ↔
      (layerAfter row ⟨s.values, linearParent⟩).values[left]?.getD 0 ≤
        (layerAfter row ⟨s.values, linearParent⟩).values[right]?.getD 0 := by
  rw [ColumnLe.congr_iff (encode_suffix_eq_mountainColumn s hL row)
    (encode_suffix_eq_mountainColumn s hR row)]
  exact mountainColumn_le_iff_of_common_chain (legal_layerAfter_rootInvariant s.legal row)
    (by simpa [layerAfter_length] using hL) (by simpa [layerAfter_length] using hR)
    (ancestor_iff_of_parent_eq hPrevious)

end ZeroY
