import ZeroY.Structural.DecodeTower
import ZeroY.Forest.Blocker
import ZeroY.Forest.MatrixParents
import ZeroY.PaddedExt

/-!
# 原始往返条件与纯矩阵结构条件

条件 I 与 S 保持 `MatrixOrder` 中的原始定义。必要性来自实际山脉中的阻挡
阈值，充分性通过给定父森林上的反向求和重建进行。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem layerAfter_succ_eq_next (row : Nat) (layer : Layer) :
    layerAfter (row + 1) layer = nextLayer (layerAfter row layer) := by
  induction row generalizing layer with
  | zero => rfl
  | succ row ih => exact ih (nextLayer layer)

theorem parent_encode (s : Expr) (row : Nat) :
    parent row (encode s).raw = layerParent (layerAfter row ⟨s.values, linearParent⟩) := by
  rw [encode_raw_eq_encodeRaw]
  exact parent_encodeRaw s.legal row

theorem previousParent_encode (s : Expr) (row : Nat) :
    previousParent (encode s).raw row = (layerAfter row ⟨s.values, linearParent⟩).previous := by
  cases row with
  | zero => rfl
  | succ row =>
      rw [layerAfter_succ_eq_next]
      exact parent_encode s row

/-- 所有合法编码都满足纯矩阵阻挡条件 S。 -/
theorem encode_blockerCondition (s : Expr) : BlockerCondition (encode s).raw := by
  intro row column q p hColumn hQ hP hDistinct
  have hColumnValid : column < s.values.length := by simpa only [encode_length] using hColumn
  rw [previousParent_encode] at hQ
  rw [parent_encode] at hP
  have hInv := legal_layerAfter_rootInvariant s.legal row
  have hNearest : Forest.nearestSmaller (layerAfter row ⟨s.values, linearParent⟩).previous
      (fun i => (layerAfter row ⟨s.values, linearParent⟩).values[i]?.getD 0) column = some p := by
    rw [← Forest.layerParent_eq_nearestSmaller]
    exact hP
  obtain ⟨z, hZPath, hZParent, hValueLe⟩ :=
    Forest.nearestSmaller_exists_blocker hInv.leftward hQ hNearest hDistinct
  rw [← Forest.layerParent_eq_nearestSmaller] at hZPath hZParent
  have hZColumn : z < column := by
    have hQLt := hInv.leftward hQ
    rcases hZPath with rfl | hZPath
    · exact hQLt
    · exact Nat.lt_trans (Forest.ancestor_lt (fun h => layerParent_some_lt h) hZPath) hQLt
  have hZValid : z < s.values.length := Nat.lt_trans hZColumn hColumnValid
  refine ⟨z, ?_, ?_, ?_⟩
  · rcases hZPath with rfl | hZPath
    · exact Or.inl rfl
    · apply Or.inr
      apply isAncestor_iff_strictAncestor.mpr
      change Forest.Ancestor (parent row (encode s).raw) q z
      rw [parent_encode]
      exact hZPath
  · rw [parent_encode]
    exact hZParent
  · apply (encode_suffix_le_iff_of_previous_eq s (row + 1) hColumnValid hZValid ?_).mpr
    · rw [layerAfter_succ_eq_next]
      change (nextLayer (layerAfter row ⟨s.values, linearParent⟩)).values[column]?.getD 0 ≤
        (nextLayer (layerAfter row ⟨s.values, linearParent⟩)).values[z]?.getD 0
      rw [nextLayer_getD (by simpa [layerAfter_length] using hColumnValid),
        nextLayer_getD (by simpa [layerAfter_length] using hZValid), hP, hZParent]
      simp only
      omega
    · rw [layerAfter_succ_eq_next]
      exact hP.trans hZParent.symm

theorem encode_structural (s : Expr) : Structural (encode s).raw :=
  ⟨encode_depthRegular s, encode_blockerCondition s⟩

/-- 可逆性必然满足 I 与 S；矩阵无需标准。 -/
theorem structural_of_roundTrip (array : ValidArray) (hRoundTrip : RoundTrip array.raw) :
    Structural array.raw := by
  obtain ⟨s, rfl⟩ := (roundTrip_iff_exists_encode array).mp hRoundTrip
  exact encode_structural s

/-- 高行已重建时，S 的后缀比较足以逐列恢复当前给定父图。 -/
theorem decodeTower_parent_of_upper (array : ValidArray) (hStructural : Structural array.raw)
    (row fuel : Nat)
    (hMatrixParent : parent row array.raw =
      Forest.nearestSmaller (previousParent array.raw row)
        (fun column => matrixEntry array.raw column row))
    (hUpper : ∀ column, column < array.raw.length →
      ColumnEq (columnSuffix array.raw column (row + 1))
        (mountainColumn ⟨decodeTower array.raw (row + 1) fuel,
          previousParent array.raw (row + 1)⟩ column)) :
    layerParent ⟨decodeTower array.raw row (fuel + 1), previousParent array.raw row⟩ =
      parent row array.raw := by
  let current : Layer := ⟨decodeTower array.raw row (fuel + 1), previousParent array.raw row⟩
  let upper : Layer := ⟨decodeTower array.raw (row + 1) fuel,
    previousParent array.raw (row + 1)⟩
  have hInv : current.RootInvariant := decodeTower_rootInvariant array.raw row (fuel + 1)
  have hUpperInv : upper.RootInvariant := decodeTower_rootInvariant array.raw (row + 1) fuel
  have hLen : current.values.length = array.raw.length := decodeTower_length _ _ _
  have hUpperLen : upper.values.length = array.raw.length := decodeTower_length _ _ _
  have hEquation (column : Nat) (hColumn : column < array.raw.length) :
      current.values[column]?.getD 0 =
        match parent row array.raw column with
        | none => upper.values[column]?.getD 0
        | some found => upper.values[column]?.getD 0 + current.values[found]?.getD 0 := by
    exact sumRow_getD (parent := parent row array.raw) (fun h => parent_some_lt h)
      (by simpa only [decodeTower_length] using hColumn)
  change layerParent current = parent row array.raw
  funext column
  induction column using Nat.strongRecOn with
  | ind column ih =>
      by_cases hColumn : column < array.raw.length
      · have hCurrentColumn : column < current.values.length := by omega
        cases hp : parent row array.raw column with
        | none =>
            apply layerParent_none_of_value_one hInv.positive hCurrentColumn
            exact decodeTower_getD_of_parent_none array.raw row (fuel + 1) hColumn hp
        | some p =>
            have hOld : Forest.nearestSmaller current.previous
                (fun i => matrixEntry array.raw i row) column = some p := by
              rw [← hMatrixParent]
              exact hp
            have hPAnc := ((Forest.nearestSmaller_some_iff hInv.leftward).mp hOld).1
            have hLower : current.values[p]?.getD 0 < current.values[column]?.getD 0 := by
              have hEq := hEquation column hColumn
              have hPositive := decodeTower_getD_positive array.raw (row + 1) fuel hColumn
              change 0 < upper.values[column]?.getD 0 at hPositive
              rw [hp] at hEq
              simp only at hEq
              omega
            rw [Forest.layerParent_eq_nearestSmaller]
            cases hQ : current.previous column with
            | none =>
                rcases transGen_head hPAnc with hd | ⟨next, hn, _⟩
                · simp [hQ] at hd
                · simp [hQ] at hn
            | some q =>
                by_cases hEqual : p = q
                · subst q
                  exact Forest.nearestSmaller_eq_of_direct hInv.leftward hQ hLower
                · obtain ⟨z, hZPath, hZParent, hLe⟩ :=
                    hStructural.2 row column q p hColumn hQ hp hEqual
                  have hQLt : q < column := hInv.leftward hQ
                  have hZLt : z < column := by
                    rcases hZPath with rfl | hZPath
                    · exact hQLt
                    · exact Nat.lt_trans (isAncestor_lt hZPath) hQLt
                  have hZValid : z < array.raw.length := Nat.lt_trans hZLt hColumn
                  have hUpperPrevious : upper.previous column = upper.previous z :=
                    hp.trans hZParent.symm
                  have hUpperValue : upper.values[column]?.getD 0 ≤ upper.values[z]?.getD 0 := by
                    apply (mountainColumn_le_iff_of_common_chain hUpperInv
                      (by omega) (by omega) (Forest.ancestor_iff_of_parent_eq hUpperPrevious)).mp
                    exact (ColumnLe.congr_iff (hUpper column hColumn) (hUpper z hZValid)).mp hLe
                  apply Forest.nearestSmaller_eq_of_blocker hInv.leftward
                    (fun h => parent_some_lt h) hQ hPAnc
                  · intro i hi
                    have hEarlier := ih i hi
                    rw [Forest.layerParent_eq_nearestSmaller] at hEarlier
                    exact hEarlier.symm
                  · rcases hZPath with rfl | hZPath
                    · exact Or.inl rfl
                    · exact Or.inr (isAncestor_iff_strictAncestor.mp hZPath)
                  · exact hZParent
                  · exact hLower
                  · have hI := hEquation column hColumn
                    have hZ := hEquation z hZValid
                    rw [hp] at hI
                    rw [hZParent] at hZ
                    simp only at hI hZ
                    omega
      · have hCurrent : ¬ column < current.values.length := by omega
        simp only [layerParent, hCurrent, ↓reduceIte]
        symm
        exact parent_eq_none_iff.mpr (Or.inl (by omega))

/-- 对任意足够高的解码塔，I 与 S 逐层重建其全部实际山脉后缀。 -/
theorem decodeTower_reconstruct (array : ValidArray) (hStructural : Structural array.raw)
    (row fuel : Nat) (hHeight : trimHeight array.raw ≤ row + fuel) :
    layerParent ⟨decodeTower array.raw row fuel, previousParent array.raw row⟩ =
        parent row array.raw ∧
      ∀ column, column < array.raw.length →
        ColumnEq (columnSuffix array.raw column row)
          (mountainColumn ⟨decodeTower array.raw row fuel, previousParent array.raw row⟩ column) := by
  induction fuel generalizing row with
  | zero =>
      have hDone : (Layer.mk (decodeTower array.raw row 0)
          (previousParent array.raw row)).values.all (fun value => value == 1) = true := by
        simp [decodeTower]
      refine ⟨?_, ?_⟩
      · funext column
        rw [layerParent_none_of_all_ones hDone column,
          bms_parent_none_of_trimHeight_le (by omega) column]
      · intro column hColumn index
        rw [columnEntry_suffix, matrixEntry_zero_of_trimHeight_le _ (by omega)]
        rw [mountainColumn_entry_depth (decodeTower_rootInvariant array.raw row 0).positive
          (by simpa [decodeTower_length] using hColumn)]
        symm
        apply Forest.parentDepth_none
        exact layerParent_none_of_all_ones (layerAfter_all_ones_of_all_ones hDone index) column
  | succ fuel ih =>
      obtain ⟨_, hUpper⟩ := ih (row + 1) (by omega)
      have hParent := decodeTower_parent_of_upper array hStructural row fuel
        (parent_eq_nearestSmaller array.rectangular_eq row) hUpper
      have hNext := nextLayer_decodeTower array.raw row fuel hParent
      refine ⟨hParent, ?_⟩
      intro column hColumn index
      rw [columnEntry_suffix, mountainColumn_entry_depth
        (decodeTower_rootInvariant array.raw row (fuel + 1)).positive
        (by simpa [decodeTower_length] using hColumn)]
      cases index with
      | zero =>
          simp only [Nat.add_zero, layerAfter]
          rw [hParent]
          exact depthRegular_eq_parentDepth hStructural.1 row column hColumn
      | succ index =>
          rw [layerAfter, hNext]
          have hUpperEntry := hUpper column hColumn index
          rw [columnEntry_suffix, mountainColumn_entry_depth
            (decodeTower_rootInvariant array.raw (row + 1) fuel).positive
            (by simpa [decodeTower_length] using hColumn)] at hUpperEntry
          simpa only [Nat.add_assoc, Nat.add_comm 1] using hUpperEntry

/-- I 与 S 已足以恢复全部补零矩阵坐标。 -/
theorem structural_encode_decode_entries (array : ValidArray)
    (hStructural : Structural array.raw) (column : Nat) (hColumn : column < array.raw.length)
    (row : Nat) :
    matrixEntry (encode (decode array)).raw column row = matrixEntry array.raw column row := by
  have hShape := (decodeTower_reconstruct array hStructural 0 (trimHeight array.raw)
    (by omega)).2 column hColumn row
  rw [columnEntry_suffix, mountainColumn_entry_depth
    (decodeTower_rootInvariant array.raw 0 (trimHeight array.raw)).positive
    (by simpa [decodeTower_length] using hColumn)] at hShape
  rw [decodeTower_eq_decodeRaw] at hShape
  rw [encode_entry_depth (decode array)
    (by simpa only [decode_values, decodeRaw_length] using hColumn)]
  have hPrevious : previousParent array.raw 0 = linearParent := by funext i; rfl
  rw [hPrevious, Nat.zero_add] at hShape
  exact hShape.symm

/-- 纯矩阵 I 与 S 足以保证实际编码解码往返恢复规范矩阵。 -/
theorem encode_decode_of_structural (array : ValidArray) (hStructural : Structural array.raw) :
    encode (decode array) = array := by
  apply validArray_eq_of_padded_entries
  · simp only [encode_length, decode_values, decodeRaw_length]
  · intro column hColumn row
    have hValid : column < array.raw.length := by
      simpa only [encode_length, decode_values, decodeRaw_length] using hColumn
    exact structural_encode_decode_entries array hStructural column hValid row

theorem roundTrip_of_structural (array : ValidArray) (hStructural : Structural array.raw) :
    RoundTrip array.raw :=
  (roundTrip_iff_exists_encode array).mpr ⟨decode array, encode_decode_of_structural array hStructural⟩

/-- 所有规范矩阵可逆，当且仅当满足原始定义中的条件 I 与 S。 -/
theorem roundTrip_iff_structural (array : ValidArray) :
    RoundTrip array.raw ↔ Structural array.raw :=
  ⟨structural_of_roundTrip array, roundTrip_of_structural array⟩

/-- 结构条件与合法编码像的纯矩阵识别，同样不限于标准式。 -/
theorem structural_iff_exists_encode (array : ValidArray) :
    Structural array.raw ↔ ∃ s : Expr, encode s = array :=
  (roundTrip_iff_structural array).symm.trans (roundTrip_iff_exists_encode array)

end ZeroY
