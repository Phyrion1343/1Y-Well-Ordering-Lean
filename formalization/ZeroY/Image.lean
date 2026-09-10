import ZeroY.RoundTrip

/-!
# 编码像的规范性与深度正规性

合法输入产生的原始山脉编码已经没有公共尾零行。因此规范编码的归一化
步骤不改变任何列；全部编码像满足条件 I 与原始往返定义。
-/

namespace ZeroY

open YesMetaZFC.BMS

/-- 已知实际山脉在第 steps 层全为 1，则任何燃料至多记录 steps 行。 -/
theorem mountainRows_length_le_of_layerAfter_all_ones {layer : Layer} (steps fuel : Nat)
    (hDone : (layerAfter steps layer).values.all (fun value => value == 1) = true) :
    (mountainRows fuel layer).length ≤ steps := by
  induction steps generalizing layer fuel with
  | zero =>
      cases fuel <;> simp [mountainRows, layerAfter] at hDone ⊢
      exact hDone
  | succ steps ih =>
      cases fuel with
      | zero => simp [mountainRows]
      | succ fuel =>
          by_cases hOnes : layer.values.all (fun value => value == 1) = true
          · simp [mountainRows, hOnes]
          · have hNext := ih (layer := nextLayer layer) fuel hDone
            simpa [mountainRows, hOnes] using Nat.succ_le_succ hNext

theorem encodeRaw_column_length {s : Sequence} {column : List Nat}
    (hColumn : column ∈ encodeRaw s) :
    column.length = (mountainRows (maxValue s) ⟨s, linearParent⟩).length := by
  rcases List.mem_map.mp hColumn with ⟨index, _, rfl⟩
  simp

/-- 合法原始编码本身已经无公共尾零行，不只是归一化后具有此性质。 -/
theorem encodeRaw_trimmed {s : Sequence} (hLegal : Legal s) :
    trimZeroRows (encodeRaw s) = encodeRaw s := by
  have hDone : (layerAfter (trimHeight (encodeRaw s)) ⟨s, linearParent⟩).values.all
      (fun value => value == 1) = true := by
    rw [layerAfter_encodeRaw_trimHeight hLegal]
    simp
  have hHeight := mountainRows_length_le_of_layerAfter_all_ones
    (trimHeight (encodeRaw s)) (maxValue s) hDone
  unfold trimZeroRows
  calc
    List.map (fun column => column.take (trimHeight (encodeRaw s))) (encodeRaw s) =
        List.map id (encodeRaw s) := by
      apply List.map_congr_left
      intro column hColumn
      exact List.take_of_length_le (by rw [encodeRaw_column_length hColumn]; exact hHeight)
    _ = encodeRaw s := List.map_id _

/-- 规范编码的矩阵正文就是原始山脉编码。 -/
theorem encode_raw_eq_encodeRaw (s : Expr) : (encode s).raw = encodeRaw s.values :=
  encodeRaw_trimmed s.legal

/-- 原始山脉编码的每个条目就是 BM4 父链深度。 -/
theorem encodeRaw_depthRegular {s : Sequence} (hLegal : Legal s) :
    DepthRegular (encodeRaw s) := by
  intro row column hColumn
  have hOriginal : column < s.length := by simpa [encodeRaw_length] using hColumn
  rw [parent_encodeRaw hLegal]
  cases hParent : layerParent (layerAfter row ⟨s, linearParent⟩) column with
  | none =>
      rw [encodeRaw_entry_depth hLegal hOriginal row]
      exact Forest.parentDepth_none hParent
  | some found =>
      simp only
      have hFound : found < s.length := Nat.lt_trans (layerParent_some_lt hParent) hOriginal
      rw [encodeRaw_entry_depth hLegal hOriginal row,
        encodeRaw_entry_depth hLegal hFound row]
      exact Forest.parentDepth_some
        (parent := layerParent (layerAfter row ⟨s, linearParent⟩))
        (fun h => layerParent_some_lt h) hParent

theorem encode_depthRegular (s : Expr) : DepthRegular (encode s).raw := by
  rw [encode_raw_eq_encodeRaw]
  exact encodeRaw_depthRegular s.legal

/-- 每个合法原始编码都满足此前固定的原始往返谓词。 -/
theorem encodeRaw_roundTrip {s : Sequence} (hLegal : Legal s) :
    RoundTrip (encodeRaw s) := by
  unfold RoundTrip
  rw [decodeRaw_encodeRaw hLegal, encodeRaw_trimmed hLegal]

theorem encode_roundTrip (s : Expr) : RoundTrip (encode s).raw := by
  rw [encode_raw_eq_encodeRaw]
  exact encodeRaw_roundTrip s.legal

end ZeroY
