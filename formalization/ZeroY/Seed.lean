import ZeroY.Structural.Recognition

/-!
# 标准种子的实际转换

高度 h 的 BM4 种子精确对应 (1,h+1)，包含 h=0 的两个空列。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem trimHeight_seed (height : Nat) : trimHeight (seed height) = height := by
  simp [seed, trimHeight, supportHeight_replicate_zero, supportHeight_replicate_one]

theorem seed_structural (height : Nat) : Structural (seed height) := by
  constructor
  · intro row column hColumn
    have hBound : column < 2 := by simpa [seed] using hColumn
    by_cases hRow : row < height
    · match column with
      | 0 =>
          rw [bms_parent_first]
          simp [matrixEntry, columnEntry, seed, hRow]
      | 1 =>
          rw [parent_seed_one_of_lt hRow]
          simp [matrixEntry, columnEntry, seed, hRow]
      | column + 2 => omega
    · rw [bms_parent_none_of_trimHeight_le (by rw [trimHeight_seed]; omega)]
      exact matrixEntry_zero_of_trimHeight_le _ (by rw [trimHeight_seed]; omega) _
  · intro row column q p hColumn hQ hP hDistinct
    have hBound : column < 2 := by simpa [seed] using hColumn
    have hQLt := previousParent_some_lt hQ
    have hPLt := parent_some_lt hP
    exact False.elim (hDistinct (by omega))

private theorem sumRow_seed_pair {height row : Nat} (hRow : row < height) (value : Nat) :
    sumRow (parent row (seed height)) [1, value] = [1, value + 1] := by
  simp [sumRow, bms_parent_first, parent_seed_one_of_lt hRow]

private theorem seed_rows_fold (height : Nat) (rows : List Nat)
    (hRows : ∀ row ∈ rows, row < height) :
    rows.foldr (fun row upper => sumRow (parent row (seed height)) upper) [1, 1] =
      [1, rows.length + 1] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rw [List.foldr_cons, ih (fun r hr => hRows r (List.mem_cons_of_mem row hr)),
        sumRow_seed_pair (hRows row List.mem_cons_self)]
      rfl

theorem decodeRaw_seed (height : Nat) : decodeRaw (seed height) = [1, height + 1] := by
  unfold decodeRaw
  rw [trimHeight_seed]
  change (List.range height).foldr
    (fun row upper => sumRow (parent row (seed height)) upper) [1, 1] = _
  rw [seed_rows_fold height (List.range height) (by simp), List.length_range]

theorem decode_seed (height : Nat) : decode (validSeed height) = Expr.seed height := by
  apply Expr.ext
  exact decodeRaw_seed height

theorem encode_seed (height : Nat) : encode (Expr.seed height) = validSeed height := by
  rw [← decode_seed]
  exact encode_decode_of_structural _ (seed_structural height)

end ZeroY
