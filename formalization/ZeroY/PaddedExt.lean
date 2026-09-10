import ZeroY.RoundTrip

/-!
# 规范矩阵的补零坐标外延性

共同尾零行已裁掉的矩形矩阵，由列数和全部补零条目唯一决定。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem supportHeight_cons (value : Nat) (rest : List Nat) :
    supportHeight (value :: rest) =
      if supportHeight rest = 0 then (if value = 0 then 0 else 1)
      else supportHeight rest + 1 := by
  simp only [supportHeight_eq_relativeSupport]
  change (match _ with
    | 0 => if value == 0 then 0 else 1
    | height + 1 => height + 2) = _
  split <;> simp_all

theorem supportHeight_le_of_getD_zero (column : List Nat) (height : Nat)
    (hZero : ∀ row, height ≤ row → column[row]?.getD 0 = 0) :
    supportHeight column ≤ height := by
  induction column generalizing height with
  | nil => exact Nat.zero_le _
  | cons value rest ih =>
      cases height with
      | zero =>
          have hValue : value = 0 := hZero 0 (Nat.zero_le _)
          have hRest : supportHeight rest = 0 := Nat.eq_zero_of_le_zero
            (ih 0 (fun row _ => hZero (row + 1) (Nat.zero_le _)))
          simp [supportHeight_cons, hValue, hRest]
      | succ height =>
          have hRest := ih height (fun row hRow => hZero (row + 1) (by omega))
          rw [supportHeight_cons]
          split
          · split <;> omega
          · omega

theorem trimHeight_le_of_entries_zero (array : Matrix) (height : Nat)
    (hZero : ∀ column, column < array.length → ∀ row, height ≤ row →
      matrixEntry array column row = 0) : trimHeight array ≤ height := by
  have hColumns : ∀ column ∈ array, supportHeight column ≤ height := by
    intro column hMem
    obtain ⟨index, hIndex, rfl⟩ := List.getElem_of_mem hMem
    apply supportHeight_le_of_getD_zero
    intro row hRow
    simpa only [matrixEntry, columnEntry, List.getElem?_eq_getElem hIndex,
      Option.getD_some] using hZero index hIndex row hRow
  have hFold : ∀ (remaining : Matrix) (initial : Nat),
      (∀ column ∈ remaining, supportHeight column ≤ height) → initial ≤ height →
      remaining.foldl (fun result column => max result (supportHeight column)) initial ≤ height := by
    intro remaining
    induction remaining with
    | nil => intro initial _ hInitial; exact hInitial
    | cons first rest ih =>
        intro initial hColumns hInitial
        apply ih
        · intro column hMem
          exact hColumns column (List.mem_cons_of_mem first hMem)
        · exact Nat.max_le.mpr ⟨hInitial, hColumns first List.mem_cons_self⟩
  exact hFold array 0 hColumns (Nat.zero_le _)

theorem trimHeight_eq_of_padded_entries {left right : Matrix}
    (hLength : left.length = right.length)
    (hEntries : ∀ column, column < left.length → ∀ row,
      matrixEntry left column row = matrixEntry right column row) :
    trimHeight left = trimHeight right := by
  apply Nat.le_antisymm
  · apply trimHeight_le_of_entries_zero
    intro column hColumn row hRow
    rw [hEntries column hColumn row]
    exact matrixEntry_zero_of_trimHeight_le right hRow column
  · apply trimHeight_le_of_entries_zero
    intro column hColumn row hRow
    rw [← hEntries column (by omega) row]
    exact matrixEntry_zero_of_trimHeight_le left hRow column

theorem validArray_uniform_trimHeight (array : ValidArray) :
    UniformHeight (trimHeight array.raw) array.raw := by
  obtain ⟨height, hUniform⟩ := rectangular_iff_exists_uniformHeight.mp array.rectangular_eq
  have h := uniformHeight_trimZeroRows hUniform
  rwa [array.trimmed_eq] at h

/-- 无公共尾零行的矩形表示不再含补零歧义。 -/
theorem validArray_eq_of_padded_entries {left right : ValidArray}
    (hLength : left.raw.length = right.raw.length)
    (hEntries : ∀ column, column < left.raw.length → ∀ row,
      matrixEntry left.raw column row = matrixEntry right.raw column row) : left = right := by
  have hHeight := trimHeight_eq_of_padded_entries hLength hEntries
  apply ValidArray.ext
  apply List.ext_getElem hLength
  intro column hLeft hRight
  have hLeftHeight := validArray_uniform_trimHeight left _ (List.getElem_mem hLeft)
  have hRightHeight := validArray_uniform_trimHeight right _ (List.getElem_mem hRight)
  apply List.ext_getElem (hLeftHeight.trans (hHeight.trans hRightHeight.symm))
  intro row hL hR
  have hEntry := hEntries column hLeft row
  simpa only [matrixEntry, columnEntry, List.getElem?_eq_getElem hLeft,
    List.getElem?_eq_getElem hRight, Option.getD_some,
    List.getElem?_eq_getElem hL, List.getElem?_eq_getElem hR] using hEntry

end ZeroY
