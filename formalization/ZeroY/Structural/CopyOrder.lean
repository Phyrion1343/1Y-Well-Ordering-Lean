import ZeroY.Structural.ExpansionCoordinates
import ZeroY.Forest.MatrixParents
import ZeroY.Forest.Comparison
import ZeroY.Forest.AncestorMonotone
import ZeroY.Mountain.CommonChain

/-!
# 同一复制块中的列后缀保序

对整个原列施加 BM4 加量公式，包括只用于边界比较的虚拟末列。证明只需要
条件 I：相同候选链上的相同深度决定相同父项，首差处祖先指示随深度不减。
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

def liftedEntry {array : ValidArray} (context : ExpansionContext array)
    (copy source row : Nat) : Nat :=
  matrixEntry array.raw source row +
    if ascending array.raw context.maximalRow context.parentColumn
      (source - context.parentColumn) row then copy * rowIncrement context row else 0

/-- 允许 source 为原末列；该虚拟列只服务于跨块边界比较。 -/
def liftedColumn {array : ValidArray} (context : ExpansionContext array)
    (copy source : Nat) : List Nat :=
  (List.range (trimHeight array.raw)).map (liftedEntry context copy source)

def liftedSuffix {array : ValidArray} (context : ExpansionContext array)
    (copy source start : Nat) : List Nat := (liftedColumn context copy source).drop start

theorem liftedColumn_entry {array : ValidArray} (context : ExpansionContext array)
    (copy source row : Nat) :
    columnEntry (liftedColumn context copy source) row = liftedEntry context copy source row := by
  by_cases hRow : row < trimHeight array.raw
  · simp [columnEntry, liftedColumn, List.getElem?_range hRow]
  · have hMaximal := maximalRow_lt_height context
    have hNotAscending : ascending array.raw context.maximalRow context.parentColumn
        (source - context.parentColumn) row = false := by
      simp [ascending, show ¬ row < context.maximalRow by omega]
    have hNil : (List.range (trimHeight array.raw))[row]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [show columnEntry (liftedColumn context copy source) row = 0 by
      simp [columnEntry, liftedColumn, hNil]]
    simp [liftedEntry, hNotAscending,
      matrixEntry_zero_of_height_le (uniformHeight_valid array) (by omega : trimHeight array.raw ≤ row)]

theorem liftedSuffix_entry {array : ValidArray} (context : ExpansionContext array)
    (copy source start index : Nat) :
    columnEntry (liftedSuffix context copy source start) index =
      liftedEntry context copy source (start + index) := by
  simp only [liftedSuffix, columnEntry, List.getElem?_drop]
  exact liftedColumn_entry context copy source (start + index)

/-- 共用候选链的两列若坐标深度相同，则本行父项相同。 -/
theorem parent_eq_of_previous_eq_entry_eq {array : ValidArray} (hI : DepthRegular array.raw)
    {row left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hPrevious : previousParent array.raw row left = previousParent array.raw row right)
    (hEntry : matrixEntry array.raw left row = matrixEntry array.raw right row) :
    parent row array.raw left = parent row array.raw right := by
  have hParents := parent_eq_nearestSmaller array.rectangular_eq row
  have hDepth : parentDepth (parent row array.raw) left = parentDepth (parent row array.raw) right := by
    rw [← depthRegular_eq_parentDepth hI row left hL,
      ← depthRegular_eq_parentDepth hI row right hR]
    exact hEntry
  rw [hParents] at hDepth ⊢
  exact Forest.nearestSmaller_eq_of_common_chain_depth_eq
    (fun h => previousParent_some_lt h) (Forest.ancestor_iff_of_parent_eq hPrevious) hDepth

/-- 早期后缀坐标相同时，后续首次比较仍共用同一个候选森林。 -/
theorem previous_eq_of_equal_rows {array : ValidArray} (hI : DepthRegular array.raw)
    {left right start : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    (count : Nat)
    (hEntries : ∀ index, index < count →
      matrixEntry array.raw left (start + index) = matrixEntry array.raw right (start + index)) :
    previousParent array.raw (start + count) left = previousParent array.raw (start + count) right := by
  induction count with
  | zero => simpa using hPrevious
  | succ count ih =>
      have hPrev := ih (fun i hi => hEntries i (by omega))
      have hParents := parent_eq_of_previous_eq_entry_eq hI hL hR hPrev
        (hEntries count (by omega))
      rw [show start + (count + 1) = (start + count) + 1 by omega]
      exact hParents

theorem ascending_eq_of_parent_eq {array : ValidArray} (context : ExpansionContext array)
    {row left right : Nat} (hL : context.parentColumn < left) (hR : context.parentColumn < right)
    (hParent : parent row array.raw left = parent row array.raw right) :
    ascending array.raw context.maximalRow context.parentColumn (left - context.parentColumn) row =
      ascending array.raw context.maximalRow context.parentColumn (right - context.parentColumn) row := by
  have hAsc := isAncestor_congr_of_parent_eq hParent context.parentColumn
  simp only [ascending, Nat.add_sub_of_le (Nat.le_of_lt hL), Nat.add_sub_of_le (Nat.le_of_lt hR)]
  have hLeft : (left - context.parentColumn == 0) = false := by simp; omega
  have hRight : (right - context.parentColumn == 0) = false := by simp; omega
  rw [hLeft, hRight, Bool.false_or, Bool.false_or, hAsc]

theorem ascending_mono_of_previous_eq {array : ValidArray} (context : ExpansionContext array)
    {row left right : Nat} (hL : context.parentColumn < left) (hR : context.parentColumn < right)
    (hPrevious : previousParent array.raw row left = previousParent array.raw row right)
    (hEntry : matrixEntry array.raw left row ≤ matrixEntry array.raw right row)
    (hAscending : ascending array.raw context.maximalRow context.parentColumn
      (left - context.parentColumn) row = true) :
    ascending array.raw context.maximalRow context.parentColumn
      (right - context.parentColumn) row = true := by
  have hLeft : (left - context.parentColumn == 0) = false := by simp; omega
  have hRight : (right - context.parentColumn == 0) = false := by simp; omega
  simp only [ascending, Nat.add_sub_of_le (Nat.le_of_lt hL), hLeft, Bool.false_or,
    Bool.and_eq_true] at hAscending
  simp only [ascending, Nat.add_sub_of_le (Nat.le_of_lt hR), hRight, Bool.false_or,
    Bool.and_eq_true]
  exact ⟨hAscending.1, matrix_ancestor_mono_of_previous_eq array.rectangular_eq
    hPrevious hEntry hAscending.2⟩

private theorem liftedEntry_eq_of_previous_eq_entry_eq {array : ValidArray}
    (context : ExpansionContext array) (hI : DepthRegular array.raw)
    {row left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLeftBad : context.parentColumn < left) (hRightBad : context.parentColumn < right)
    (hPrevious : previousParent array.raw row left = previousParent array.raw row right)
    (hEntry : matrixEntry array.raw left row = matrixEntry array.raw right row) (copy : Nat) :
    liftedEntry context copy left row = liftedEntry context copy right row := by
  have hParent := parent_eq_of_previous_eq_entry_eq hI hL hR hPrevious hEntry
  have hAscending := ascending_eq_of_parent_eq context hLeftBad hRightBad hParent
  simp only [liftedEntry, hEntry, hAscending]

/-- 共候选链的相等后缀在同一复制变换下仍相等。 -/
theorem liftedSuffix_eq_of_common_previous {array : ValidArray}
    (context : ExpansionContext array) (hI : DepthRegular array.raw)
    {start left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLeftBad : context.parentColumn < left) (hRightBad : context.parentColumn < right)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    (hSuffix : ColumnEq (columnSuffix array.raw left start) (columnSuffix array.raw right start))
    (copy : Nat) :
    ColumnEq (liftedSuffix context copy left start) (liftedSuffix context copy right start) := by
  have hEntry (index : Nat) : matrixEntry array.raw left (start + index) =
      matrixEntry array.raw right (start + index) := by
    simpa only [columnEntry_suffix] using hSuffix index
  intro index
  rw [liftedSuffix_entry, liftedSuffix_entry]
  apply liftedEntry_eq_of_previous_eq_entry_eq context hI hL hR hLeftBad hRightBad
  · exact previous_eq_of_equal_rows hI hL hR hPrevious index (fun i _ => hEntry i)
  · exact hEntry index

/-- 首个严格不同坐标处，加量指示从小列到大列不会由真变假。 -/
theorem liftedSuffix_lt_of_common_previous {array : ValidArray}
    (context : ExpansionContext array) (hI : DepthRegular array.raw)
    {start left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLeftBad : context.parentColumn < left) (hRightBad : context.parentColumn < right)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    (hSuffix : ColumnLt (columnSuffix array.raw left start) (columnSuffix array.raw right start))
    (copy : Nat) :
    ColumnLt (liftedSuffix context copy left start) (liftedSuffix context copy right start) := by
  obtain ⟨index, hEarlier, hLess⟩ := hSuffix
  have hEntries (i : Nat) (hi : i < index) : matrixEntry array.raw left (start + i) =
      matrixEntry array.raw right (start + i) := by
    simpa only [columnEntry_suffix] using hEarlier i hi
  have hValue : matrixEntry array.raw left (start + index) <
      matrixEntry array.raw right (start + index) := by
    simpa only [columnEntry_suffix] using hLess
  refine ⟨index, ?_, ?_⟩
  · intro i hi
    rw [liftedSuffix_entry, liftedSuffix_entry]
    apply liftedEntry_eq_of_previous_eq_entry_eq context hI hL hR hLeftBad hRightBad
    · exact previous_eq_of_equal_rows hI hL hR hPrevious i
        (fun j hj => hEntries j (by omega))
    · exact hEntries i hi
  · rw [liftedSuffix_entry, liftedSuffix_entry]
    have hPrev := previous_eq_of_equal_rows hI hL hR hPrevious index hEntries
    have hMonotone := ascending_mono_of_previous_eq context hLeftBad hRightBad hPrev
      (Nat.le_of_lt hValue)
    unfold liftedEntry
    cases hLeft : ascending array.raw context.maximalRow context.parentColumn
        (left - context.parentColumn) (start + index) with
    | false =>
        cases hRight : ascending array.raw context.maximalRow context.parentColumn
            (right - context.parentColumn) (start + index) with
        | false => exact hValue
        | true =>
            change matrixEntry array.raw left (start + index) <
              matrixEntry array.raw right (start + index) + copy * rowIncrement context (start + index)
            omega
    | true =>
        have hRight := hMonotone hLeft
        rw [hRight]
        simp only
        omega

/-- 同块加量保持整个非严格后缀序，允许源列是原来的末列。 -/
theorem liftedSuffix_le_of_common_previous {array : ValidArray}
    (context : ExpansionContext array) (hI : DepthRegular array.raw)
    {start left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLeftBad : context.parentColumn < left) (hRightBad : context.parentColumn < right)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    (hSuffix : ColumnLe (columnSuffix array.raw left start) (columnSuffix array.raw right start))
    (copy : Nat) :
    ColumnLe (liftedSuffix context copy left start) (liftedSuffix context copy right start) := by
  rcases hSuffix with hEqual | hLess
  · exact Or.inl (liftedSuffix_eq_of_common_previous context hI hL hR
      hLeftBad hRightBad hPrevious hEqual copy)
  · exact Or.inr (liftedSuffix_lt_of_common_previous context hI hL hR
      hLeftBad hRightBad hPrevious hLess copy)

/-- 普通证明引理 7 的直接接口：共用本行父项的两列，其高行后缀同块保序。 -/
theorem liftedSuffix_le_of_common_parent {array : ValidArray}
    (context : ExpansionContext array) (hI : DepthRegular array.raw)
    {row left right : Nat} (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLeftBad : context.parentColumn < left) (hRightBad : context.parentColumn < right)
    (hParent : parent row array.raw left = parent row array.raw right)
    (hSuffix : ColumnLe (columnSuffix array.raw left (row + 1))
      (columnSuffix array.raw right (row + 1))) (copy : Nat) :
    ColumnLe (liftedSuffix context copy left (row + 1))
      (liftedSuffix context copy right (row + 1)) :=
  liftedSuffix_le_of_common_previous (start := row + 1) context hI hL hR
    hLeftBad hRightBad hParent hSuffix copy

end ZeroY.BMS
