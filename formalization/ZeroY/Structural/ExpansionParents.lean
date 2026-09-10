import ZeroY.Structural.Prefix
import YesMetaZFC.BMS.Lemma25

/-!
# 展开副本的直接父项

从上游已经核验的五条祖先复制规律，提取结构保持所需的直接父项等式。
-/

namespace ZeroY.BMS

open YesMetaZFC.BMS

theorem parent_expand_prefix {array : ValidArray} (context : ExpansionContext array)
    (index row : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    parent row (array.expand index).raw column = parent row array.raw column := by
  change parent row (trimZeroRows (expandRaw array.raw index)) column = _
  rw [bms_parent_trimZeroRows]
  exact context.parent_expandRaw_eq_of_lt_lastIndex index row hColumn

theorem isAncestor_expand_prefix {array : ValidArray} (context : ExpansionContext array)
    (index row ancestor : Nat) {column : Nat} (hColumn : column < context.lastIndex) :
    isAncestor (array.expand index).raw row ancestor column = isAncestor array.raw row ancestor column := by
  apply isAncestor_congr_below
  intro earlier hEarlier
  exact parent_expand_prefix context index row (by omega)

theorem parent_expand_indices {array : ValidArray} (context : ExpansionContext array)
    {smallerIndex largerIndex column : Nat} (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length) (row : Nat) :
    parent row (array.expand smallerIndex).raw column =
      parent row (array.expand largerIndex).raw column := by
  change parent row (trimZeroRows (expandRaw array.raw smallerIndex)) column =
    parent row (trimZeroRows (expandRaw array.raw largerIndex)) column
  rw [bms_parent_trimZeroRows, bms_parent_trimZeroRows]
  have hSmaller : column < (expandRaw array.raw smallerIndex).length := by
    simpa [ValidArray.raw_expand, YesMetaZFC.BMS.expand] using hColumn
  have hLarger : column < (expandRaw array.raw largerIndex).length := by
    have := context.length_expand_mono hIndices
    have h := Nat.lt_of_lt_of_le hColumn this
    simpa [ValidArray.raw_expand, YesMetaZFC.BMS.expand] using h
  apply parent_eq_of_entry?_eq_below hSmaller hLarger
  intro earlier hEarlier entryRow
  exact context.entry?_expandRaw_indices_eq_of_lt_length hIndices (by omega)

theorem isAncestor_expand_indices {array : ValidArray} (context : ExpansionContext array)
    {smallerIndex largerIndex column : Nat} (hIndices : smallerIndex ≤ largerIndex)
    (hColumn : column < (array.expand smallerIndex).raw.length) (row ancestor : Nat) :
    isAncestor (array.expand smallerIndex).raw row ancestor column =
      isAncestor (array.expand largerIndex).raw row ancestor column := by
  apply isAncestor_congr_below
  intro earlier hEarlier
  exact parent_expand_indices context hIndices (by omega) row

/-- 好部固定，坏部列平移到指定副本。 -/
def copyColumn {array : ValidArray} (context : ExpansionContext array) (copy column : Nat) : Nat :=
  if column < context.parentColumn then column else column + copy * context.blockLength

theorem copyColumn_zero {array : ValidArray} (context : ExpansionContext array) (column : Nat) :
    copyColumn context 0 column = column := by simp [copyColumn]

theorem copyColumn_good {array : ValidArray} (context : ExpansionContext array)
    (copy : Nat) {column : Nat} (hColumn : column < context.parentColumn) :
    copyColumn context copy column = column := by simp [copyColumn, hColumn]

theorem copyColumn_bad {array : ValidArray} (context : ExpansionContext array)
    (copy : Nat) {column : Nat} (hColumn : context.parentColumn ≤ column) :
    copyColumn context copy column = context.copyPosition copy (column - context.parentColumn) := by
  simp only [copyColumn, show ¬ column < context.parentColumn by omega, ↓reduceIte,
    ExpansionContext.copyPosition, ExpansionContext.copyStart]
  omega

theorem copyColumn_local {array : ValidArray} (context : ExpansionContext array)
    (copy localColumn : Nat) :
    copyColumn context copy (context.parentColumn + localColumn) =
      context.copyPosition copy localColumn := by
  rw [copyColumn_bad context copy (by omega)]
  simp

theorem copyColumn_le {array : ValidArray} (context : ExpansionContext array)
    (copy : Nat) {first second : Nat} (hOrder : first ≤ second) :
    copyColumn context copy first ≤ copyColumn context copy second := by
  simp only [copyColumn]
  split <;> split <;> omega

theorem copyColumn_lt {array : ValidArray} (context : ExpansionContext array)
    (copy : Nat) {first second : Nat} (hOrder : first < second) :
    copyColumn context copy first < copyColumn context copy second := by
  simp only [copyColumn]
  split <;> split <;> omega

theorem copyColumn_ge {array : ValidArray} (context : ExpansionContext array)
    (copy column : Nat) : column ≤ copyColumn context copy column := by
  simp only [copyColumn]
  split <;> omega

theorem copyColumn_injective {array : ValidArray} (context : ExpansionContext array)
    (copy : Nat) {first second : Nat}
    (hEqual : copyColumn context copy first = copyColumn context copy second) : first = second := by
  rcases Nat.lt_trichotomy first second with h | h | h
  · have := copyColumn_lt context copy h; omega
  · exact h
  · have := copyColumn_lt context copy h; omega

/-- 原数组与第 n 个副本的同一祖先关系，包含好部祖先。 -/
theorem isAncestor_copied {array : ValidArray} (context : ExpansionContext array)
    (index row : Nat) {candidate localColumn : Nat}
    (hCandidate : candidate < context.lastIndex) (hLocal : localColumn < context.blockLength) :
    isAncestor array.raw row candidate (context.parentColumn + localColumn) =
      isAncestor (array.expand index).raw row (copyColumn context index candidate)
        (context.copyPosition index localColumn) := by
  have hTarget : context.parentColumn + localColumn < context.lastIndex := by
    have := context.parentColumn_lt_lastIndex
    simp only [ExpansionContext.blockLength] at hLocal
    omega
  have hOriginal : isAncestor (array.expand index).raw row candidate
      (context.copyPosition 0 localColumn) =
        isAncestor array.raw row candidate (context.parentColumn + localColumn) := by
    simpa only [ExpansionContext.copyPosition_zero] using
      isAncestor_expand_prefix context index row candidate hTarget
  rw [← hOriginal]
  by_cases hGood : candidate < context.parentColumn
  · rw [copyColumn_good context index hGood]
    exact (context.lemma25_all index row).good_to_copy hGood hLocal
  · have hLocalCandidate : candidate - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    have hCandidateEq : context.copyPosition 0 (candidate - context.parentColumn) = candidate := by
      rw [ExpansionContext.copyPosition_zero]
      omega
    rw [copyColumn_bad context index (by omega)]
    simpa only [hCandidateEq] using
      (context.lemma25_all index row).inside_copy hLocalCandidate hLocal

/-- 非首列的展开父项总能唯一追溯为一个原祖先的副本。 -/
theorem copied_parent_source {array : ValidArray} (context : ExpansionContext array)
    {index row localColumn found : Nat} (hPositive : 0 < localColumn)
    (hLocal : localColumn < context.blockLength)
    (hParent : parent row (array.expand index).raw
      (context.copyPosition index localColumn) = some found) :
    ∃ source, source < context.lastIndex ∧ found = copyColumn context index source ∧
      isAncestor array.raw row source (context.parentColumn + localColumn) = true := by
  have hAncestor := direct_parent_isAncestor hParent
  rcases (context.lemma25_all index row).parent_locality hPositive hLocal hParent with hGood | hCopy
  · have hSource : found < context.lastIndex := Nat.lt_trans hGood context.parentColumn_lt_lastIndex
    refine ⟨found, hSource, (copyColumn_good context index hGood).symm, ?_⟩
    rw [isAncestor_copied context index row hSource hLocal, copyColumn_good context index hGood]
    exact hAncestor
  · rcases context.inCopy_iff_exists_copyPosition.mp hCopy with ⟨sourceLocal, hSourceLocal, rfl⟩
    have hSource : context.parentColumn + sourceLocal < context.lastIndex := by
      simp only [ExpansionContext.blockLength] at hSourceLocal
      omega
    refine ⟨context.parentColumn + sourceLocal, hSource,
      (copyColumn_local context index sourceLocal).symm, ?_⟩
    rw [isAncestor_copied context index row hSource hLocal, copyColumn_local]
    exact hAncestor

/-- 非首列的直接父项：好部固定，坏部移到同一副本。 -/
theorem parent_copied_nonroot {array : ValidArray} (context : ExpansionContext array)
    (index row : Nat) {localColumn : Nat} (hPositive : 0 < localColumn)
    (hLocal : localColumn < context.blockLength) :
    parent row (array.expand index).raw (context.copyPosition index localColumn) =
      (parent row array.raw (context.parentColumn + localColumn)).map (copyColumn context index) := by
  have hTarget : context.parentColumn + localColumn < context.lastIndex := by
    simp only [ExpansionContext.blockLength] at hLocal
    omega
  cases hOriginal : parent row array.raw (context.parentColumn + localColumn) with
  | none =>
      cases hParent : parent row (array.expand index).raw (context.copyPosition index localColumn) with
      | none => rfl
      | some found =>
          rcases copied_parent_source context hPositive hLocal hParent with ⟨source, _, _, hAncestor⟩
          rw [isAncestor_eq_false_of_parent_none hOriginal] at hAncestor
          contradiction
  | some p =>
      have hp : p < context.lastIndex := Nat.lt_trans (parent_some_lt hOriginal) hTarget
      have hCopied : isAncestor (array.expand index).raw row (copyColumn context index p)
          (context.copyPosition index localColumn) = true := by
        rw [← isAncestor_copied context index row hp hLocal]
        exact direct_parent_isAncestor hOriginal
      cases hParent : parent row (array.expand index).raw (context.copyPosition index localColumn) with
      | none =>
          rw [isAncestor_eq_false_of_parent_none hParent] at hCopied
          contradiction
      | some found =>
          rcases copied_parent_source context hPositive hLocal hParent with
            ⟨source, _, hFound, hAncestor⟩
          have hSourceOrder := ancestor_le_parent hOriginal hAncestor
          have hCopiedOrder := ancestor_le_parent hParent hCopied
          have hMapOrder := copyColumn_le context index hSourceOrder
          have hEqual : found = copyColumn context index p := by omega
          simp [hEqual]

/-- 最大父行及其以上，新块首列继承原坏根的直接父项。 -/
theorem parent_copied_root_high {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) {row : Nat} (hRow : context.maximalRow ≤ row) :
    parent row (array.expand index).raw (context.copyPosition index 0) =
      parent row array.raw context.parentColumn := by
  rw [← context.parent_first_copies_eq_of_maximalRow_le hRow
    (fun lower _ _ hGood => context.good_to_first_copies_all_rows index lower hGood)]
  simpa only [ExpansionContext.copyPosition_zero, Nat.add_zero] using
    parent_expand_prefix context index row context.parentColumn_lt_lastIndex

/-- 最大父行以下，新块首列继承前一块中原末列父项的副本。 -/
theorem parent_copied_root_low {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) {row : Nat} (hRow : row < context.maximalRow) :
    parent row (array.expand (index + 1)).raw (context.copyPosition (index + 1) 0) =
      (parent row array.raw context.lastIndex).map (copyColumn context index) := by
  have hRootAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  cases hOriginal : parent row array.raw context.lastIndex with
  | none =>
      rw [isAncestor_eq_false_of_parent_none hOriginal] at hRootAncestor
      contradiction
  | some p =>
      have hpLower : context.parentColumn ≤ p := ancestor_le_parent hOriginal hRootAncestor
      have hpUpper : p < context.lastIndex := parent_some_lt hOriginal
      have hpLocal : p - context.parentColumn < context.blockLength := by
        simp only [ExpansionContext.blockLength]
        omega
      have hSourceEq : context.parentColumn + (p - context.parentColumn) = p := by omega
      have hCopiedAncestor : isAncestor (array.expand (index + 1)).raw row
          (copyColumn context index p) (context.copyPosition (index + 1) 0) = true := by
        rw [copyColumn_bad context index hpLower]
        have hBridge := (context.lemma25_all (index + 1) row).previous_to_next (by omega) hRow hpLocal
        simp only [Nat.add_sub_cancel, hSourceEq] at hBridge
        rw [← hBridge]
        exact direct_parent_isAncestor hOriginal
      cases hParent : parent row (array.expand (index + 1)).raw
          (context.copyPosition (index + 1) 0) with
      | none =>
          rw [isAncestor_eq_false_of_parent_none hParent] at hCopiedAncestor
          contradiction
      | some found =>
          have hFoundLower := ancestor_le_parent hParent hCopiedAncestor
          have hFoundUpper := parent_some_lt hParent
          have hPrevEnd : context.copyPosition (index + 1) 0 =
              context.copyStart index + context.blockLength := by
            simp [ExpansionContext.copyPosition, ExpansionContext.copyStart, Nat.add_mul, Nat.add_assoc]
          have hStart : context.copyStart index ≤ copyColumn context index p := by
            rw [copyColumn_bad context index hpLower]
            simp [ExpansionContext.copyPosition]
          have hFoundCopy : context.InCopy index found := by
            constructor
            · omega
            · change found < context.copyPosition (index + 1) 0
              exact hFoundUpper
          rcases context.inCopy_iff_exists_copyPosition.mp hFoundCopy with
            ⟨localFound, hLocalFound, hFoundPosition⟩
          have hOldAncestor : isAncestor array.raw row
              (context.parentColumn + localFound) context.lastIndex = true := by
            have hBridge := (context.lemma25_all (index + 1) row).previous_to_next
              (by omega) hRow hLocalFound
            simp only [Nat.add_sub_cancel] at hBridge
            rw [hBridge, ← hFoundPosition]
            exact direct_parent_isAncestor hParent
          have hOldBound := ancestor_le_parent hOriginal hOldAncestor
          have hNewBound := copyColumn_le context index hOldBound
          rw [copyColumn_local, ← hFoundPosition] at hNewBound
          have hEqual : found = copyColumn context index p := by omega
          simp [hEqual]

theorem parent_copied_nonroot_of_le {array : ValidArray} (context : ExpansionContext array)
    {index copy localColumn : Nat} (hCopy : copy ≤ index)
    (row : Nat) (hPositive : 0 < localColumn) (hLocal : localColumn < context.blockLength) :
    parent row (array.expand index).raw (context.copyPosition copy localColumn) =
      (parent row array.raw (context.parentColumn + localColumn)).map (copyColumn context copy) := by
  rw [← parent_expand_indices context hCopy
    (context.copyPosition_lt_length (Nat.le_refl copy) hLocal) row]
  exact parent_copied_nonroot context copy row hPositive hLocal

theorem parent_copied_root_high_of_le {array : ValidArray} (context : ExpansionContext array)
    {index copy row : Nat} (hCopy : copy ≤ index) (hRow : context.maximalRow ≤ row) :
    parent row (array.expand index).raw (context.copyPosition copy 0) =
      parent row array.raw context.parentColumn := by
  rw [← parent_expand_indices context hCopy
    (context.copyPosition_lt_length (Nat.le_refl copy) context.blockLength_pos) row]
  exact parent_copied_root_high context copy hRow

theorem parent_copied_root_low_of_le {array : ValidArray} (context : ExpansionContext array)
    {index copy row : Nat} (hCopy : copy ≤ index) (hPositive : 0 < copy)
    (hRow : row < context.maximalRow) :
    parent row (array.expand index).raw (context.copyPosition copy 0) =
      (parent row array.raw context.lastIndex).map (copyColumn context (copy - 1)) := by
  rw [← parent_expand_indices context hCopy
    (context.copyPosition_lt_length (Nat.le_refl copy) context.blockLength_pos) row]
  cases copy with
  | zero => omega
  | succ copy => exact parent_copied_root_low context copy hRow

theorem parent_copyColumn_high {array : ValidArray} (context : ExpansionContext array)
    {index copy row source : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hRow : context.maximalRow ≤ row) :
    parent row (array.expand index).raw (copyColumn context copy source) =
      (parent row array.raw source).map (copyColumn context copy) := by
  by_cases hGood : source < context.parentColumn
  · rw [copyColumn_good context copy hGood, parent_expand_prefix context index row hSource]
    cases hParent : parent row array.raw source with
    | none => rfl
    | some p =>
        have hp : p < context.parentColumn := Nat.lt_trans (parent_some_lt hParent) hGood
        simp [copyColumn_good context copy hp]
  · have hLocal : source - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    rw [copyColumn_bad context copy (by omega)]
    by_cases hRoot : source = context.parentColumn
    · subst source
      simp only [Nat.sub_self]
      rw [parent_copied_root_high_of_le context hCopy hRow]
      cases hParent : parent row array.raw context.parentColumn with
      | none => rfl
      | some p => simp [copyColumn_good context copy (parent_some_lt hParent)]
    · rw [parent_copied_nonroot_of_le context hCopy row (by omega) hLocal]
      have : context.parentColumn + (source - context.parentColumn) = source := by omega
      rw [this]

theorem parent_copyColumn_nonroot {array : ValidArray} (context : ExpansionContext array)
    {index copy source : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hNonroot : source ≠ context.parentColumn) (row : Nat) :
    parent row (array.expand index).raw (copyColumn context copy source) =
      (parent row array.raw source).map (copyColumn context copy) := by
  by_cases hGood : source < context.parentColumn
  · rw [copyColumn_good context copy hGood, parent_expand_prefix context index row hSource]
    cases hParent : parent row array.raw source with
    | none => rfl
    | some p =>
        have hp : p < context.parentColumn := Nat.lt_trans (parent_some_lt hParent) hGood
        simp [copyColumn_good context copy hp]
  · have hLocal : source - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    rw [copyColumn_bad context copy (by omega),
      parent_copied_nonroot_of_le context hCopy row (by omega) hLocal]
    have : context.parentColumn + (source - context.parentColumn) = source := by omega
    rw [this]

theorem isAncestor_copyColumn {array : ValidArray} (context : ExpansionContext array)
    {index copy candidate source : Nat} (hCopy : copy ≤ index)
    (hCandidate : candidate < context.lastIndex) (hSource : source < context.lastIndex) (row : Nat) :
    isAncestor (array.expand index).raw row (copyColumn context copy candidate)
        (copyColumn context copy source) =
      isAncestor array.raw row candidate source := by
  by_cases hGood : source < context.parentColumn
  · rw [copyColumn_good context copy hGood, isAncestor_expand_prefix context index row _ hSource]
    by_cases hCandidateGood : candidate < context.parentColumn
    · rw [copyColumn_good context copy hCandidateGood]
    · have hLe := copyColumn_ge context copy candidate
      cases hLeft : isAncestor array.raw row (copyColumn context copy candidate) source with
      | true => have := isAncestor_lt hLeft; omega
      | false =>
          cases hRight : isAncestor array.raw row candidate source with
          | false => rfl
          | true => have := isAncestor_lt hRight; omega
  · have hLocal : source - context.parentColumn < context.blockLength := by
      simp only [ExpansionContext.blockLength]
      omega
    have hSourceEq : context.parentColumn + (source - context.parentColumn) = source := by omega
    rw [copyColumn_bad context copy (column := source) (by omega),
      ← isAncestor_expand_indices context hCopy
        (context.copyPosition_lt_length (Nat.le_refl copy) hLocal) row,
      ← isAncestor_copied context copy row hCandidate hLocal, hSourceEq]

end ZeroY.BMS
