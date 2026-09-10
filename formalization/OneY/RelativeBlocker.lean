import ZeroY.Structural.Expansion
import ZeroY.Structural.Recognition
import ZeroY.Structural.ExpansionParentAlignment
import ZeroY.Transport

/-!
# Relative blocker preservation

The framing rows need depth regularity, but they need not satisfy S.
Every proof below preserves a single row of S without using S at other rows.
The original ZeroY theorem statements and entry points are unchanged.
-/

namespace OneY.RelativeBlocker

open YesMetaZFC.BMS ZeroY ZeroY.BMS

def RowS (array : Matrix) (row : Nat) : Prop :=
  ∀ column q p, column < array.length →
    previousParent array row column = some q →
    parent row array column = some p → p ≠ q →
    ∃ z, (z = q ∨ isAncestor array row z q = true) ∧
      parent row array z = some p ∧
      ColumnLe (columnSuffix array column (row + 1))
        (columnSuffix array z (row + 1))

def AboveS (array : Matrix) (base : Nat) : Prop :=
  ∀ row, base ≤ row → RowS array row

theorem relative_blockerAt_expand_prefix {array : ValidArray} {row : Nat} (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) (index : Nat) {column : Nat}
    (hColumn : column < context.lastIndex) : BlockerAt (array.expand index).raw row column := by
  intro q p hQ hP hDistinct
  have hPrevious : previousParent (array.expand index).raw row column = previousParent array.raw row column := by
    cases row with
    | zero => rfl
    | succ row => exact parent_expand_prefix context index row hColumn
  rw [hPrevious] at hQ
  rw [parent_expand_prefix context index row hColumn] at hP
  obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker column q p
    (by rw [context.array_length]; omega) hQ hP hDistinct
  have hQLt := previousParent_some_lt hQ
  have hZLt : z < column := by
    rcases hZPath with rfl | hZPath
    · exact hQLt
    · exact Nat.lt_trans (isAncestor_lt hZPath) hQLt
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [isAncestor_expand_prefix context index row _ (by omega : q < context.lastIndex)] using hZPath
  · rw [parent_expand_prefix context index row (by omega)]
    exact hZParent
  · exact ColumnLe.of_le_of_eq
      (ColumnLe.of_eq_of_le (suffix_expand_prefix context index (row + 1) hColumn) hZLe)
      (ColumnEq.symm (suffix_expand_prefix context index (row + 1) (by omega)))

theorem relative_blockerAt_copied_high {array : ValidArray} {row : Nat} (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy source : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hRow : context.maximalRow ≤ row)
    (hPrevious : previousParent (array.expand index).raw row (copyColumn context copy source) =
      (previousParent array.raw row source).map (copyColumn context copy)) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  intro q p hQ hP hDistinct
  rw [hPrevious] at hQ
  rw [parent_copyColumn_high context hCopy hSource hRow] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw source with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
          have hOldDistinct : oldP ≠ oldQ := by
            intro hEqual
            apply hDistinct
            rw [← hP, ← hQ, hEqual]
          obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker source oldQ oldP
            (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
          have hOldQLt := previousParent_some_lt hOldQ
          have hZLt : z < source := by
            rcases hZPath with rfl | hZPath
            · exact hOldQLt
            · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hZPath with rfl | hZPath
            · exact Or.inl hQ
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
              exact hZPath
          · rw [parent_copyColumn_high context hCopy (by omega) hRow, hZParent]
            simpa only [Option.map_some] using congrArg some hP
          · exact ColumnLe.of_le_of_eq
              (ColumnLe.of_eq_of_le (suffix_copyColumn_high context hCopy hSource (by omega)) hZLe)
              (ColumnEq.symm (suffix_copyColumn_high context hCopy (by omega) (by omega)))

theorem relative_blockerAt_copied_nonroot_high {array : ValidArray} {row : Nat} (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy source : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hNonroot : source ≠ context.parentColumn) (hRow : context.maximalRow ≤ row) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := relative_blockerAt_copied_high hBlocker context hCopy hSource hRow
    (previousParent_copyColumn_nonroot context hCopy hSource hNonroot row)

theorem relative_blockerAt_copied_above {array : ValidArray} {row : Nat} (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy source : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hRow : context.maximalRow < row) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := relative_blockerAt_copied_high hBlocker context hCopy hSource (Nat.le_of_lt hRow)
    (previousParent_copyColumn_high context hCopy hSource hRow)

theorem relative_blockerAt_copied_root_at {array : ValidArray} (context : ExpansionContext array)
    (hBlocker : RowS array.raw context.maximalRow) {index copy : Nat}
    (hCopy : copy + 1 ≤ index) :
    BlockerAt (array.expand index).raw context.maximalRow (context.copyPosition (copy + 1) 0) := by
  intro q p hQ hP _
  rw [previousParent_copied_root_low context hCopy (Nat.le_refl _)] at hQ
  rw [parent_copied_root_high_of_le context hCopy (Nat.le_refl _)] at hP
  cases hOldQ : previousParent array.raw context.maximalRow context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldQLt := previousParent_some_lt hOldQ
      have hRootPath : context.parentColumn = oldQ ∨
          isAncestor array.raw context.maximalRow context.parentColumn oldQ = true := by
        by_cases hEqual : context.parentColumn = oldQ
        · exact Or.inl hEqual
        · obtain ⟨z, hZPath, hZParent, _⟩ := hBlocker context.lastIndex
            oldQ context.parentColumn (by rw [context.array_length]; omega)
            hOldQ context.parent_eq hEqual
          apply Or.inr
          rcases hZPath with rfl | hZPath
          · exact direct_parent_isAncestor hZParent
          · exact isAncestor_trans (direct_parent_isAncestor hZParent) hZPath
      refine ⟨copyColumn context copy context.parentColumn, ?_, ?_, ?_⟩
      · rcases hRootPath with hEqual | hPath
        · exact Or.inl ((congrArg (copyColumn context copy) hEqual).trans hQ)
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context (by omega)
            context.parentColumn_lt_lastIndex hOldQLt]
          exact hPath
      · rw [copyColumn_bad context copy (Nat.le_refl _), Nat.sub_self,
          parent_copied_root_high_of_le context (by omega) (Nat.le_refl _)]
        exact hP
      · have hLeft := suffix_copyColumn_high context hCopy
          context.parentColumn_lt_lastIndex (start := context.maximalRow + 1) (by omega)
        have hRight := suffix_copyColumn_high context (show copy ≤ index by omega)
          context.parentColumn_lt_lastIndex (start := context.maximalRow + 1) (by omega)
        rw [copyColumn_bad context (copy + 1) (Nat.le_refl _), Nat.sub_self] at hLeft
        exact Or.inl (ColumnEq.trans hLeft (ColumnEq.symm hRight))

theorem relative_blockerAt_copied_parent_good {array : ValidArray} {row : Nat} (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy source oldP : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hNonroot : source ≠ context.parentColumn) (hRow : row < context.maximalRow)
    (hOldP : parent row array.raw source = some oldP) (hGood : oldP < context.parentColumn) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  intro q p hQ hP hDistinct
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP,
    Option.map_some, copyColumn_good context copy hGood] at hP
  have hPEq : oldP = p := Option.some.inj hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldDistinct : oldP ≠ oldQ := by
        intro hEqual
        apply hDistinct
        rw [← hPEq, ← hQ, ← hEqual, copyColumn_good context copy hGood]
      obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
      have hOldQLt := previousParent_some_lt hOldQ
      have hZLt : z < source := by
        rcases hZPath with rfl | hZPath
        · exact hOldQLt
        · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
      have hSourceSuffix := suffix_copyColumn_parent_good context hCopy hSource hNonroot hOldP hGood
      by_cases hRoot : z = context.parentColumn
      · subst z
        refine ⟨context.parentColumn, ?_, ?_, ?_⟩
        · rw [← hQ]
          exact zero_root_path_copy context hCopy hRow (by omega) hZPath
        · rw [parent_expand_prefix context index row context.parentColumn_lt_lastIndex, hZParent, hPEq]
        · exact ColumnLe.of_le_of_eq (ColumnLe.of_eq_of_le hSourceSuffix hZLe)
            (ColumnEq.symm (suffix_expand_prefix context index (row + 1) context.parentColumn_lt_lastIndex))
      · refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
        · rcases hZPath with rfl | hZPath
          · exact Or.inl hQ
          · apply Or.inr
            rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
            exact hZPath
        · rw [parent_copyColumn_nonroot context hCopy (by omega) hRoot row, hZParent,
            Option.map_some, copyColumn_good context copy hGood, hPEq]
        · exact ColumnLe.of_le_of_eq (ColumnLe.of_eq_of_le hSourceSuffix hZLe)
            (ColumnEq.symm (suffix_copyColumn_parent_good context hCopy (by omega) hRoot hZParent hGood))

theorem relative_blockerAt_copied_parent_bad {array : ValidArray} {row : Nat}
    (hI : DepthRegular array.raw) (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy source oldP : Nat}
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hOldP : parent row array.raw source = some oldP) (hBad : context.parentColumn ≤ oldP) :
    BlockerAt (array.expand index).raw row (copyColumn context copy source) := by
  have hParentLt := parent_some_lt hOldP
  have hSourceBad : context.parentColumn < source := by omega
  have hNonroot : source ≠ context.parentColumn := by omega
  intro q p hQ hP hDistinct
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP] at hP
  simp only [Option.map_some, Option.some.injEq] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hOldDistinct : oldP ≠ oldQ := by
        intro hEqual
        apply hDistinct
        rw [← hP, ← hQ, hEqual]
      obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
      have hOldQLt := previousParent_some_lt hOldQ
      have hZLt : z < source := by
        rcases hZPath with rfl | hZPath
        · exact hOldQLt
        · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
      have hPZ := parent_some_lt hZParent
      have hZBad : context.parentColumn < z := by omega
      refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
      · rcases hZPath with rfl | hZPath
        · exact Or.inl hQ
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
          exact hZPath
      · rw [parent_copyColumn_nonroot context hCopy (by omega) (by omega) row, hZParent]
        simpa only [Option.map_some] using congrArg some hP
      · have hLifted := liftedSuffix_le_of_common_parent context hI
          (by rw [context.array_length]; omega) (by rw [context.array_length]; omega)
          hSourceBad hZBad (hOldP.trans hZParent.symm) hZLe copy
        exact ColumnLe.of_le_of_eq
          (ColumnLe.of_eq_of_le (suffix_copyColumn_eq_lifted context hCopy hSource (by omega) (row + 1)) hLifted)
          (ColumnEq.symm (suffix_copyColumn_eq_lifted context hCopy (by omega) (by omega) (row + 1)))

theorem relative_blockerAt_copied_root_below {array : ValidArray} {row : Nat}
    (hI : DepthRegular array.raw) (hBlocker : RowS array.raw row)
    (context : ExpansionContext array) {index copy : Nat}
    (hCopy : copy + 1 ≤ index) (hRow : row < context.maximalRow) :
    BlockerAt (array.expand index).raw row (context.copyPosition (copy + 1) 0) := by
  intro q p hQ hP hDistinct
  rw [previousParent_copied_root_low context hCopy (Nat.le_of_lt hRow)] at hQ
  rw [parent_copied_root_low_of_le context hCopy (by omega) hRow] at hP
  simp only [Nat.add_sub_cancel] at hP
  cases hOldQ : previousParent array.raw row context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw context.lastIndex with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
          have hOldDistinct : oldP ≠ oldQ := by
            intro hEqual
            apply hDistinct
            rw [← hP, ← hQ, hEqual]
          obtain ⟨z, hZPath, hZParent, hZLe⟩ := hBlocker context.lastIndex oldQ oldP
            (by rw [context.array_length]; omega) hOldQ hOldP hOldDistinct
          have hOldQLt := previousParent_some_lt hOldQ
          have hZLt : z < context.lastIndex := by
            rcases hZPath with rfl | hZPath
            · exact hOldQLt
            · exact Nat.lt_trans (isAncestor_lt hZPath) hOldQLt
          have hRootAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
          have hOldPBad := ancestor_le_parent hOldP hRootAncestor
          have hPZ := parent_some_lt hZParent
          have hZBad : context.parentColumn < z := by omega
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hZPath with rfl | hZPath
            · exact Or.inl hQ
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context (by omega) hZLt hOldQLt]
              exact hZPath
          · rw [parent_copyColumn_nonroot context (by omega) hZLt (by omega) row, hZParent]
            simpa only [Option.map_some] using congrArg some hP
          · have hLifted := liftedSuffix_le_of_common_parent context hI
              (by rw [context.array_length]; omega) (by rw [context.array_length]; omega)
              context.parentColumn_lt_lastIndex hZBad (hOldP.trans hZParent.symm) hZLe copy
            exact ColumnLe.of_le_of_eq
              (ColumnLe.trans (Or.inr (newroot_suffix_lt_ghost context hCopy hRow)) hLifted)
              (ColumnEq.symm (suffix_copyColumn_eq_lifted context (by omega) hZLt (by omega) (row + 1)))

theorem relative_blockerCondition_expand_of_context {array : ValidArray} (hI : DepthRegular array.raw)
    (context : ExpansionContext array) (index row : Nat) (hBlocker : RowS array.raw row) :
    RowS (array.expand index).raw row := by
  intro column q p hColumn hQ hP hDistinct
  have hAt : BlockerAt (array.expand index).raw row column := by
    by_cases hPrefix : column < context.lastIndex
    · exact relative_blockerAt_expand_prefix hBlocker context index hPrefix
    · have hNotGood : context.parentColumn ≤ column := by
        have := context.parentColumn_lt_lastIndex
        omega
      rcases context.exists_copyPosition_of_not_good hColumn hNotGood with
        ⟨copy, localColumn, hCopy, hLocal, rfl⟩
      have hSource : context.parentColumn + localColumn < context.lastIndex := by
        simp only [ExpansionContext.blockLength] at hLocal
        omega
      by_cases hZero : localColumn = 0
      · subst localColumn
        cases copy with
        | zero =>
            simp only [ExpansionContext.copyPosition_zero, Nat.add_zero] at hPrefix
            exact False.elim (hPrefix context.parentColumn_lt_lastIndex)
        | succ copy =>
            by_cases hLow : row < context.maximalRow
            · exact relative_blockerAt_copied_root_below hI hBlocker context hCopy hLow
            · by_cases hEqual : row = context.maximalRow
              · subst row
                exact relative_blockerAt_copied_root_at context hBlocker hCopy
              · have hAbove := relative_blockerAt_copied_above hBlocker context hCopy
                  context.parentColumn_lt_lastIndex (by omega : context.maximalRow < row)
                rw [copyColumn_bad context (copy + 1) (Nat.le_refl _), Nat.sub_self] at hAbove
                exact hAbove
      · rw [← copyColumn_local context copy localColumn]
        have hNonroot : context.parentColumn + localColumn ≠ context.parentColumn := by omega
        by_cases hLow : row < context.maximalRow
        · cases hOldP : parent row array.raw (context.parentColumn + localColumn) with
          | none =>
              intro q p _ hP _
              rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP] at hP
              contradiction
          | some oldP =>
              by_cases hGood : oldP < context.parentColumn
              · exact relative_blockerAt_copied_parent_good hBlocker context hCopy hSource
                  hNonroot hLow hOldP hGood
              · exact relative_blockerAt_copied_parent_bad hI hBlocker context hCopy hSource hOldP (by omega)
        · exact relative_blockerAt_copied_nonroot_high hBlocker context hCopy hSource hNonroot (by omega)
  exact hAt q p hQ hP hDistinct

theorem aboveS_expand_of_context {array : ValidArray} (hI : DepthRegular array.raw)
    (context : ExpansionContext array) (base index : Nat) (hS : AboveS array.raw base) :
    AboveS (array.expand index).raw base := by
  intro row hRow
  exact relative_blockerCondition_expand_of_context hI context index row (hS row hRow)

theorem relative_structural_expand_of_context {array : ValidArray}
    (context : ExpansionContext array) (base index : Nat)
    (h : DepthRegular array.raw ∧ AboveS array.raw base) :
    DepthRegular (array.expand index).raw ∧ AboveS (array.expand index).raw base :=
  ⟨depthRegular_expand h.1 index, aboveS_expand_of_context h.1 context base index h.2⟩

theorem relative_decodeTower_parent_of_upper (array : ValidArray) (row fuel : Nat)
    (hBlocker : RowS array.raw row)
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
                    hBlocker column q p hColumn hQ hp hEqual
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

theorem relative_decodeTower_reconstruct (array : ValidArray) (base : Nat)
    (hI : DepthRegular array.raw) (hBlocker : AboveS array.raw base)
    (row fuel : Nat) (hBase : base ≤ row) (hHeight : trimHeight array.raw ≤ row + fuel) :
    layerParent ⟨decodeTower array.raw row fuel, previousParent array.raw row⟩ =
        parent row array.raw ∧
      ∀ column, column < array.raw.length →
        ColumnEq (columnSuffix array.raw column row)
          (mountainColumn ⟨decodeTower array.raw row fuel, previousParent array.raw row⟩ column) :=
  by
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
      obtain ⟨_, hUpper⟩ := ih (row + 1) (by omega) (by omega)
      have hParent := relative_decodeTower_parent_of_upper array row fuel (hBlocker row hBase)
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
          exact depthRegular_eq_parentDepth hI row column hColumn
      | succ index =>
          rw [layerAfter, hNext]
          have hUpperEntry := hUpper column hColumn index
          rw [columnEntry_suffix, mountainColumn_entry_depth
            (decodeTower_rootInvariant array.raw (row + 1) fuel).positive
            (by simpa [decodeTower_length] using hColumn)] at hUpperEntry
          simpa only [Nat.add_assoc, Nat.add_comm 1] using hUpperEntry

theorem rowS_trimZeroRows {array : Matrix} {row : Nat} (hBlocker : RowS array row) :
    RowS (trimZeroRows array) row := by
  intro column q p hColumn hPrevious hParent hNe
  rw [length_trimZeroRows] at hColumn
  rw [previousParent_trimZeroRows] at hPrevious
  rw [bms_parent_trimZeroRows] at hParent
  rcases hBlocker column q p hColumn hPrevious hParent hNe with ⟨z, hChain, hZ, hLe⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [bms_isAncestor_trimZeroRows] using hChain
  · simpa only [bms_parent_trimZeroRows] using hZ
  · exact ColumnLe.of_le_of_eq
      (ColumnLe.of_eq_of_le (columnSuffix_trimZeroRows array column (row + 1)) hLe)
      (ColumnEq.symm (columnSuffix_trimZeroRows array z (row + 1)))

theorem rowS_take {array : Matrix} {row : Nat} (hBlocker : RowS array row) (count : Nat) :
    RowS (array.take count) row := by
  intro column q p hColumn hPrevious hParent hNe
  have hBound : column < array.length ∧ column < count := by
    rw [List.length_take] at hColumn
    omega
  rw [previousParent_take hColumn] at hPrevious
  rw [bms_parent_take hColumn] at hParent
  rcases hBlocker column q p hBound.1 hPrevious hParent hNe with ⟨z, hChain, hZ, hLe⟩
  have hQ : q < column := previousParent_some_lt hPrevious
  have hZColumn : z < column := by
    rcases hChain with rfl | hAncestor
    · exact hQ
    · exact Nat.lt_trans (isAncestor_lt hAncestor) hQ
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa only [bms_isAncestor_take (by omega : q < (array.take count).length)] using hChain
  · simpa only [bms_parent_take (by omega : z < (array.take count).length)] using hZ
  · simpa only [columnSuffix, List.getElem?_take_of_lt hBound.2,
      List.getElem?_take_of_lt (by omega : z < count)] using hLe

/-- The framing rows require I only; S is preserved at every supported row. -/
theorem relative_structural_expand {array : ValidArray} (base index : Nat)
    (h : DepthRegular array.raw ∧ AboveS array.raw base) :
    DepthRegular (array.expand index).raw ∧ AboveS (array.expand index).raw base := by
  refine ⟨depthRegular_expand h.1 index, ?_⟩
  cases hMaximal : maximalParentRow array.raw with
  | none =>
      have hEqual : array.expand index = array.expand 0 := by
        apply ValidArray.ext
        simp [ValidArray.raw_expand, YesMetaZFC.BMS.expand, expandRaw, hMaximal]
      rw [hEqual, array.raw_expand_zero]
      intro row hRow
      exact rowS_trimZeroRows (rowS_take (h.2 row hRow) _)
  | some maximalRow =>
      let context := Classical.choice (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
      exact aboveS_expand_of_context h.1 context base index h.2

/-- Above the fixed boundary, decoding is compatible with the transported
candidate forest. This includes arbitrary finite active rows above the boundary. -/
theorem candidate_transport_and_decode {array : ValidArray}
    (context : ExpansionContext array) (frameRow index fuel : Nat)
    (hCut : frameRow + 1 ≤ context.maximalRow)
    (h : DepthRegular array.raw ∧ AboveS array.raw (frameRow + 1))
    (hFuel : trimHeight (array.expand index).raw ≤ frameRow + 1 + fuel) :
    (∀ column, column < (array.expand index).raw.length →
      previousParent (array.expand index).raw (frameRow + 1) column =
        copiedMountainParent (previousParent array.raw (frameRow + 1))
          context.parentColumn context.lastIndex column) ∧
      layerParent ⟨decodeTower (array.expand index).raw (frameRow + 1) fuel,
        previousParent (array.expand index).raw (frameRow + 1)⟩ =
          parent (frameRow + 1) (array.expand index).raw := by
  refine ⟨?_, ?_⟩
  · intro column hColumn
    exact parent_expand_eq_copiedMountainParent context (by omega) hColumn
  · have hNew := relative_structural_expand (frameRow + 1) index h
    exact (relative_decodeTower_reconstruct (array.expand index) (frameRow + 1)
      hNew.1 hNew.2 (frameRow + 1) fuel (Nat.le_refl _) hFuel).1

/-- A single fixed row boundary is carried through every expansion. -/
def FramedState (base : Nat) : Type :=
  { array : ValidArray // DepthRegular array.raw ∧ AboveS array.raw base }

def expandFramed {base : Nat} (state : FramedState base) (index : Nat) : FramedState base :=
  ⟨state.val.expand index, relative_structural_expand base index state.property⟩

def FramedStep {base : Nat} (smaller larger : FramedState base) : Prop :=
  (∃ index, expandFramed larger index = smaller) ∧ smaller.val ≠ larger.val

/-- Persistent candidate frames inherit BM4 well-foundedness. The BM4 theorem
is an explicit input; this theorem adds no new model or well-foundedness axiom. -/
theorem framedStep_wellFounded (base : Nat)
    (hBMS : WellFounded YesMetaZFC.BMS.Step) :
    WellFounded (FramedStep (base := base)) := by
  apply ZeroY.wellFounded_of_relation_map (fun state : FramedState base => state.val)
    (target := YesMetaZFC.BMS.Step) ?_ hBMS
  intro smaller larger hStep
  obtain ⟨⟨index, hEqual⟩, hNe⟩ := hStep
  refine ⟨⟨index, ?_⟩, hNe⟩
  exact (congrArg (fun state : FramedState base => state.val) hEqual).symm

end OneY.RelativeBlocker

#print axioms OneY.RelativeBlocker.relative_blockerCondition_expand_of_context
#print axioms OneY.RelativeBlocker.relative_structural_expand_of_context
#print axioms OneY.RelativeBlocker.relative_decodeTower_reconstruct
#print axioms OneY.RelativeBlocker.relative_structural_expand
#print axioms OneY.RelativeBlocker.candidate_transport_and_decode
#print axioms OneY.RelativeBlocker.framedStep_wellFounded
