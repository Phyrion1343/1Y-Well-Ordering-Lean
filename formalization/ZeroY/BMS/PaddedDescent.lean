import ZeroY.PaddedOrder
import ZeroY.BMS.AnyArray
import ZeroY.Transport

/-!
# BM4 展开的补零字典序下降

所有坐标比较都采用无限尾零约定，允许展开后删除公共尾零行。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem matrixEntry_eq_entry_getD (array : Matrix) (column row : Nat) :
    matrixEntry array column row = (entry? array column row).getD 0 := by
  simp only [matrixEntry, columnEntry, entry?]
  cases array[column]? <;> simp

theorem matrixEntry_trimZeroRows (array : Matrix) (column row : Nat) :
    matrixEntry (trimZeroRows array) column row = matrixEntry array column row := by
  simp only [matrixEntry_eq_entry_getD]
  by_cases hRow : row < trimHeight array
  · rw [entry?_trimZeroRows_of_lt array column row hRow]
  · rw [entry?_trimZeroRows_eq_none_of_le array column row (by omega)]
    cases hEntry : entry? array column row with
    | none => rfl
    | some value =>
        have hZero : value = 0 := by
          apply Classical.byContradiction
          intro hNonzero
          exact hRow (row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry hNonzero)
        simp [hZero]

namespace MatrixLt

/-- 长度较短且全部已有列逐补零坐标相等时，是真前缀。 -/
theorem of_strict_prefix {a b : Matrix} (hLength : a.length < b.length)
    (hPrefix : ∀ column, column < a.length →
      ∀ row, matrixEntry a column row = matrixEntry b column row) : MatrixLt a b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp at hLength
      | cons column rest => exact .nil column rest
  | cons column rest ih =>
      cases b with
      | nil => simp at hLength
      | cons other tail =>
          apply MatrixLt.tail
          · intro row
            exact hPrefix 0 (by simp) row
          · apply ih (by simpa using hLength)
            intro index hIndex row
            exact hPrefix (index + 1) (by simpa using hIndex) row

/-- 首个不同列由首个不同条目决定。 -/
theorem of_first_difference {a b : Matrix} {column row : Nat}
    (hA : column < a.length) (hB : column < b.length)
    (hColumns : ∀ earlier, earlier < column → ∀ index,
      matrixEntry a earlier index = matrixEntry b earlier index)
    (hRows : ∀ earlier, earlier < row →
      matrixEntry a column earlier = matrixEntry b column earlier)
    (hLess : matrixEntry a column row < matrixEntry b column row) :
    MatrixLt a b := by
  induction column generalizing a b with
  | zero =>
      cases a with
      | nil => simp at hA
      | cons first rest =>
          cases b with
          | nil => simp at hB
          | cons other tail => exact .head ⟨row, hRows, hLess⟩
  | succ column ih =>
      cases a with
      | nil => simp at hA
      | cons first rest =>
          cases b with
          | nil => simp at hB
          | cons other tail =>
              apply MatrixLt.tail
              · intro index
                exact hColumns 0 (by omega) index
              · apply ih (by simpa using hA) (by simpa using hB)
                · intro earlier hEarlier index
                  exact hColumns (earlier + 1) (by omega) index
                · exact hRows
                · exact hLess

end MatrixLt

namespace BMS

private theorem first_copy_position {array : ValidArray}
    (context : ExpansionContext array) : context.copyPosition 1 0 = context.lastIndex := by
  simp only [ExpansionContext.copyPosition, ExpansionContext.copyStart,
    ExpansionContext.blockLength, Nat.one_mul, Nat.add_zero]
  have := context.parentColumn_lt_lastIndex
  omega

/-- 首个新增坏根在最大父行以下，逐坐标复制原末列。 -/
theorem first_copy_entry_below {array : ValidArray}
    (context : ExpansionContext array) {index row : Nat}
    (hIndex : 0 < index) (hRow : row < context.maximalRow) :
    entry? (expandRaw array.raw index) context.lastIndex row =
      entry? array.raw context.lastIndex row := by
  have hAncestor := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
  rcases ancestor_entries_lt hAncestor with
    ⟨firstValue, lastValue, hFirst, hLast, hLess⟩
  have hFirstBad : entry? context.badPart 0 row = some firstValue := by
    rw [context.entry?_badPart context.blockLength_pos]
    simpa using hFirst
  have hFirstAscending : ascending array.raw context.maximalRow
      context.parentColumn 0 row = true := by simp [ascending, hRow]
  rw [← first_copy_position context,
    context.entry?_expandRaw_copy (by omega) context.blockLength_pos]
  rw [ExpansionContext.entry?_copyBlock_first_of_ascending array.raw context.badPart
    context.maximalRow context.parentColumn 1 row firstValue lastValue
    (array.raw[context.lastIndex]?.getD []) hFirstBad hFirstAscending
    (ExpansionContext.getD_getElem?_of_entry?_eq_some array.raw hLast)]
  rw [first_copy_position context, hLast, Nat.one_mul,
    Nat.add_sub_of_le (Nat.le_of_lt hLess)]

/-- 首个新增坏根在最大父行的条目严格小于原末列。 -/
theorem first_copy_entry_at {array : ValidArray}
    (context : ExpansionContext array) {index : Nat} (hIndex : 0 < index) :
    matrixEntry (expandRaw array.raw index) context.lastIndex context.maximalRow <
      matrixEntry array.raw context.lastIndex context.maximalRow := by
  rcases parent_some_entry_lt context.parent_eq with
    ⟨firstValue, lastValue, hFirst, hLast, hLess⟩
  have hFirstBad : entry? context.badPart 0 context.maximalRow = some firstValue := by
    rw [context.entry?_badPart context.blockLength_pos]
    simpa using hFirst
  unfold entry? at hFirstBad
  cases hColumn : context.badPart[0]? with
  | none => simp [hColumn] at hFirstBad
  | some column =>
      have hValue : column[context.maximalRow]? = some firstValue := by
        simpa [hColumn] using hFirstBad
      have hCopied : entry? (expandRaw array.raw index) context.lastIndex
          context.maximalRow = some firstValue := by
        rw [← first_copy_position context,
          context.entry?_expandRaw_copy (by omega) context.blockLength_pos]
        exact ExpansionContext.entry?_copyBlock_of_not_ascending array.raw context.badPart
          context.maximalRow context.parentColumn 1 0 context.maximalRow firstValue
          (array.raw[context.lastIndex]?.getD []) column hColumn hValue
          (by simp [ascending])
      simpa only [matrixEntry_eq_entry_getD, hCopied, hLast, Option.getD_some]
        using hLess

theorem matrixLt_trimmed_take {array : Matrix} {count : Nat}
    (hCount : count < array.length) :
    MatrixLt (trimZeroRows (array.take count)) array := by
  apply MatrixLt.of_strict_prefix
  · simpa [length_trimZeroRows, List.length_take, Nat.min_eq_left (Nat.le_of_lt hCount)]
  · intro column hColumn row
    rw [length_trimZeroRows, List.length_take] at hColumn
    rw [matrixEntry_trimZeroRows]
    simp only [matrixEntry, List.getElem?_take_of_lt (Nat.lt_of_lt_of_le hColumn (Nat.min_le_left _ _))]

/-- 有坏根且复制次数为正时，首个差异发生于原末列的最大父行。 -/
theorem expand_matrixLt_of_context {array : ValidArray}
    (context : ExpansionContext array) {index : Nat} (hIndex : 0 < index) :
    MatrixLt (array.expand index).raw array.raw := by
  apply MatrixLt.of_first_difference (column := context.lastIndex)
    (row := context.maximalRow)
  · rw [← first_copy_position context]
    exact context.copyPosition_lt_length (by omega) context.blockLength_pos
  · rw [context.array_length]
    omega
  · intro earlier hEarlier row
    change matrixEntry (trimZeroRows (expandRaw array.raw index)) earlier row = _
    rw [matrixEntry_trimZeroRows, matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD,
      context.entry?_expandRaw_eq_of_lt_lastIndex index hEarlier]
  · intro row hRow
    change matrixEntry (trimZeroRows (expandRaw array.raw index)) context.lastIndex row = _
    rw [matrixEntry_trimZeroRows, matrixEntry_eq_entry_getD, matrixEntry_eq_entry_getD,
      first_copy_entry_below context hIndex hRow]
  · change matrixEntry (trimZeroRows (expandRaw array.raw index))
      context.lastIndex context.maximalRow < _
    rw [matrixEntry_trimZeroRows]
    exact first_copy_entry_at context hIndex

/-- 任意非空合法矩阵的一步展开在补零字典序下严格下降。 -/
theorem expand_matrixLt (array : ValidArray) (index : Nat)
    (hLength : 0 < array.raw.length) : MatrixLt (array.expand index).raw array.raw := by
  by_cases hIndex : index = 0
  · subst index
    rw [array.raw_expand_zero]
    exact matrixLt_trimmed_take (by omega)
  · cases hMaximal : maximalParentRow array.raw with
    | none =>
        have hRaw : (array.expand index).raw =
            trimZeroRows (array.raw.take (array.raw.length - 1)) := by
          rw [ValidArray.raw_expand]
          unfold YesMetaZFC.BMS.expand expandRaw
          cases hSize : array.raw.length with
          | zero => omega
          | succ lastIndex => simp [hMaximal]
        rw [hRaw]
        exact matrixLt_trimmed_take (by omega)
    | some maximalRow =>
        let context := Classical.choice
          (exists_expansionContext_of_maximalParentRow_eq_some hMaximal)
        exact expand_matrixLt_of_context context (by omega)

/-- 非退化展开的起点必有列。 -/
theorem length_pos_of_step {smaller larger : ValidArray} (hStep : Step smaller larger) :
    0 < larger.raw.length := by
  apply Nat.pos_of_ne_zero
  intro hZero
  rcases hStep.1 with ⟨index, rfl⟩
  apply hStep.2
  apply ValidArray.ext
  have hNil : larger.raw = [] := List.length_eq_zero_iff.mp hZero
  simp [ValidArray.raw_expand, YesMetaZFC.BMS.expand, expandRaw, hNil, trimZeroRows]

theorem matrixLt_of_step {smaller larger : ValidArray} (hStep : Step smaller larger) :
    MatrixLt smaller.raw larger.raw := by
  have hLength := length_pos_of_step hStep
  rcases hStep.1 with ⟨index, rfl⟩
  exact expand_matrixLt larger index hLength

theorem matrixLt_of_strictDescent {smaller larger : ValidArray}
    (hDescent : StrictDescent smaller larger) : MatrixLt smaller.raw larger.raw := by
  induction hDescent with
  | single hStep => exact matrixLt_of_step hStep
  | tail prior hStep ih => exact MatrixLt.trans (matrixLt_of_step hStep) ih

/-- 上游按路径方向定义的下降，与良基关系方向的传递闭包相同。 -/
theorem transGen_step_of_strictDescent {smaller larger : ValidArray}
    (hDescent : StrictDescent smaller larger) : Relation.TransGen Step smaller larger := by
  induction hDescent with
  | single hStep => exact .single hStep
  | tail prior hStep ih => exact Relation.TransGen.trans (.single hStep) ih

open YesMetaZFC.BMS.StabilityFrame

universe u

/-- 固定任意起点，比较两个后代时，补零字典序恰等于严格展开顺序。 -/
theorem descendants_matrixLt_iff {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) {root first second : ValidArray}
    (hFirst : ExpansionPath root first) (hSecond : ExpansionPath root second) :
    MatrixLt first.raw second.raw ↔ StrictDescent first second := by
  constructor
  · intro hLess
    rcases descendants_comparable_any system hFirst hSecond with hEqual | hForward | hReverse
    · subst first
      exact False.elim (MatrixLt.irrefl _ hLess)
    · exact hForward
    · exact False.elim (MatrixLt.asymm hLess (matrixLt_of_strictDescent hReverse))
  · exact matrixLt_of_strictDescent

/-- 从一个固定矩阵出发的全部有限展开结果，包含起点自身。 -/
abbrev Descendant (root : ValidArray) := {array : ValidArray // ExpansionPath root array}

def DescendantLt {root : ValidArray} (first second : Descendant root) : Prop :=
  MatrixLt first.1.raw second.1.raw

/-- 任意固定根的后代，在补零字典序下良序。 -/
theorem descendants_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (root : ValidArray) :
    StrictWellOrder (Descendant root) DescendantLt where
  wellFounded := wellFounded_of_relation_map (fun array : Descendant root => array.1)
    (fun {first second} hLess => transGen_step_of_strictDescent
      ((descendants_matrixLt_iff system first.2 second.2).mp hLess))
    (transGen_step_wellFounded_any system)
  transitive := fun hFirst hSecond => MatrixLt.trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases descendants_comparable_any system first.2 second.2 with hEqual | hForward | hReverse
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl (matrixLt_of_strictDescent hForward))
    · exact Or.inr (Or.inr (matrixLt_of_strictDescent hReverse))

def GeneratedMatrixLt (first second : GeneratedArray) : Prop :=
  MatrixLt first.1.raw second.1.raw

theorem matrixLt_of_generatedStrictDescent {first second : GeneratedArray}
    (hDescent : GeneratedStrictDescent first second) : GeneratedMatrixLt first second := by
  induction hDescent with
  | single hStep => exact matrixLt_of_step hStep
  | tail prior hStep ih => exact MatrixLt.trans ih (matrixLt_of_step hStep)

/-- 标准 BMS 上，已有的展开良序精确等于补零字典序。 -/
theorem generatedMatrixLt_iff {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (first second : GeneratedArray) :
    GeneratedMatrixLt first second ↔ GeneratedStrictDescent first second := by
  constructor
  · intro hLess
    rcases system.generated_comparable first second with hEqual | hForward | hReverse
    · subst first
      exact False.elim (MatrixLt.irrefl _ hLess)
    · exact hForward
    · exact False.elim
        (MatrixLt.asymm hLess (matrixLt_of_generatedStrictDescent hReverse))
  · exact matrixLt_of_generatedStrictDescent

theorem generatedMatrix_strictWellOrder {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    StrictWellOrder GeneratedArray GeneratedMatrixLt where
  wellFounded := wellFounded_of_relation_map (fun array : GeneratedArray => array)
    (fun {first second} hLess => (generatedMatrixLt_iff system first second).mp hLess)
    system.strictDescent_wellFoundedOn_generated
  transitive := fun hFirst hSecond => MatrixLt.trans hFirst hSecond
  trichotomy := by
    intro first second
    rcases system.generated_comparable first second with hEqual | hForward | hReverse
    · exact Or.inl hEqual
    · exact Or.inr (Or.inl (matrixLt_of_generatedStrictDescent hForward))
    · exact Or.inr (Or.inr (matrixLt_of_generatedStrictDescent hReverse))

end BMS
end ZeroY
