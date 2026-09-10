import ZeroY.Decode
import ZeroY.Mountain.Termination

/-!
# 差分与逐列求和互逆

先证明一般左向父图上的求和递推唯一性。根的原值为 1 时，山脉的
`nextLayer` 差分满足这个递推，因而逐列求和精确恢复原行。
-/

namespace ZeroY

/-- 向一行追加一项时，求和只追加依据已有前缀计算的新值。 -/
theorem sumRow_append_singleton (parent : ParentMap) (upper : Sequence) (value : Nat) :
    sumRow parent (upper ++ [value]) =
      sumRow parent upper ++ [match parent (sumRow parent upper).length with
        | none => value
        | some column => value + (sumRow parent upper)[column]?.getD 0] := by
  simp only [sumRow, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-- 满足逐列求和递推的原行由上行和左向父图唯一确定。 -/
theorem sumRow_eq_of_recurrence (parent : ParentMap) (upper original : Sequence)
    (hLength : upper.length = original.length)
    (hLeft : ∀ {column found}, parent column = some found → found < column)
    (hStep : ∀ column, column < original.length →
      original[column]?.getD 0 =
        match parent column with
        | none => upper[column]?.getD 0
        | some found => upper[column]?.getD 0 + original[found]?.getD 0) :
    sumRow parent upper = original := by
  have hPrefix : ∀ count, count ≤ original.length →
      sumRow parent (upper.take count) = original.take count := by
    intro count
    induction count with
    | zero => simp [sumRow]
    | succ count ih =>
        intro hCount
        have hOriginal : count < original.length := by omega
        have hUpper : count < upper.length := by omega
        rw [List.take_succ_eq_append_getElem hUpper, sumRow_append_singleton,
          ih (by omega), List.take_succ_eq_append_getElem hOriginal]
        have hTakeLength : (original.take count).length = count := by
          simp [List.length_take, Nat.min_eq_left (by omega : count ≤ original.length)]
        rw [hTakeLength]
        congr 2
        have hEquation := hStep count hOriginal
        cases hParent : parent count with
        | none => simpa [hParent, List.getElem?_eq_getElem hUpper,
            List.getElem?_eq_getElem hOriginal] using hEquation.symm
        | some found =>
            have hFound : found < count := hLeft hParent
            have hFoundOriginal : found < original.length := by omega
            have hFoundTake : found < (original.take count).length := by
              rw [hTakeLength]
              exact hFound
            simpa [hParent, List.getElem?_eq_getElem hUpper,
              List.getElem?_eq_getElem hOriginal, List.getElem?_eq_getElem hFoundOriginal,
              List.getElem?_eq_getElem hFoundTake] using hEquation.symm
  have hFinal := hPrefix original.length (Nat.le_refl _)
  rw [← hLength, List.take_length] at hFinal
  simpa [hLength] using hFinal

/-- 逐项写出山脉差分，不依赖标准式或任何森林不变量。 -/
theorem nextLayer_getD {layer : Layer} {column : Nat}
    (hColumn : column < layer.values.length) :
    (nextLayer layer).values[column]?.getD 0 =
      match layerParent layer column with
      | none => 1
      | some found => layer.values[column]?.getD 0 - layer.values[found]?.getD 0 := by
  simp only [nextLayer, List.getElem?_mapIdx, List.getElem?_eq_getElem hColumn,
    Option.map_some, Option.getD_some]
  rfl

/-- 根的原值为 1 时，求和完整恢复作差前的一行。 -/
theorem sumRow_nextLayer {layer : Layer}
    (hRoots : ∀ column, column < layer.values.length →
      layerParent layer column = none → layer.values[column]?.getD 0 = 1) :
    sumRow (layerParent layer) (nextLayer layer).values = layer.values := by
  apply sumRow_eq_of_recurrence _ _ _ (nextLayer_length layer)
    (fun hParent => layerParent_some_lt hParent)
  intro column hColumn
  rw [nextLayer_getD hColumn]
  cases hParent : layerParent layer column with
  | none => exact hRoots column hColumn hParent
  | some found =>
      have hLess := layerParent_some_value_lt hParent
      simp only at *
      omega

end ZeroY
