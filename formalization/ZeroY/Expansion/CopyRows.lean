import ZeroY.Expansion.Context
import ZeroY.Structural.ExpansionCoordinates
import ZeroY.Structural.ExpansionParentAlignment
import ZeroY.Structural.DecodeTower

/-!
# 最高活动行及以上的数值复制

展开后的高行父图沿每个副本复制原父图，因此逐列求和的值也逐副本复制。
证明先在任意有限解码塔上进行，不以重新编码或展开共轭定义实际算法。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem BMS.copyColumn_lt_length {array : ValidArray} (context : ExpansionContext array)
    {index copy source : Nat} (hCopy : copy ≤ index) (hSource : source < context.lastIndex) :
    BMS.copyColumn context copy source < (array.expand index).raw.length := by
  by_cases hGood : source < context.parentColumn
  · rw [BMS.copyColumn_good context copy hGood, context.length_expand]
    omega
  · rw [BMS.copyColumn_bad context copy (by omega)]
    exact context.copyPosition_lt_length hCopy (by
      simp only [ExpansionContext.blockLength]
      omega)

/-- 所有高行的有限解码塔逐副本保值；复制首列已使用原坏根的高行父项。 -/
theorem decodeTower_copyColumn_high {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) {copy row source : Nat} (hCopy : copy ≤ index)
    (hSource : source < context.lastIndex) (hRow : context.maximalRow ≤ row) (fuel : Nat) :
    (decodeTower (array.expand index).raw row fuel)[BMS.copyColumn context copy source]?.getD 0 =
      (decodeTower array.raw row fuel)[source]?.getD 0 := by
  induction fuel generalizing row source with
  | zero =>
      have hOriginal : source < array.raw.length := by rw [context.array_length]; omega
      simp only [decodeTower,
        List.getElem?_replicate_of_lt (BMS.copyColumn_lt_length context hCopy hSource),
        List.getElem?_replicate_of_lt hOriginal]
  | succ fuel ih =>
      induction source using Nat.strongRecOn with
      | ind source ihSource =>
          have hExpanded := BMS.copyColumn_lt_length context hCopy hSource
          have hOriginal : source < array.raw.length := by rw [context.array_length]; omega
          rw [decodeTower, sumRow_getD (parent := parent row (array.expand index).raw)
            (fun hp => parent_some_lt hp) (by simpa [decodeTower_length] using hExpanded)]
          rw [decodeTower, sumRow_getD (parent := parent row array.raw)
            (fun hp => parent_some_lt hp) (by simpa [decodeTower_length] using hOriginal)]
          rw [BMS.parent_copyColumn_high context hCopy hSource hRow]
          cases hp : parent row array.raw source with
          | none =>
              simp only [Option.map_none]
              exact ih hSource (by omega)
          | some p =>
              simp only [Option.map_some]
              have hpLt := parent_some_lt hp
              rw [ih hSource (by omega)]
              exact congrArg (fun n => (decodeTower array.raw (row + 1) fuel)[source]?.getD 0 + n)
                (ihSource p hpLt (by omega))

/-- 高于全部非零坐标时，任何列都无父项。 -/
theorem parent_none_of_trimHeight_le (array : Matrix) {row : Nat}
    (hRow : trimHeight array ≤ row) (column : Nat) : parent row array column = none := by
  cases hp : parent row array column with
  | none => rfl
  | some found =>
      obtain ⟨_, value, _, hEntry, hLess⟩ := parent_some_entry_lt hp
      have := row_lt_trimHeight_of_entry?_eq_some_of_ne_zero hEntry (by omega)
      omega

theorem decodeTower_eq_ones_of_height_le (array : Matrix) {row : Nat}
    (hRow : trimHeight array ≤ row) (fuel : Nat) :
    decodeTower array row fuel = List.replicate array.length 1 := by
  apply List.ext_getElem (by simp [decodeTower_length])
  intro column hL hR
  have hc : column < array.length := by simpa [decodeTower_length] using hL
  have hValue := decodeTower_getD_of_parent_none array row fuel hc
    (parent_none_of_trimHeight_le array hRow column)
  simpa [List.getElem?_eq_getElem hL] using hValue

/-- 一旦解码塔顶端超过矩阵高度，增加任意燃料不改变结果。 -/
theorem decodeTower_fuel_stable (array : Matrix) (row fuel extra : Nat)
    (hFuel : trimHeight array ≤ row + fuel) :
    decodeTower array row (fuel + extra) = decodeTower array row fuel := by
  induction fuel generalizing row with
  | zero =>
      rw [decodeTower_eq_ones_of_height_le array (by omega), decodeTower]
  | succ fuel ih =>
      simp only [Nat.succ_add, decodeTower]
      rw [ih (row + 1) (by omega)]

theorem decodeTower_eq_decodeRaw_of_fuel (array : Matrix) {fuel : Nat}
    (hFuel : trimHeight array ≤ fuel) : decodeTower array 0 fuel = decodeRaw array := by
  have hEq : fuel = trimHeight array + (fuel - trimHeight array) := by omega
  rw [hEq, decodeTower_fuel_stable array 0 (trimHeight array) _ (by omega),
    decodeTower_eq_decodeRaw]

theorem copyMountainRow_succ (values : Sequence) (root last count : Nat) :
    copyMountainRow values root last (count + 1) =
      copyMountainRow values root last count ++ (values.drop root).take (last - root) := by
  simp [copyMountainRow, List.range_succ, List.flatMap_append, List.append_assoc]

theorem copyMountainRow_length {values : Sequence} {root last : Nat}
    (hLast : last ≤ values.length) (hRoot : root ≤ last) (count : Nat) :
    (copyMountainRow values root last count).length = last + count * (last - root) := by
  induction count with
  | zero => simp [copyMountainRow, Nat.min_eq_left hLast]
  | succ count ih =>
      rw [copyMountainRow_succ, List.length_append, ih]
      simp only [List.length_take, List.length_drop]
      rw [Nat.min_eq_left (show last - root ≤ values.length - root by omega)]
      rw [Nat.succ_mul]
      omega

theorem copyMountainRow_getD_prefix {values : Sequence} {root last column : Nat}
    (hLast : last ≤ values.length) (hColumn : column < last) (count : Nat) :
    (copyMountainRow values root last count)[column]?.getD 0 = values[column]?.getD 0 := by
  have hTakeLength : (values.take last).length = last := by simp [Nat.min_eq_left hLast]
  simp [copyMountainRow, List.getElem?_append_left (by omega : column < (values.take last).length),
    hColumn]

/-- 任意坏块副本位置都取原坏块中相同位置的值。 -/
theorem copyMountainRow_getD_copy {values : Sequence} {root last count copy localColumn : Nat}
    (hLast : last ≤ values.length) (hRoot : root < last)
    (hCopy : copy ≤ count) (hLocal : localColumn < last - root) :
    (copyMountainRow values root last count)[root + copy * (last - root) + localColumn]?.getD 0 =
      values[root + localColumn]?.getD 0 := by
  induction count generalizing copy with
  | zero =>
      have hZero : copy = 0 := by omega
      subst copy
      simpa using copyMountainRow_getD_prefix (root := root) hLast
        (show root + localColumn < last by omega) 0
  | succ count ih =>
      by_cases hPrevious : copy ≤ count
      · have hMul := Nat.mul_le_mul_right (last - root) hPrevious
        have hPosition : root + copy * (last - root) + localColumn <
            (copyMountainRow values root last count).length := by
          rw [copyMountainRow_length hLast (by omega)]
          omega
        rw [copyMountainRow_succ, List.getElem?_append_left hPosition]
        exact ih hPrevious
      · have hEqual : copy = count + 1 := by omega
        subst copy
        have hPosition : (copyMountainRow values root last count).length ≤
            root + (count + 1) * (last - root) + localColumn := by
          rw [copyMountainRow_length hLast (by omega), Nat.succ_mul]
          omega
        rw [copyMountainRow_succ, List.getElem?_append_right hPosition,
          copyMountainRow_length hLast (by omega)]
        have hIndex : root + (count + 1) * (last - root) + localColumn -
            (last + count * (last - root)) = localColumn := by
          rw [Nat.succ_mul]
          omega
        rw [hIndex]
        simp [hLocal]

/-- 高行的整个解码行等于 HTML 定义的完整坏块复制。 -/
theorem decodeTower_row_high {array : ValidArray} (context : ExpansionContext array)
    (index : Nat) {row : Nat} (hRow : context.maximalRow ≤ row) (fuel : Nat) :
    decodeTower (array.expand index).raw row fuel =
      copyMountainRow (decodeTower array.raw row fuel)
        context.parentColumn context.lastIndex index := by
  have hRoot := context.parentColumn_lt_lastIndex
  have hLast : context.lastIndex ≤ (decodeTower array.raw row fuel).length := by
    rw [decodeTower_length, context.array_length]
    omega
  apply List.ext_getElem
    (by rw [decodeTower_length, copyMountainRow_length hLast (by omega), context.length_expand];
        simp only [ExpansionContext.blockLength, Nat.succ_mul]; omega)
  intro column hExpanded hCopied
  have hc : column < (array.expand index).raw.length := by simpa [decodeTower_length] using hExpanded
  have hValue : (decodeTower (array.expand index).raw row fuel)[column]?.getD 0 =
      (copyMountainRow (decodeTower array.raw row fuel)
        context.parentColumn context.lastIndex index)[column]?.getD 0 := by
    by_cases hGood : column < context.parentColumn
    · have hSource : column < context.lastIndex := by omega
      rw [copyMountainRow_getD_prefix hLast hSource]
      have h := decodeTower_copyColumn_high context index (Nat.zero_le index) hSource hRow fuel
      simpa [BMS.copyColumn, hGood] using h
    · obtain ⟨copy, localColumn, hCopy, hLocal, rfl⟩ :=
        context.exists_copyPosition_of_not_good hc (by omega)
      have hSource : context.parentColumn + localColumn < context.lastIndex := by
        simp only [ExpansionContext.blockLength] at hLocal
        omega
      have h := decodeTower_copyColumn_high context index hCopy hSource hRow fuel
      rw [BMS.copyColumn_local] at h
      rw [h]
      symm
      exact copyMountainRow_getD_copy hLast hRoot hCopy hLocal
  simpa only [List.getElem?_eq_getElem hExpanded, List.getElem?_eq_getElem hCopied,
    Option.getD_some] using hValue

theorem layerAfter_succ_next (steps : Nat) (layer : Layer) :
    layerAfter (steps + 1) layer = nextLayer (layerAfter steps layer) := by
  induction steps generalizing layer with
  | zero => rfl
  | succ steps ih => exact ih (nextLayer layer)

/-- 足够高的解码塔在编码矩阵上逐行恢复原始数值山脉。 -/
theorem decodeTower_encode_mountain (s : Expr) (row fuel : Nat)
    (hFuel : maxValue s.values ≤ row + fuel) :
    decodeTower (encode s).raw row fuel = (mountainLayer s.values row).values := by
  induction fuel generalizing row with
  | zero =>
      have hOnes := layerAfter_all_ones (layer := ⟨s.values, linearParent⟩) s.legal.1
        (show maxValue s.values ≤ row by omega)
      have hAll : ∀ value ∈ (mountainLayer s.values row).values, value = 1 := by
        simpa only [List.all_eq_true, beq_iff_eq, mountainLayer] using hOnes
      apply List.ext_getElem (by simp only [decodeTower, List.length_replicate, encode_length,
        mountainLayer, layerAfter_length])
      intro column hL hR
      simpa only [decodeTower, List.getElem_replicate] using (hAll _ (List.getElem_mem hR)).symm
  | succ fuel ih =>
      rw [decodeTower, ih (row + 1) (by omega), bms_parent_encode_mountain]
      change sumRow (layerParent (layerAfter row ⟨s.values, linearParent⟩))
        (layerAfter (row + 1) ⟨s.values, linearParent⟩).values = _
      rw [layerAfter_succ_next]
      exact rootInvariant_sumRow_nextLayer (legal_layerAfter_rootInvariant s.legal row)

/-- 从任意行把解码塔按较低行数分成 foldr 与高层塔。 -/
theorem decodeTower_split (array : Matrix) (row lower upper : Nat) :
    decodeTower array row (lower + upper) =
      (List.range lower).foldr (fun offset next => sumRow (parent (row + offset) array) next)
        (decodeTower array (row + lower) upper) := by
  induction lower generalizing row with
  | zero => simp only [Nat.zero_add, List.range_zero, List.foldr_nil, Nat.add_zero]
  | succ lower ih =>
      simp only [Nat.succ_add, decodeTower, ih, List.range_succ_eq_map,
        List.foldr_cons, List.foldr_map, Nat.add_zero, Nat.add_succ]

private def copiedSumStep (parent : ParentMap) (acc : Sequence) (value : Nat) : Sequence :=
  acc ++ [match parent acc.length with
    | none => value
    | some column => value + acc[column]?.getD 0]

private theorem sumFold_congr_parent {left right : ParentMap} {bound : Nat}
    (hParent : ∀ i, i < bound → left i = right i) (remaining acc : Sequence)
    (hBound : acc.length + remaining.length ≤ bound) :
    remaining.foldl (copiedSumStep left) acc = remaining.foldl (copiedSumStep right) acc := by
  induction remaining generalizing acc with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.foldl_cons, copiedSumStep]
      rw [hParent acc.length (by simpa only [List.length_cons] using
        (show acc.length < bound by simp only [List.length_cons] at hBound; omega))]
      apply ih
      simp only [List.length_append, List.length_cons, List.length_nil] at hBound ⊢
      omega

/-- 求和程序仅读取有效列范围内的父项，范围外图无需相同。 -/
theorem sumRow_congr_parent_below {left right : ParentMap} (upper : Sequence)
    (hParent : ∀ i, i < upper.length → left i = right i) :
    sumRow left upper = sumRow right upper := by
  exact sumFold_congr_parent hParent upper [] (by simp)

theorem sumRow_foldr_length (parents : Nat → ParentMap) (rows : List Nat) (upper : Sequence) :
    (rows.foldr (fun row next => sumRow (parents row) next) upper).length = upper.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simpa only [List.foldr_cons, sumRow_length] using ih

theorem sumRow_foldr_congr_parent {left right : Nat → ParentMap} (rows : List Nat)
    (upper : Sequence)
    (hParent : ∀ row ∈ rows, ∀ column, column < upper.length → left row column = right row column) :
    rows.foldr (fun row next => sumRow (left row) next) upper =
      rows.foldr (fun row next => sumRow (right row) next) upper := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.foldr_cons]
      rw [sumRow_congr_parent_below _ (fun column hc =>
        hParent row (List.mem_cons_self ..) column (by simpa only [sumRow_foldr_length] using hc))]
      rw [ih (fun r hr => hParent r (List.mem_cons_of_mem _ hr))]

/--
有活动行时，实际 BM4 展开矩阵的求和解码，正好是独立 HTML 规则的 0-Y 展开。
此处没有假设展开后的矩阵仍可逆；可逆保持与本等式共同给出编码共轭。
-/
theorem decodeRaw_expand_encode_of_context (s : Expr) (context : ExpansionContext (encode s))
    (count : Nat) : decodeRaw ((encode s).expand count).raw = expandYRaw s.values count := by
  let fuel := maxValue s.values + trimHeight ((encode s).expand count).raw
  have hFuelHeight : trimHeight ((encode s).expand count).raw ≤ context.maximalRow + fuel := by
    dsimp [fuel]
    omega
  have hFuelValue : maxValue s.values ≤ context.maximalRow + fuel := by
    dsimp [fuel]
    omega
  have hUpper : decodeTower ((encode s).expand count).raw context.maximalRow fuel =
      copyMountainRow (mountainLayer s.values context.maximalRow).values
        context.parentColumn context.lastIndex count := by
    rw [decodeTower_row_high context count (Nat.le_refl _) fuel,
      decodeTower_encode_mountain s context.maximalRow fuel hFuelValue]
  have hUpperLength : (copyMountainRow (mountainLayer s.values context.maximalRow).values
      context.parentColumn context.lastIndex count).length = ((encode s).expand count).raw.length := by
    rw [← hUpper, decodeTower_length]
  rw [← decodeTower_eq_decodeRaw_of_fuel _ hFuelHeight,
    decodeTower_split _ 0 context.maximalRow fuel]
  simp only [Nat.zero_add]
  rw [hUpper]
  unfold expandYRaw
  rw [expansionSite_of_context s context]
  simp only
  have hLast : s.values.length - 1 = context.lastIndex := by
    have hLength := context.array_length
    rw [encode_length] at hLength
    omega
  rw [hLast]
  apply sumRow_foldr_congr_parent
  intro row hRow column hColumn
  have hr : row < context.maximalRow := List.mem_range.mp hRow
  have hc : column < ((encode s).expand count).raw.length := by
    rwa [hUpperLength] at hColumn
  rw [BMS.parent_expand_eq_copiedMountainParent context hr hc,
    bms_parent_encode_mountain]

end ZeroY
