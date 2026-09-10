import ZeroY.Mountain
import YesMetaZFC.BMS.Array

/-!
# 求和解码的全域合法性

本文件只使用首列没有父项与自然数加法，不要求矩阵可逆、标准或矩形。
因此先给出原始矩阵到合法表达式的 `decodeExpr`，再提供规范矩阵接口 `decode`。
-/

namespace ZeroY

private def sumStep (parent : ParentMap) (acc : Sequence) (value : Nat) : Sequence :=
  acc ++ [match parent acc.length with
    | none => value
    | some column => value + acc[column]?.getD 0]

private theorem sumStep_length (parent : ParentMap) (acc : Sequence) (value : Nat) :
    (sumStep parent acc value).length = acc.length + 1 := by
  simp [sumStep]

private theorem sumFold_length (parent : ParentMap) (upper acc : Sequence) :
    (upper.foldl (sumStep parent) acc).length = acc.length + upper.length := by
  induction upper generalizing acc with
  | nil => simp
  | cons value rest ih =>
      simp only [List.foldl_cons, ih, sumStep_length, List.length_cons]
      omega

/-- 每层求和保留输入的项数，包含空输入。 -/
theorem sumRow_length (parent : ParentMap) (upper : Sequence) :
    (sumRow parent upper).length = upper.length := by
  change (upper.foldl (sumStep parent) []).length = upper.length
  simpa using sumFold_length parent upper []

private theorem sumStep_positive (parent : ParentMap) (acc : Sequence) (value : Nat)
    (hAcc : ∀ x ∈ acc, 0 < x) (hValue : 0 < value) :
    ∀ x ∈ sumStep parent acc value, 0 < x := by
  intro x hMem
  simp only [sumStep, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hMem | hEqual
  · exact hAcc x hMem
  · subst x
    cases hParent : parent acc.length with
    | none => simpa only [hParent] using hValue
    | some column =>
        exact Nat.lt_of_lt_of_le hValue (Nat.le_add_right value _)

private theorem sumFold_positive (parent : ParentMap) (upper acc : Sequence)
    (hUpper : ∀ x ∈ upper, 0 < x) (hAcc : ∀ x ∈ acc, 0 < x) :
    ∀ x ∈ upper.foldl (sumStep parent) acc, 0 < x := by
  induction upper generalizing acc with
  | nil => exact hAcc
  | cons value rest ih =>
      exact ih _ (fun x hx => hUpper x (by simp [hx]))
        (sumStep_positive parent acc value hAcc (hUpper value (by simp)))

/-- 上层全为正数时，求和后的本层仍全为正数。 -/
theorem sumRow_positive (parent : ParentMap) (upper : Sequence)
    (hUpper : ∀ x ∈ upper, 0 < x) :
    ∀ x ∈ sumRow parent upper, 0 < x := by
  exact sumFold_positive parent upper [] hUpper (by simp)

private theorem sumFold_head (parent : ParentMap) (upper : Sequence)
    (first : Nat) (acc : Sequence) :
    (upper.foldl (sumStep parent) (first :: acc)).head? = some first := by
  induction upper generalizing acc with
  | nil => rfl
  | cons value rest ih =>
      simpa only [List.foldl_cons, sumStep, List.cons_append] using
        ih (acc ++ [match parent (first :: acc).length with
          | none => value
          | some column => value + (first :: acc)[column]?.getD 0])

/-- 首列无父项时，求和保留首项。 -/
theorem sumRow_head (parent : ParentMap) (upper : Sequence)
    (hParent : parent 0 = none) :
    (sumRow parent upper).head? = upper.head? := by
  cases upper with
  | nil => rfl
  | cons first rest =>
      change (rest.foldl (sumStep parent) (sumStep parent [] first)).head? = some first
      simpa only [sumStep, List.length_nil, hParent, List.nil_append] using
        sumFold_head parent rest first []

/-- 首列无父项时，一次求和保持 0-Y 合法性。 -/
theorem sumRow_legal (parent : ParentMap) (upper : Sequence)
    (hParent : parent 0 = none) (hUpper : Legal upper) :
    Legal (sumRow parent upper) := by
  refine ⟨sumRow_positive parent upper hUpper.1, ?_⟩
  rcases hUpper.2 with hEmpty | hFirst
  · subst upper
    exact Or.inl rfl
  · exact Or.inr ((sumRow_head parent upper hParent).trans hFirst)

/-- 任意原始矩阵的第零列都没有父项。 -/
theorem bms_parent_first (row : Nat) (array : YesMetaZFC.BMS.BMSArray) :
    YesMetaZFC.BMS.parent row array 0 = none := by
  cases row <;> simp [YesMetaZFC.BMS.parent, YesMetaZFC.BMS.greatestBelow?]

private theorem decodeFold_legal (array : YesMetaZFC.BMS.BMSArray)
    (rows : List Nat) (upper : Sequence) (hUpper : Legal upper) :
    Legal (rows.foldr (fun row values =>
      sumRow (YesMetaZFC.BMS.parent row array) values) upper) := by
  induction rows with
  | nil => exact hUpper
  | cons row rest ih => exact sumRow_legal _ _ (bms_parent_first row array) ih

/-- 任意多个 1（包含零个）都是合法表达式。 -/
theorem replicate_one_legal (count : Nat) : Legal (List.replicate count 1) := by
  constructor
  · intro value hMem
    have hValue : value = 1 := List.eq_of_mem_replicate hMem
    omega
  · cases count with
    | zero => exact Or.inl rfl
    | succ count => exact Or.inr rfl

/-- F 对全部原始矩阵均输出合法 0-Y 式子。 -/
theorem decodeRaw_legal (array : YesMetaZFC.BMS.BMSArray) : Legal (decodeRaw array) :=
  decodeFold_legal array _ _ (replicate_one_legal array.length)

private theorem decodeFold_length (array : YesMetaZFC.BMS.BMSArray)
    (rows : List Nat) (upper : Sequence) :
    (rows.foldr (fun row values =>
      sumRow (YesMetaZFC.BMS.parent row array) values) upper).length = upper.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simpa only [List.foldr_cons, sumRow_length] using ih

/-- 解码保留原始矩阵的全部列数。 -/
theorem decodeRaw_length (array : YesMetaZFC.BMS.BMSArray) :
    (decodeRaw array).length = array.length := by
  simpa only [decodeRaw, List.length_replicate] using
    decodeFold_length array (List.range (YesMetaZFC.BMS.trimHeight array))
      (List.replicate array.length 1)

/-- 零行矩阵的列数可以任意，并不被识别为空矩阵。 -/
theorem trimHeight_nil_columns (count : Nat) :
    YesMetaZFC.BMS.trimHeight (List.replicate count []) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change YesMetaZFC.BMS.trimHeight (List.replicate count []) = 0
      exact ih

/-- 任意个空列精确解码为相同个数的 1。 -/
theorem decodeRaw_nil_columns (count : Nat) :
    decodeRaw (List.replicate count []) = List.replicate count 1 := by
  simp only [decodeRaw, trimHeight_nil_columns, List.range_zero, List.foldr_nil,
    List.length_replicate]

/-- 原始矩阵的合法表达式解码；不附加可逆性或标准性前提。 -/
def decodeExpr (array : YesMetaZFC.BMS.BMSArray) : Expr :=
  ⟨decodeRaw array, decodeRaw_legal array⟩

/-- 与上游规范矩阵载体相接的解码接口。 -/
def decode (array : YesMetaZFC.BMS.ValidArray) : Expr := decodeExpr array.raw

@[simp]
theorem decodeExpr_values (array : YesMetaZFC.BMS.BMSArray) :
    (decodeExpr array).values = decodeRaw array := rfl

@[simp]
theorem decode_values (array : YesMetaZFC.BMS.ValidArray) :
    (decode array).values = decodeRaw array.raw := rfl

end ZeroY
