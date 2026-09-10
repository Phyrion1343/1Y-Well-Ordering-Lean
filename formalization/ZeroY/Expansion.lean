import ZeroY.Mountain.Roots
import ZeroY.Decode

/-!
# 0-Y 标准模式的独立展开算法

定义直接对应用户 HTML 的完整坏部模式：最高活动行复制坏部，较低行按复制的
父图逐层求和。这里不调用 BMS 展开，也不通过编码与解码复合来定义展开。
新块首列的低行父项来自原末列；最高活动行不使用复制父项作求和。
-/

namespace ZeroY

def mountainLayer (s : Sequence) (row : Nat) : Layer :=
  layerAfter row ⟨s, linearParent⟩

def mountainParent (s : Sequence) (row : Nat) : ParentMap :=
  layerParent (mountainLayer s row)

/-- 最高一个末列仍有父项的行及该父项位置。 -/
def expansionSite (s : Sequence) : Option (Nat × Nat) :=
  (YesMetaZFC.BMS.greatestBelow? (maxValue s) (fun row =>
    (mountainParent s row (s.length - 1)).isSome)).bind fun row =>
      (mountainParent s row (s.length - 1)).map fun root => (row, root)

/-- 原前缀包含第零坏块，随后追加 n 个完整坏块。 -/
def copyMountainRow (values : Sequence) (root last count : Nat) : Sequence :=
  values.take last ++ (List.range count).flatMap (fun _ =>
    (values.drop root).take (last - root))

/-- 原末列的父项覆盖后续每一块的首列，这是 HTML 循环的边界写入规则。 -/
def copiedMountainParent (parent : ParentMap) (root last target : Nat) : Option Nat :=
  if target < last then parent target
  else
    let blockLength := last - root
    let copy := (target - root) / blockLength
    let source := root + (target - root) % blockLength
    if source = root then
      (parent last).map fun p => if p < root then p else p + (copy - 1) * blockLength
    else
      (parent source).map fun p => if p < root then p else p + copy * blockLength

/-- 全部有限序列上的总计算函数；合法性定理用于封装实际表达式。 -/
def expandYRaw (s : Sequence) (count : Nat) : Sequence :=
  match expansionSite s with
  | none => s.take (s.length - 1)
  | some (row, root) =>
      (List.range row).foldr (fun lower upper =>
        sumRow (copiedMountainParent (mountainParent s lower) root (s.length - 1)) upper)
        (copyMountainRow (mountainLayer s row).values root (s.length - 1) count)

theorem expansionSite_parent {s : Sequence} {row root : Nat}
    (hSite : expansionSite s = some (row, root)) :
    mountainParent s row (s.length - 1) = some root := by
  unfold expansionSite at hSite
  cases hRow : YesMetaZFC.BMS.greatestBelow? (maxValue s) (fun r =>
      (mountainParent s r (s.length - 1)).isSome) with
  | none => simp [hRow] at hSite
  | some found =>
      cases hParent : mountainParent s found (s.length - 1) with
      | none => simp [hRow, hParent] at hSite
      | some p =>
          simp only [hRow, Option.bind_some, hParent, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at hSite
          rcases hSite with ⟨rfl, rfl⟩
          exact hParent

theorem expansionSite_root_lt {s : Sequence} {row root : Nat}
    (hSite : expansionSite s = some (row, root)) : root < s.length - 1 :=
  layerParent_some_lt (expansionSite_parent hSite)

theorem mountainParent_zero (s : Sequence) (row : Nat) : mountainParent s row 0 = none := by
  cases hParent : mountainParent s row 0 with
  | none => rfl
  | some p => have := layerParent_some_lt hParent; omega

theorem copiedMountainParent_zero (parent : ParentMap) (root last : Nat)
    (hLast : 0 < last) (hParent : parent 0 = none) :
    copiedMountainParent parent root last 0 = none := by
  simp [copiedMountainParent, hLast, hParent]

theorem legal_take {s : Sequence} (hLegal : Legal s) (count : Nat) : Legal (s.take count) := by
  refine ⟨fun value hMem => hLegal.1 value (List.mem_of_mem_take hMem), ?_⟩
  cases count with
  | zero => exact Or.inl rfl
  | succ count =>
      rcases hLegal.2 with hEmpty | hHead
      · simp [hEmpty]
      · cases s with
        | nil => exact Or.inl rfl
        | cons first rest => exact Or.inr hHead

theorem rootInvariant_legal {layer : Layer} (hInv : layer.RootInvariant) :
    Legal layer.values := by
  refine ⟨hInv.positive, ?_⟩
  by_cases hEmpty : layer.values = []
  · exact Or.inl hEmpty
  · have hLength : 0 < layer.values.length := List.length_pos_iff.mpr hEmpty
    have hParent : layer.previous 0 = none := by
      cases hP : layer.previous 0 with
      | none => rfl
      | some p => have := hInv.leftward hP; omega
    have hOne := hInv.rootsOne 0 hLength hParent
    apply Or.inr
    cases hValues : layer.values with
    | nil => exact False.elim (hEmpty hValues)
    | cons first rest => simpa [hValues] using hOne

theorem mountainLayer_legal {s : Sequence} (hLegal : Legal s) (row : Nat) :
    Legal (mountainLayer s row).values :=
  rootInvariant_legal (legal_layerAfter_rootInvariant hLegal row)

theorem copyMountainRow_positive {values : Sequence}
    (hPositive : ∀ value ∈ values, 0 < value) (root last count : Nat) :
    ∀ value ∈ copyMountainRow values root last count, 0 < value := by
  intro value hMem
  rcases List.mem_append.mp hMem with hMem | hMem
  · exact hPositive value (List.mem_of_mem_take hMem)
  · rcases List.mem_flatMap.mp hMem with ⟨_, _, hMem⟩
    exact hPositive value (List.mem_of_mem_drop (List.mem_of_mem_take hMem))

theorem copyMountainRow_legal {values : Sequence} (hLegal : Legal values)
    (root last count : Nat) (hLast : 0 < last) :
    Legal (copyMountainRow values root last count) := by
  refine ⟨copyMountainRow_positive hLegal.1 root last count, ?_⟩
  rcases hLegal.2 with hEmpty | hHead
  · subst values
    left
    simp [copyMountainRow]
  · right
    cases last with
    | zero => omega
    | succ last =>
        cases values with
        | nil => simp at hHead
        | cons first rest => exact hHead

private theorem expandedFold_legal (s : Sequence) (root last : Nat) (hLast : 0 < last)
    (rows : List Nat) (upper : Sequence) (hUpper : Legal upper) :
    Legal (rows.foldr (fun row next =>
      sumRow (copiedMountainParent (mountainParent s row) root last) next) upper) := by
  induction rows with
  | nil => exact hUpper
  | cons row rest ih =>
      exact sumRow_legal _ _
        (copiedMountainParent_zero _ _ _ hLast (mountainParent_zero s row)) ih

theorem expandYRaw_legal {s : Sequence} (hLegal : Legal s) (count : Nat) :
    Legal (expandYRaw s count) := by
  unfold expandYRaw
  cases hSite : expansionSite s with
  | none => exact legal_take hLegal _
  | some pair =>
      rcases pair with ⟨row, root⟩
      have hLast : 0 < s.length - 1 := by have := expansionSite_root_lt hSite; omega
      exact expandedFold_legal s root _ hLast _ _
        (copyMountainRow_legal (mountainLayer_legal hLegal row) root _ count hLast)

/-- 合法 0-Y 表达式上的标准模式展开。 -/
def expandY (s : Expr) (count : Nat) : Expr :=
  ⟨expandYRaw s.values count, expandYRaw_legal s.legal count⟩

@[simp]
theorem expandY_values (s : Expr) (count : Nat) :
    (expandY s count).values = expandYRaw s.values count := rfl

end ZeroY
