import ZeroY.Mountain

/-!
# 补零字典序与矩阵结构条件

列内比较按无限尾零解释；列与列之间仍采用有限序列字典序。
这与上游 `compareArray` 的有限列表嵌套比较不同。
本文件只固定定义，结构条件与往返可逆的充要性待后续证明。
-/

namespace ZeroY

abbrev Matrix := YesMetaZFC.BMS.BMSArray

def columnEntry (column : List Nat) (row : Nat) : Nat := column[row]?.getD 0

def matrixEntry (array : Matrix) (column row : Nat) : Nat :=
  columnEntry (array[column]?.getD []) row

def ColumnEq (a b : List Nat) : Prop :=
  ∀ row, columnEntry a row = columnEntry b row

def ColumnLt (a b : List Nat) : Prop :=
  ∃ row, (∀ earlier, earlier < row → columnEntry a earlier = columnEntry b earlier) ∧
    columnEntry a row < columnEntry b row

def ColumnLe (a b : List Nat) : Prop := ColumnEq a b ∨ ColumnLt a b

inductive MatrixLt : Matrix → Matrix → Prop where
  | nil (column : List Nat) (rest : Matrix) : MatrixLt [] (column :: rest)
  | head {a b : List Nat} {s t : Matrix} (h : ColumnLt a b) :
      MatrixLt (a :: s) (b :: t)
  | tail {a b : List Nat} {s t : Matrix} (hEq : ColumnEq a b) (h : MatrixLt s t) :
      MatrixLt (a :: s) (b :: t)

/-- 条件 I：矩阵条目恰是本行父链深度的递推值。 -/
def DepthRegular (array : Matrix) : Prop :=
  ∀ row column, column < array.length →
    match YesMetaZFC.BMS.parent row array column with
    | none => matrixEntry array column row = 0
    | some p => matrixEntry array column row = matrixEntry array p row + 1

/-- 条件 S 中的 q：第零行使用相邻前驱，其余行使用前行父项。 -/
def previousParent (array : Matrix) (row column : Nat) : Option Nat :=
  match row with
  | 0 => linearParent column
  | r + 1 => YesMetaZFC.BMS.parent r array column

def columnSuffix (array : Matrix) (column row : Nat) : List Nat :=
  (array[column]?.getD []).drop row

/--
条件 S：跳过 q 选择 p 时，q 的本行父链上紧接 p 的子项 z 阻止越过该阈值。
深度正规矩阵中这样的 z 唯一；存在性与唯一性要作为父链引理证明。
-/
def BlockerCondition (array : Matrix) : Prop :=
  ∀ row column q p,
    column < array.length →
    previousParent array row column = some q →
    YesMetaZFC.BMS.parent row array column = some p →
    p ≠ q →
    ∃ z,
      (z = q ∨ YesMetaZFC.BMS.isAncestor array row z q = true) ∧
      YesMetaZFC.BMS.parent row array z = some p ∧
      ColumnLe (columnSuffix array column (row + 1))
        (columnSuffix array z (row + 1))

def Structural (array : Matrix) : Prop := DepthRegular array ∧ BlockerCondition array

end ZeroY
