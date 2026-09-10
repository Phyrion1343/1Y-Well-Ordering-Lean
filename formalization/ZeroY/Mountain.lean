import ZeroY.Syntax
import YesMetaZFC.BMS.Reference

/-!
# 山脉与互转的可计算定义

父项搜索沿上一层完整祖先链进行，不模拟 HTML 的原地跳链优化。
`encodeRaw` 用输入最大值作为有限燃料；`Mountain.Termination` 证明该燃料
对所有合法输入充足。往返、保序和展开交换仍须分别证明。
-/

namespace ZeroY

private abbrev B := YesMetaZFC.BMS.BMSArray

/-- 不存在父项使用 none；不使用自然数截断来模拟 -1。 -/
abbrev ParentMap := Nat → Option Nat

/-- 第 -1 层的线性前驱森林。 -/
def linearParent : ParentMap
  | 0 => none
  | k + 1 => some k

structure Layer where
  values : Sequence
  previous : ParentMap

/-- 在前层严格祖先中，选取值严格较小的最右一项。 -/
def layerParent (layer : Layer) (column : Nat) : Option Nat :=
  if column < layer.values.length then
    YesMetaZFC.BMS.greatestBelow? column (fun candidate =>
      (YesMetaZFC.BMS.ancestorChain layer.previous column column).contains candidate &&
        layer.values[candidate]?.getD 0 < layer.values[column]?.getD 0)
  else none

/-- 本层沿父链的深度。对左向父图，column 步覆盖全部严格祖先。 -/
def parentDepth (parent : ParentMap) (column : Nat) : Nat :=
  (YesMetaZFC.BMS.ancestorChain parent column column).length

def depthRow (layer : Layer) : List Nat :=
  (List.range layer.values.length).map (parentDepth (layerParent layer))

/-- 父项不存在时下一层取 1，否则取与父项的差。 -/
def nextLayer (layer : Layer) : Layer where
  previous := layerParent layer
  values := layer.values.mapIdx fun column value =>
    match layerParent layer column with
    | none => 1
    | some parent => value - layer.values[parent]?.getD 0

def maxValue (s : Sequence) : Nat := s.foldl max 0

/-- 已到全 1 行时不记录额外的全零深度行。 -/
def mountainRows : Nat → Layer → List (List Nat)
  | 0, _ => []
  | fuel + 1, layer =>
      if layer.values.all (fun value => value == 1) then []
      else depthRow layer :: mountainRows fuel (nextLayer layer)

/-- D 的总函数版本；矩阵外层是列，保留零行矩阵的全部列数。 -/
def encodeRaw (s : Sequence) : B :=
  let rows := mountainRows (maxValue s) ⟨s, linearParent⟩
  (List.range s.length).map fun column =>
    rows.map fun row => row[column]?.getD 0

/-- 沿一行从左向右求和；acc 只含已经算好的本行值。 -/
def sumRow (parent : ParentMap) (upper : Sequence) : Sequence :=
  upper.foldl (fun acc value =>
    let next := match parent acc.length with
      | none => value
      | some column => value + acc[column]?.getD 0
    acc ++ [next]) []

/-- F 的总函数版本。共同尾零行不参与求和，矩形输入的父图复用上游定义。 -/
def decodeRaw (array : B) : Sequence :=
  (List.range (YesMetaZFC.BMS.trimHeight array)).foldr
    (fun row upper => sumRow (YesMetaZFC.BMS.parent row array) upper)
    (List.replicate array.length 1)

/-- 往返可逆按共同尾零行归一化理解；结构判据的等价性仍待证明。 -/
def RoundTrip (array : B) : Prop :=
  encodeRaw (decodeRaw array) = YesMetaZFC.BMS.trimZeroRows array

theorem encodeRaw_length (s : Sequence) : (encodeRaw s).length = s.length := by
  simp [encodeRaw]

theorem encodeRaw_empty : encodeRaw [] = [] := rfl

theorem decodeRaw_empty : decodeRaw [] = [] := rfl

/-- 用户指出的矩阵在 F 下丢失结构，给出一个具体否定实例。 -/
theorem nonreversible_matrix : ¬ RoundTrip [[0, 0], [1, 0], [1, 1]] := by
  unfold RoundTrip
  decide

theorem nonreversible_matrix_decode :
    decodeRaw [[0, 0], [1, 0], [1, 1]] = [1, 2, 3] := by
  decide

theorem nonreversible_matrix_reencode :
    encodeRaw [1, 2, 3] = [[0], [1], [2]] := by
  decide

end ZeroY
