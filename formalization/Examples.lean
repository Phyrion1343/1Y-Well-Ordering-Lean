import ZeroY.Expansion.LastColumn
import ZeroY.Structural.Recognition

/-!
# 有限数学样例

这些有限实例最初由 HTML 实现比对选出；期望值完整列在本文件中，
检查时不读取外部文件，也不假定 HTML 程序正确。它们不代替库中已经
完成的全称证明。所有计算由 Lean 内核的 `decide` 检查。

空输入是数学定义的总化：HTML UI 不接受长度小于 2 的输入。复制次数输入框
标注 min=1，但原 ExpansionProcess 算法也正确实现指标 0 的删尾，因此单独检查。
-/

namespace ZeroY.Examples

def sourceExpansionCases : List (Sequence × Nat × Sequence) :=
  [([1], 0, []),
   ([1], 3, []),
   ([1, 1, 1], 0, [1, 1]),
   ([1, 1, 1], 3, [1, 1]),
   ([1, 2], 0, [1]),
   ([1, 2], 3, [1, 1, 1, 1]),
   ([1, 3], 2, [1, 2, 3]),
   ([1, 4], 3, [1, 3, 6, 10]),
   ([1, 4, 6, 4], 0, [1, 4, 6]),
   ([1, 4, 6, 4], 1, [1, 4, 6, 3, 7, 10]),
   ([1, 4, 6, 4], 3, [1, 4, 6, 3, 7, 10, 6, 11, 15, 10, 16, 21]),
   ([1, 3, 2, 3], 2, [1, 3, 2, 2, 2]),
   ([1, 2, 4, 3, 5], 2, [1, 2, 4, 3, 4, 5])]

/-- 逐个核验原 ExpansionProcess 普通模式的全部精选实例。 -/
theorem source_expansion_cases :
    sourceExpansionCases.all (fun sample =>
      expandYRaw sample.1 sample.2.1 == sample.2.2) = true := by
  decide

/-- 空式的数学总化，不能误称 HTML UI 本身支持该输入。 -/
theorem empty_extension : expandYRaw [] 0 = [] ∧ expandYRaw [] 3 = [] := by
  decide

/-- 原互转器的数值输出；全零行在 Lean 规范中删除但保留全部列数。 -/
theorem source_converter_cases :
    encodeRaw [1] = [[]] ∧
    encodeRaw [1, 1, 1] = [[], [], []] ∧
    decodeRaw [[], [], []] = [1, 1, 1] ∧
    encodeRaw [1, 2, 3] = [[0], [1], [2]] ∧
    encodeRaw [1, 4, 6, 4] = [[0, 0, 0], [1, 1, 1], [2, 1, 0], [1, 1, 1]] ∧
    decodeRaw [[0, 0, 0], [1, 1, 1], [2, 1, 0], [1, 1, 1]] = [1, 4, 6, 4] ∧
    encodeRaw [1, 3, 2, 3] = [[0, 0], [1, 1], [1, 0], [2, 0]] := by
  decide

def rejectedMatrix : YesMetaZFC.BMS.ValidArray where
  raw := [[0, 0], [1, 0], [1, 1]]
  rectangular_eq := by decide
  trimmed_eq := by decide

/-- 原来不可逆的矩阵仍被实际往返谓词拒绝，未被载体定义掩盖。 -/
theorem rejected_matrix_not_roundTrip : ¬ RoundTrip rejectedMatrix.raw := by
  unfold RoundTrip
  decide

/-- 同一原始结构判据也拒绝它；没有另换一个“编码像”定义作为结构条件。 -/
theorem rejected_matrix_not_structural : ¬ Structural rejectedMatrix.raw := by
  intro h
  exact rejected_matrix_not_roundTrip ((roundTrip_iff_structural rejectedMatrix).mpr h)

/-- 加入共同零行只改变表示，不改变数值解码。 -/
theorem common_zero_rows :
    decodeRaw [[0, 0, 0], [1, 0, 0], [2, 0, 0]] = [1, 2, 3] ∧
    RoundTrip [[0, 0, 0], [1, 0, 0], [2, 0, 0]] := by
  unfold RoundTrip
  decide

/-- 不满足首项为 1 的非空序列仍不属于本次全称定理的合法载体。 -/
theorem invalid_head : ¬ Legal [2] := by simp [Legal]

end ZeroY.Examples
