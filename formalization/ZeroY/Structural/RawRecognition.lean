import ZeroY.Structural.Recognition

/-!
# 带共同尾零行的原始矩形矩阵识别

规范化不改变条目补零值、任何行父图或祖先关系，因此也不改变原始条件 I、S。
这将规范矩阵上的识别定理外延到任意矩形代表，而不改写可逆性的定义。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem depthRegular_trimZeroRows_iff (array : Matrix) :
    DepthRegular (trimZeroRows array) ↔ DepthRegular array := by
  constructor
  · intro h row column hColumn
    have hTrimmed := h row column (by simpa only [length_trimZeroRows] using hColumn)
    simpa only [bms_parent_trimZeroRows, matrixEntry_trimZeroRows] using hTrimmed
  · exact depthRegular_trimZeroRows

theorem blockerCondition_trimZeroRows_iff (array : Matrix) :
    BlockerCondition (trimZeroRows array) ↔ BlockerCondition array := by
  constructor
  · intro h row column q p hColumn hPrevious hParent hDistinct
    obtain ⟨z, hChain, hZParent, hOrder⟩ := h row column q p
      (by simpa only [length_trimZeroRows] using hColumn)
      (by simpa only [previousParent_trimZeroRows] using hPrevious)
      (by simpa only [bms_parent_trimZeroRows] using hParent) hDistinct
    refine ⟨z, ?_, ?_, ?_⟩
    · simpa only [bms_isAncestor_trimZeroRows] using hChain
    · simpa only [bms_parent_trimZeroRows] using hZParent
    · exact ColumnLe.of_eq_of_le (columnSuffix_trimZeroRows array column (row + 1)).symm
        (ColumnLe.of_le_of_eq hOrder (columnSuffix_trimZeroRows array z (row + 1)))
  · exact blockerCondition_trimZeroRows

/-- 删除或保留共同尾零行不改变原始 I 与 S。 -/
theorem structural_trimZeroRows_iff (array : Matrix) :
    Structural (trimZeroRows array) ↔ Structural array := by
  unfold Structural
  rw [depthRegular_trimZeroRows_iff, blockerCondition_trimZeroRows_iff]

/-- 原始往返条件本身也不区分共同尾零行代表。 -/
theorem roundTrip_trimZeroRows_iff (array : Matrix) :
    RoundTrip (trimZeroRows array) ↔ RoundTrip array := by
  simp only [RoundTrip, decodeRaw_trimZeroRows, trimZeroRows_idempotent]

/--
任意非负矩形矩阵可逆，当且仅当满足原始纯矩阵条件 I 与 S。
允许任意多共同尾零行，没有标准性或预先规范化的要求。
-/
theorem roundTrip_iff_structural_of_rectangular {array : Matrix}
    (hRectangular : rectangular array = true) : RoundTrip array ↔ Structural array := by
  let normalized : ValidArray := {
    raw := trimZeroRows array
    rectangular_eq := rectangular_trimZeroRows hRectangular
    trimmed_eq := trimZeroRows_idempotent array }
  calc
    RoundTrip array ↔ RoundTrip normalized.raw := (roundTrip_trimZeroRows_iff array).symm
    _ ↔ Structural normalized.raw := roundTrip_iff_structural normalized
    _ ↔ Structural array := structural_trimZeroRows_iff array

end ZeroY
