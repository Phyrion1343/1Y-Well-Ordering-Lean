import ZeroY.Expansion.CopyRows
import ZeroY.Expansion.Prefix
import ZeroY.Structural.Recognition
import ZeroY.Structural.Expansion

/-!
# 实际转换与两个独立展开算法的交换

`expandY` 使用山脉复制和求和，`ValidArray.expand` 使用 BM4 条目提升。
这里把此前独立证明的计算交换等式接到表达式与矩阵载体。
-/

namespace ZeroY

open YesMetaZFC.BMS

theorem decode_expand_encode (s : Expr) (count : Nat) :
    decode ((encode s).expand count) = expandY s count := by
  cases hMaximal : maximalParentRow (encode s).raw with
  | none =>
      rw [← encode_expandY_of_no_site s count ((expansionSite_none_iff s).mpr hMaximal)]
      exact decode_encode _
  | some row =>
      obtain ⟨context⟩ := exists_expansionContext_of_maximalParentRow_eq_some hMaximal
      apply Expr.ext
      exact decodeRaw_expand_encode_of_context s context count

theorem expandY_length (s : Expr) (count : Nat) :
    (expandY s count).values.length = ((encode s).expand count).raw.length := by
  rw [← decode_expand_encode]
  exact decodeRaw_length _

theorem expandY_zero (s : Expr) : expandY s 0 = s.take (s.values.length - 1) := by
  rw [← decode_expand_encode]
  have hMatrix : (encode s).expand 0 = matrixPrefix (encode s) (s.values.length - 1) := by
    apply ValidArray.ext
    rw [ValidArray.raw_expand_zero]
    simp only [matrixPrefix, encode_length]
  rw [hMatrix, ← encode_take, decode_encode]

/-- 全部合法式上的实际编码展开交换，不要求标准生成性。 -/
theorem encode_expandY (s : Expr) (count : Nat) :
    encode (expandY s count) = (encode s).expand count := by
  rw [← decode_expand_encode]
  exact encode_decode_of_structural _ (BMS.structural_expand (encode_structural s) count)

theorem roundTrip_expand {array : ValidArray} (hRoundTrip : RoundTrip array.raw) (count : Nat) :
    RoundTrip (array.expand count).raw :=
  roundTrip_of_structural _ (BMS.structural_expand (structural_of_roundTrip array hRoundTrip) count)

theorem decode_expand {array : ValidArray} (hRoundTrip : RoundTrip array.raw) (count : Nat) :
    decode (array.expand count) = expandY (decode array) count := by
  have hEncode : encode (decode array) = array :=
    encode_decode_of_structural array (structural_of_roundTrip array hRoundTrip)
  simpa only [hEncode] using decode_expand_encode (decode array) count

theorem expandY_lt (s : Expr) (count : Nat) (hNonempty : 0 < s.values.length) :
    ExprLt (expandY s count) s := by
  apply (encode_lt_iff _ _).mp
  rw [encode_expandY]
  exact BMS.expand_matrixLt _ count (by simpa only [encode_length] using hNonempty)

end ZeroY
