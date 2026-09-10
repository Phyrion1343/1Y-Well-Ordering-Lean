import ZeroY.Mountain
import YesMetaZFC.BMS.Expansion

/-!
# 与上游规范矩阵载体相接的编码

先用山脉算法生成列，再删除共同尾零行。这只固定矩阵表示，不以可逆性或
标准生成性作为定义前提。编码和解码的全称往返定理仍须另证。
-/

namespace ZeroY

theorem encodeRaw_rectangular (values : Sequence) :
    YesMetaZFC.BMS.rectangular (encodeRaw values) = true := by
  apply YesMetaZFC.BMS.rectangular_iff_exists_uniformHeight.mpr
  refine ⟨(mountainRows (maxValue values) ⟨values, linearParent⟩).length, ?_⟩
  intro column hColumn
  rcases List.mem_map.mp hColumn with ⟨index, _, rfl⟩
  simp

/-- 合法 0-Y 表达式到规范矩阵的总编码。 -/
def encode (s : Expr) : YesMetaZFC.BMS.ValidArray where
  raw := YesMetaZFC.BMS.trimZeroRows (encodeRaw s.values)
  rectangular_eq := YesMetaZFC.BMS.rectangular_trimZeroRows (encodeRaw_rectangular s.values)
  trimmed_eq := YesMetaZFC.BMS.trimZeroRows_idempotent _

@[simp]
theorem encode_raw (s : Expr) :
    (encode s).raw = YesMetaZFC.BMS.trimZeroRows (encodeRaw s.values) := rfl

theorem encode_length (s : Expr) : (encode s).raw.length = s.values.length := by
  simp [encode, encodeRaw_length]

/-- 全 1 输入产生零行矩阵，每一个列位置都保留。 -/
theorem encodeRaw_nil_columns_of_all_ones (values : Sequence)
    (hOnes : values.all (fun value => value == 1) = true) :
    encodeRaw values = List.replicate values.length [] := by
  have hRows : mountainRows (maxValue values) ⟨values, linearParent⟩ = [] := by
    cases maxValue values <;> simp [mountainRows, hOnes]
  simp [encodeRaw, hRows, List.map_const']

theorem encodeRaw_replicate_one (count : Nat) :
    encodeRaw (List.replicate count 1) = List.replicate count [] := by
  simpa using encodeRaw_nil_columns_of_all_ones (List.replicate count 1) (by simp)

end ZeroY
