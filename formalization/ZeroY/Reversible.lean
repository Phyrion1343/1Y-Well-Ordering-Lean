import ZeroY.Image
import ZeroY.OrderEmbedding
import ZeroY.Transport

/-!
# 全部可逆规范矩阵与合法表达式的双射

可逆载体直接使用最初固定的 `RoundTrip` 谓词，而不是把编码像重新定义为
“可逆”。以下定理证明两种描述确实相等；双射不要求标准生成性。
-/

namespace ZeroY

open YesMetaZFC.BMS

/-- 全部满足往返等式的规范矩阵。 -/
abbrev ReversibleArray := { array : ValidArray // RoundTrip array.raw }

/-- 每个合法表达式的实际编码落在可逆规范矩阵中。 -/
def encodeReversible (s : Expr) : ReversibleArray := ⟨encode s, encode_roundTrip s⟩

/-- 逆映射使用原有求和解码程序。 -/
def decodeReversible (array : ReversibleArray) : Expr := decode array.val

@[simp]
theorem encodeReversible_val (s : Expr) : (encodeReversible s).val = encode s := rfl

@[simp]
theorem decodeReversible_values (array : ReversibleArray) :
    (decodeReversible array).values = decodeRaw array.val.raw := rfl

@[simp]
theorem decodeReversible_encodeReversible (s : Expr) :
    decodeReversible (encodeReversible s) = s := decode_encode s

/-- 在全部可逆规范矩阵上，编码实际解码的结果也恢复原矩阵。 -/
theorem encode_decode_of_roundTrip (array : ValidArray) (hRoundTrip : RoundTrip array.raw) :
    encode (decode array) = array := by
  apply ValidArray.ext
  rw [encode_raw_eq_encodeRaw]
  change encodeRaw (decodeRaw array.raw) = array.raw
  exact hRoundTrip.trans array.trimmed_eq

@[simp]
theorem encodeReversible_decodeReversible (array : ReversibleArray) :
    encodeReversible (decodeReversible array) = array := by
  apply Subtype.ext
  exact encode_decode_of_roundTrip array.val array.property

theorem encodeReversible_injective : Function.Injective encodeReversible :=
  Function.LeftInverse.injective decodeReversible_encodeReversible

theorem encodeReversible_surjective : Function.Surjective encodeReversible :=
  Function.RightInverse.surjective encodeReversible_decodeReversible

/-- 实际的编码和解码构成双射，无标准式前提。 -/
theorem encodeReversible_bijective :
    Function.Injective encodeReversible ∧ Function.Surjective encodeReversible :=
  ⟨encodeReversible_injective, encodeReversible_surjective⟩

theorem decodeReversible_injective : Function.Injective decodeReversible :=
  Function.LeftInverse.injective encodeReversible_decodeReversible

theorem decodeReversible_surjective : Function.Surjective decodeReversible :=
  Function.RightInverse.surjective decodeReversible_encodeReversible

/-- 规范矩阵满足原始往返条件，当且仅当它是某个合法表达式的实际编码。 -/
theorem roundTrip_iff_exists_encode (array : ValidArray) :
    RoundTrip array.raw ↔ ∃ s : Expr, encode s = array := by
  constructor
  · intro hRoundTrip
    exact ⟨decode array, encode_decode_of_roundTrip array hRoundTrip⟩
  · rintro ⟨s, rfl⟩
    exact encode_roundTrip s

/-- 不预设矩形的原始矩阵版本：可逆恰好是归一化正文属于合法编码像。 -/
theorem roundTrip_iff_exists_encodeRaw (array : Matrix) :
    RoundTrip array ↔ ∃ s : Sequence, Legal s ∧ encodeRaw s = trimZeroRows array := by
  constructor
  · intro hRoundTrip
    exact ⟨decodeRaw array, decodeRaw_legal array, hRoundTrip⟩
  · rintro ⟨s, hLegal, hEncode⟩
    have hDecode := congrArg decodeRaw hEncode
    rw [decodeRaw_encodeRaw hLegal, decodeRaw_trimZeroRows] at hDecode
    unfold RoundTrip
    rw [← hDecode]
    exact hEncode

/-- 可逆规范矩阵自动满足条件 I；不是额外限制载体的定义。 -/
theorem reversible_depthRegular (array : ReversibleArray) : DepthRegular array.val.raw := by
  have hEncode := encode_decode_of_roundTrip array.val array.property
  rw [← hEncode]
  exact encode_depthRegular _

/-- 可逆载体上的关系仍然是原始矩阵补零字典序。 -/
def ReversibleLt (left right : ReversibleArray) : Prop :=
  MatrixLt left.val.raw right.val.raw

/-- 全部合法式与全部可逆矩阵的实际序同构，不限于标准式。 -/
def reversibleOrderIso : StrictRelationIso Expr ReversibleArray ExprLt ReversibleLt where
  toFun := encodeReversible
  invFun := decodeReversible
  left_inv := decodeReversible_encodeReversible
  right_inv := encodeReversible_decodeReversible
  rel_iff := encode_lt_iff

theorem decodeReversible_lt_iff (left right : ReversibleArray) :
    ExprLt (decodeReversible left) (decodeReversible right) ↔ ReversibleLt left right :=
  reversibleOrderIso.inv_rel_iff left right

/-- 此全域序同构不把全域字典序变成良序：它保留已给出的无限下降族。 -/
theorem reversibleLt_not_wellFounded : ¬ WellFounded ReversibleLt := by
  intro hWellFounded
  exact exprLt_not_wellFounded (reversibleOrderIso.wellFounded_iff.mpr hWellFounded)

end ZeroY
