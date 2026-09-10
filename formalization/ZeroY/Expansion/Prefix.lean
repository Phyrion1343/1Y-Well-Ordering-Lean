import ZeroY.Expansion.Context
import ZeroY.PaddedExt
import ZeroY.OrderEmbedding
import ZeroY.Structural.Prefix

/-!
# 前缀交换及退化展开

编码与截取任意前缀交换。删除末项的退化展开因此直接交换，不需要
假定源表达式是标准式，也不需要展开保持定理。
-/

namespace ZeroY

open YesMetaZFC.BMS

def Expr.take (s : Expr) (count : Nat) : Expr :=
  ⟨s.values.take count, legal_take s.legal count⟩

def matrixPrefix (array : ValidArray) (count : Nat) : ValidArray where
  raw := trimZeroRows (array.raw.take count)
  rectangular_eq := by
    apply rectangular_trimZeroRows
    apply rectangular_iff_exists_uniformHeight.mpr
    refine ⟨trimHeight array.raw, ?_⟩
    intro column hColumn
    exact validArray_uniform_trimHeight array column (List.mem_of_mem_take hColumn)
  trimmed_eq := trimZeroRows_idempotent _

theorem encode_take (s : Expr) (count : Nat) :
    encode (s.take count) = matrixPrefix (encode s) count := by
  apply validArray_eq_of_padded_entries
  · rw [encode_length]
    simp only [Expr.take, matrixPrefix, length_trimZeroRows, List.length_take, encode_length]
  · intro column hColumn row
    have hBounds : column < s.values.length ∧ column < count := by
      rw [encode_length] at hColumn
      change column < (s.values.take count).length at hColumn
      simp only [List.length_take] at hColumn
      omega
    change matrixEntry (encode (s.take count)).raw column row =
      matrixEntry (trimZeroRows ((encode s).raw.take count)) column row
    rw [matrixEntry_trimZeroRows, matrixEntry_take hBounds.2]
    apply encode_entry_eq_of_prefix
    · simpa only [encode_length] using hColumn
    · exact hBounds.1
    · intro earlier hEarlier
      exact congrArg (fun value : Option Nat => value.getD 0)
        (List.getElem?_take_of_lt (by omega : earlier < count))

theorem expandY_eq_take_of_no_site (s : Expr) (count : Nat)
    (hNone : expansionSite s.values = none) :
    expandY s count = s.take (s.values.length - 1) := by
  apply Expr.ext
  simp only [expandY_values, expandYRaw, hNone, Expr.take]

theorem encode_expandY_of_no_site (s : Expr) (count : Nat)
    (hNone : expansionSite s.values = none) :
    encode (expandY s count) = (encode s).expand count := by
  rw [expandY_eq_take_of_no_site s count hNone, encode_take]
  have hMaximal := (expansionSite_none_iff s).mp hNone
  apply ValidArray.ext
  change trimZeroRows ((encode s).raw.take (s.values.length - 1)) =
    trimZeroRows (expandRaw (encode s).raw count)
  rw [← encode_length s]
  unfold expandRaw
  split
  next hLength => rw [hLength]; rfl
  next last hLength => simp only [hMaximal, hLength, Nat.succ_sub_one]

end ZeroY
