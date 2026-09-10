import ZeroY.Forest.Comparison
import ZeroY.Mountain.Roots
import ZeroY.Mountain.Encoding
import ZeroY.SequenceOrder
import ZeroY.BMS.PaddedDescent

/-!
# 全部合法表达式上的编码保序

在首个不同列比较两座山脉。每次深度相等，父项也相同，因而相减后仍保留
严格的数值大小关系。较小数值严格下降，保证有限行内出现同方向的深度差。
-/

namespace ZeroY

open Forest

/-- 当前父项相同时，差分保留目标左侧的一致性。 -/
theorem nextLayer_agreeBelow {left right : Layer}
    (hLeft : Forest.Leftward left.previous) {column : Nat}
    (hColumnLeft : column < left.values.length)
    (hColumnRight : column < right.values.length)
    (hAgree : AgreeBelow left right column)
    (hParent : layerParent left column = layerParent right column) :
    AgreeBelow (nextLayer left) (nextLayer right) column := by
  constructor
  · intro i hi
    rw [nextLayer_getD (show i < left.values.length by omega),
      nextLayer_getD (show i < right.values.length by omega)]
    have hp := layerParent_congr_prefix hLeft hAgree hi
    rw [← hp]
    cases hpi : layerParent left i with
    | none => rfl
    | some p =>
        have hpLt := layerParent_some_lt hpi
        simp only
        rw [hAgree.1 i hi, hAgree.1 p (by omega)]
  · intro i hi
    change layerParent left i = layerParent right i
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · subst i; exact hParent
    · exact layerParent_congr_prefix hLeft hAgree hlt

/-- 当前列以下的共同数值与候选森林，在任意山脉层都保持共同前缀。 -/
theorem layerAfter_agree_le {left right : Layer}
    (hLeft : Forest.Leftward left.previous) {column : Nat}
    (hColumnLeft : column < left.values.length)
    (hColumnRight : column < right.values.length)
    (hValues : ∀ i, i ≤ column → left.values[i]?.getD 0 = right.values[i]?.getD 0)
    (hPrevious : ∀ i, i ≤ column → left.previous i = right.previous i)
    (steps : Nat) :
    (∀ i, i ≤ column → (layerAfter steps left).values[i]?.getD 0 =
      (layerAfter steps right).values[i]?.getD 0) ∧
    (∀ i, i ≤ column → (layerAfter steps left).previous i =
      (layerAfter steps right).previous i) := by
  induction steps generalizing left right with
  | zero => exact ⟨hValues, hPrevious⟩
  | succ steps ih =>
      apply ih (fun hp => layerParent_some_lt hp)
        (by simpa using hColumnLeft) (by simpa using hColumnRight)
      · intro i hi
        rw [nextLayer_getD (show i < left.values.length by omega),
          nextLayer_getD (show i < right.values.length by omega)]
        have hp := layerParent_congr_below (target := i) hLeft
          (fun j hj => hValues j (by omega)) (fun j hj => hPrevious j (by omega))
        rw [← hp]
        cases hpi : layerParent left i with
        | none => rfl
        | some p =>
            have hpLt := layerParent_some_lt hpi
            simp only
            rw [hValues i hi, hValues p (by omega)]
      · intro i hi
        exact layerParent_congr_below hLeft
          (fun j hj => hValues j (by omega)) (fun j hj => hPrevious j (by omega))

/-- 严格不同的数值，在有限行内给出严格同方向的第一个深度差。 -/
theorem layer_depth_first_difference {left right : Layer}
    (hLeftInv : left.RootInvariant) (hRightInv : right.RootInvariant) {column : Nat}
    (hColumnLeft : column < left.values.length)
    (hColumnRight : column < right.values.length)
    (hAgree : AgreeBelow left right column)
    (hValue : left.values[column]?.getD 0 < right.values[column]?.getD 0) :
    ∃ row,
      (∀ earlier, earlier < row →
        parentDepth (layerParent (layerAfter earlier left)) column =
          parentDepth (layerParent (layerAfter earlier right)) column) ∧
      parentDepth (layerParent (layerAfter row left)) column <
        parentDepth (layerParent (layerAfter row right)) column := by
  generalize hSize : left.values[column]?.getD 0 = size
  induction size using Nat.strongRecOn generalizing left right with
  | ind size ih =>
      obtain ⟨hDepthLe, hParentOfEq⟩ := layer_depth_compare hLeftInv.leftward hAgree
        (Nat.le_of_lt hValue)
      rcases Nat.eq_or_lt_of_le hDepthLe with hDepthEq | hDepthLt
      · have hParentEq := hParentOfEq hDepthEq
        cases hParent : layerParent left column with
        | none =>
            have hLeftOne := (layerParent_none_iff_value_one hLeftInv hColumnLeft).mp hParent
            have hRightOne := (layerParent_none_iff_value_one hRightInv hColumnRight).mp
              (hParentEq.symm.trans hParent)
            omega
        | some p =>
            have hRightParent : layerParent right column = some p := hParentEq.symm.trans hParent
            have hpLt := layerParent_some_lt hParent
            have hpValue := hAgree.1 p hpLt
            have hpPositive := positive_getD hLeftInv.positive
              (show p < left.values.length by omega)
            have hpSmaller := layerParent_some_value_lt hParent
            have hNextLeft := nextLayer_getD hColumnLeft
            have hNextRight := nextLayer_getD hColumnRight
            simp only [hParent] at hNextLeft
            simp only [hRightParent] at hNextRight
            rw [← hpValue] at hNextRight
            have hNextSize : (nextLayer left).values[column]?.getD 0 < size := by
              rw [hNextLeft, ← hSize]
              exact Nat.sub_lt_of_pos_le hpPositive (Nat.le_of_lt hpSmaller)
            have hNextValue : (nextLayer left).values[column]?.getD 0 <
                (nextLayer right).values[column]?.getD 0 := by
              rw [hNextLeft, hNextRight]
              exact Nat.sub_lt_sub_right (Nat.le_of_lt hpSmaller) hValue
            obtain ⟨row, hEarlier, hLess⟩ := ih _ hNextSize
              (nextLayer_rootInvariant left) (nextLayer_rootInvariant right)
              (by simpa using hColumnLeft) (by simpa using hColumnRight)
              (nextLayer_agreeBelow hLeftInv.leftward hColumnLeft hColumnRight hAgree hParentEq)
              hNextValue rfl
            refine ⟨row + 1, ?_, hLess⟩
            intro earlier hEarlierLt
            cases earlier with
            | zero => exact hDepthEq
            | succ earlier => exact hEarlier earlier (by omega)
      · exact ⟨0, by intro earlier h; omega, hDepthLt⟩

theorem encode_entry_depth (s : Expr) {column : Nat}
    (hColumn : column < s.values.length) (row : Nat) :
    matrixEntry (encode s).raw column row =
      parentDepth (layerParent (layerAfter row ⟨s.values, linearParent⟩)) column := by
  rw [encode_raw, matrixEntry_trimZeroRows]
  exact encodeRaw_entry_depth s.legal hColumn row

/-- 编码的任何既有列仅依赖输入到该列为止的前缀。 -/
theorem encode_entry_eq_of_prefix {s t : Expr} {column : Nat}
    (hS : column < s.values.length) (hT : column < t.values.length)
    (hPrefix : ∀ i, i ≤ column → s.values[i]?.getD 0 = t.values[i]?.getD 0)
    (row : Nat) : matrixEntry (encode s).raw column row =
      matrixEntry (encode t).raw column row := by
  rw [encode_entry_depth s hS, encode_entry_depth t hT]
  obtain ⟨hValues, hPrevious⟩ := layerAfter_agree_le
    (left := ⟨s.values, linearParent⟩) (right := ⟨t.values, linearParent⟩)
    (fun hp => linearParent_leftward hp) hS hT hPrefix (fun _ _ => rfl) row
  apply parentDepth_congr_below (fun hp => layerParent_some_lt hp)
  intro i hi
  exact layerParent_congr_below (legal_layerAfter_rootInvariant s.legal row).leftward
    (fun j hj => hValues j (by omega)) (fun j hj => hPrevious j (by omega))

/-- 首个输入差严格同方向地传到编码矩阵。 -/
theorem encode_lt_of_first_difference {s t : Expr} {column : Nat}
    (hS : column < s.values.length) (hT : column < t.values.length)
    (hPrefix : ∀ i, i < column → s.values[i]?.getD 0 = t.values[i]?.getD 0)
    (hValue : s.values[column]?.getD 0 < t.values[column]?.getD 0) :
    MatrixLt (encode s).raw (encode t).raw := by
  obtain ⟨row, hEarlier, hLess⟩ := layer_depth_first_difference
    (legal_initial_rootInvariant s.legal) (legal_initial_rootInvariant t.legal)
    hS hT ⟨hPrefix, fun _ _ => rfl⟩ hValue
  apply MatrixLt.of_first_difference (column := column) (row := row)
    (by simpa only [encode_length] using hS) (by simpa only [encode_length] using hT)
  · intro i hi index
    exact encode_entry_eq_of_prefix (by omega) (by omega)
      (fun j hj => hPrefix j (by omega)) index
  · intro earlier he
    rw [encode_entry_depth s hS, encode_entry_depth t hT]
    exact hEarlier earlier he
  · rw [encode_entry_depth s hS, encode_entry_depth t hT]
    exact hLess

/-- 有限序列字典序分解为首差或真前缀。 -/
theorem SeqLt.first_difference_or_prefix {s t : Sequence} (h : SeqLt s t) :
    (∃ column, column < s.length ∧ column < t.length ∧
      (∀ i, i < column → s[i]?.getD 0 = t[i]?.getD 0) ∧
      s[column]?.getD 0 < t[column]?.getD 0) ∨
    (s.length < t.length ∧ ∀ i, i < s.length → s[i]?.getD 0 = t[i]?.getD 0) := by
  induction h with
  | nil value rest => exact Or.inr ⟨by simp, by intro i h; simp at h⟩
  | head h => exact Or.inl ⟨0, by simp, by simp, by intro i h; omega, h⟩
  | tail value h ih =>
      rcases ih with ⟨column, hs, ht, hPrefix, hLess⟩ | ⟨hLength, hPrefix⟩
      · apply Or.inl
        refine ⟨column + 1, by simpa using hs, by simpa using ht, ?_, hLess⟩
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact hPrefix i (by omega)
      · apply Or.inr
        refine ⟨by simpa using hLength, ?_⟩
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact hPrefix i (by simpa using hi)

/-- D 在全部合法表达式上严格保序。 -/
theorem encode_strictMono {s t : Expr} (h : ExprLt s t) :
    MatrixLt (encode s).raw (encode t).raw := by
  rcases SeqLt.first_difference_or_prefix h with
    ⟨column, hs, ht, hPrefix, hLess⟩ | ⟨hLength, hPrefix⟩
  · exact encode_lt_of_first_difference hs ht hPrefix hLess
  · apply MatrixLt.of_strict_prefix (by simpa only [encode_length] using hLength)
    intro column hc row
    have hs : column < s.values.length := by simpa only [encode_length] using hc
    have ht : column < t.values.length := by omega
    exact encode_entry_eq_of_prefix hs ht (fun i hi => hPrefix i (by omega)) row

/-- 严格序反映只使用序列三歧性与已证的严格保序。 -/
theorem encode_lt_iff (s t : Expr) :
    MatrixLt (encode s).raw (encode t).raw ↔ ExprLt s t := by
  constructor
  · intro h
    rcases exprLt_trichotomy s t with heq | hst | hts
    · subst t
      exact (MatrixLt.irrefl _ h).elim
    · exact hst
    · exact (MatrixLt.asymm h (encode_strictMono hts)).elim
  · exact encode_strictMono

/-- D 的单射性由完整保序直接推出，无须把解码往返列为前提。 -/
theorem encode_injective_of_order {s t : Expr} (h : encode s = encode t) : s = t := by
  rcases exprLt_trichotomy s t with heq | hst | hts
  · exact heq
  · have hLess := encode_strictMono hst
    rw [h] at hLess
    exact (MatrixLt.irrefl _ hLess).elim
  · have hLess := encode_strictMono hts
    rw [h] at hLess
    exact (MatrixLt.irrefl _ hLess).elim

end ZeroY
