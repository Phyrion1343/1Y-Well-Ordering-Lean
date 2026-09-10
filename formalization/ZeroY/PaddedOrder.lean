import ZeroY.MatrixOrder

/-!
# 补零矩阵字典序的严格序性质

列的等价按逐坐标补零相等理解。严格比较尊重该等价，因此列高的表示差异
不会破坏矩阵字典序的传递性。
-/

namespace ZeroY

namespace ColumnEq

theorem refl (a : List Nat) : ColumnEq a a := fun _ => rfl

theorem symm {a b : List Nat} (h : ColumnEq a b) : ColumnEq b a :=
  fun row => (h row).symm

theorem trans {a b c : List Nat} (hAB : ColumnEq a b) (hBC : ColumnEq b c) :
    ColumnEq a c := fun row => (hAB row).trans (hBC row)

end ColumnEq

namespace ColumnLt

theorem irrefl (a : List Nat) : ¬ ColumnLt a a := by
  rintro ⟨row, _, hLess⟩
  exact Nat.lt_irrefl _ hLess

theorem of_eq_of_lt {a b c : List Nat} (hEq : ColumnEq a b) (hLt : ColumnLt b c) :
    ColumnLt a c := by
  rcases hLt with ⟨row, hEarlier, hLess⟩
  refine ⟨row, fun index hIndex => (hEq index).trans (hEarlier index hIndex), ?_⟩
  rw [hEq row]
  exact hLess

theorem of_lt_of_eq {a b c : List Nat} (hLt : ColumnLt a b) (hEq : ColumnEq b c) :
    ColumnLt a c := by
  rcases hLt with ⟨row, hEarlier, hLess⟩
  refine ⟨row, fun index hIndex => (hEarlier index hIndex).trans (hEq index), ?_⟩
  rw [← hEq row]
  exact hLess

theorem trans {a b c : List Nat} (hAB : ColumnLt a b) (hBC : ColumnLt b c) :
    ColumnLt a c := by
  rcases hAB with ⟨rowAB, hEarlierAB, hLessAB⟩
  rcases hBC with ⟨rowBC, hEarlierBC, hLessBC⟩
  by_cases hABFirst : rowAB < rowBC
  · refine ⟨rowAB, ?_, ?_⟩
    · intro index hIndex
      exact (hEarlierAB index hIndex).trans
        (hEarlierBC index (Nat.lt_trans hIndex hABFirst))
    · rw [← hEarlierBC rowAB hABFirst]
      exact hLessAB
  · by_cases hBCFirst : rowBC < rowAB
    · refine ⟨rowBC, ?_, ?_⟩
      · intro index hIndex
        exact (hEarlierAB index (Nat.lt_trans hIndex hBCFirst)).trans
          (hEarlierBC index hIndex)
      · rw [hEarlierAB rowBC hBCFirst]
        exact hLessBC
    · have hSame : rowAB = rowBC := by omega
      subst rowBC
      exact ⟨rowAB, fun index hIndex =>
        (hEarlierAB index hIndex).trans (hEarlierBC index hIndex),
        Nat.lt_trans hLessAB hLessBC⟩

end ColumnLt

namespace MatrixLt

theorem irrefl (array : Matrix) : ¬ MatrixLt array array := by
  induction array with
  | nil => intro h; cases h
  | cons column rest ih =>
      intro h
      cases h with
      | head hLess => exact ColumnLt.irrefl column hLess
      | tail _ hTail => exact ih hTail

theorem trans {a b c : Matrix} (hAB : MatrixLt a b) (hBC : MatrixLt b c) :
    MatrixLt a c := by
  induction hAB generalizing c with
  | nil column rest =>
      cases hBC with
      | head _ => exact .nil _ _
      | tail _ _ => exact .nil _ _
  | head hLess =>
      cases hBC with
      | head hNext => exact .head (ColumnLt.trans hLess hNext)
      | tail hEq _ => exact .head (ColumnLt.of_lt_of_eq hLess hEq)
  | tail hEq hTail ih =>
      cases hBC with
      | head hNext => exact .head (ColumnLt.of_eq_of_lt hEq hNext)
      | tail hNextEq hNext => exact .tail (ColumnEq.trans hEq hNextEq) (ih hNext)

theorem asymm {a b : Matrix} (hAB : MatrixLt a b) : ¬ MatrixLt b a := by
  intro hBA
  exact irrefl a (trans hAB hBA)

end MatrixLt

end ZeroY
