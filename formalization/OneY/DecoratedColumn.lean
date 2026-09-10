import ZeroY.Structural.Expansion

/-! # Finite depth columns with an independent final top-value coordinate -/

namespace OneY.DecoratedColumn

open ZeroY YesMetaZFC.BMS

def LE (left : List Nat) (leftTop : Nat) (right : List Nat) (rightTop : Nat) : Prop :=
  ColumnLt left right ∨ (ColumnEq left right ∧ leftTop ≤ rightTop)

theorem toColumnLe {left right : List Nat} {a b : Nat} (h : LE left a right b) :
    ColumnLe left right := by
  rcases h with h | ⟨h, _⟩
  · exact Or.inr h
  · exact Or.inl h

theorem congr {left right left' right' : List Nat} {a b : Nat}
    (hL : ColumnEq left' left) (hR : ColumnEq right' right) (h : LE left a right b) :
    LE left' a right' b := by
  rcases h with h | ⟨h, ht⟩
  · exact Or.inl (ColumnLt.of_lt_of_eq (ColumnLt.of_eq_of_lt hL h) hR.symm)
  · exact Or.inr ⟨hL.trans (h.trans hR.symm), ht⟩

theorem strict_of_lt_of_le {left middle right : List Nat} {a b c : Nat}
    (h : ColumnLt left middle) (hnext : LE middle b right c) : LE left a right c := by
  rcases hnext with hnext | ⟨hnext, _⟩
  · exact Or.inl (ColumnLt.trans h hnext)
  · exact Or.inl (ColumnLt.of_lt_of_eq h hnext)

def RowS (array : Matrix) (top : Nat → Nat) (row : Nat) : Prop :=
  ∀ column q p, column < array.length →
    previousParent array row column = some q → parent row array column = some p → p ≠ q →
    ∃ z, (z = q ∨ isAncestor array row z q = true) ∧ parent row array z = some p ∧
      LE (columnSuffix array column (row+1)) (top column)
        (columnSuffix array z (row+1)) (top z)

def BlockerAt (array : Matrix) (top : Nat → Nat) (row column : Nat) : Prop :=
  ∀ q p, previousParent array row column = some q → parent row array column = some p → p ≠ q →
    ∃ z, (z = q ∨ isAncestor array row z q = true) ∧ parent row array z = some p ∧
      LE (columnSuffix array column (row+1)) (top column)
        (columnSuffix array z (row+1)) (top z)

theorem lifted_le {array : ValidArray} (context : ExpansionContext array)
    (hI : DepthRegular array.raw) {start left right : Nat}
    (hL : left < array.raw.length) (hR : right < array.raw.length)
    (hLb : context.parentColumn < left) (hRb : context.parentColumn < right)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    {a b : Nat} (h : LE (columnSuffix array.raw left start) a
      (columnSuffix array.raw right start) b) (copy : Nat) :
    LE (BMS.liftedSuffix context copy left start) a
      (BMS.liftedSuffix context copy right start) b := by
  rcases h with h | ⟨h, ht⟩
  · exact Or.inl (BMS.liftedSuffix_lt_of_common_previous context hI hL hR hLb hRb hPrevious h copy)
  · exact Or.inr ⟨BMS.liftedSuffix_eq_of_common_previous context hI hL hR hLb hRb hPrevious h copy, ht⟩

theorem copied_le {array : ValidArray} (context : ExpansionContext array)
    (hI : DepthRegular array.raw) {start left right index copy : Nat}
    (hcopy : copy ≤ index) (hL : left < context.lastIndex) (hR : right < context.lastIndex)
    (hLb : context.parentColumn < left) (hRb : context.parentColumn < right)
    (hPrevious : previousParent array.raw start left = previousParent array.raw start right)
    {a b : Nat} (h : LE (columnSuffix array.raw left start) a
      (columnSuffix array.raw right start) b) :
    LE (columnSuffix (array.expand index).raw (BMS.copyColumn context copy left) start) a
      (columnSuffix (array.expand index).raw (BMS.copyColumn context copy right) start) b := by
  apply congr (BMS.suffix_copyColumn_eq_lifted context hcopy hL (by omega) start)
    (BMS.suffix_copyColumn_eq_lifted context hcopy hR (by omega) start)
  exact lifted_le context hI (by rw [context.array_length]; omega)
    (by rw [context.array_length]; omega) hLb hRb hPrevious h copy

end OneY.DecoratedColumn

#print axioms OneY.DecoratedColumn.copied_le
