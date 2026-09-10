import OneY.DecoratedColumn

/-! # Transport of blockers retaining the independent top-value comparison -/

namespace OneY.DecoratedColumn

open ZeroY YesMetaZFC.BMS
open ZeroY.BMS

def TopCopies {array : ValidArray} (context : ExpansionContext array) (index : Nat)
    (oldTop newTop : Nat → Nat) : Prop :=
  ∀ copy, copy ≤ index → ∀ source, source < context.lastIndex →
    newTop (copyColumn context copy source) = oldTop source

theorem top_prefix {array : ValidArray} (context : ExpansionContext array) {index : Nat}
    {oldTop newTop : Nat → Nat} (ht : TopCopies context index oldTop newTop)
    {source : Nat} (hs : source < context.lastIndex) : newTop source = oldTop source := by
  have h := ht 0 (Nat.zero_le index) source hs
  rw [copyColumn_zero] at h
  exact h

theorem blocker_prefix {array : ValidArray} (context : ExpansionContext array) {index row : Nat}
    {oldTop newTop : Nat → Nat} (ht : TopCopies context index oldTop newTop)
    (hS : RowS array.raw oldTop row) {column : Nat} (hc : column < context.lastIndex) :
    BlockerAt (array.expand index).raw newTop row column := by
  intro q p hQ hP hdist
  have hprev : previousParent (array.expand index).raw row column = previousParent array.raw row column := by
    cases row with
    | zero => rfl
    | succ r => exact parent_expand_prefix context index r hc
  rw [hprev] at hQ
  rw [parent_expand_prefix context index row hc] at hP
  obtain ⟨z, hpath, hzp, hkey⟩ := hS column q p (by rw [context.array_length]; omega) hQ hP hdist
  have hz : z < context.lastIndex := by
    have hq := previousParent_some_lt hQ
    rcases hpath with he | ha
    · omega
    · have := isAncestor_lt ha; omega
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [isAncestor_expand_prefix context index row z
      (by have := previousParent_some_lt hQ; omega : q < context.lastIndex)]
    exact hpath
  · rw [parent_expand_prefix context index row hz]
    exact hzp
  · rw [top_prefix context ht hc, top_prefix context ht hz]
    exact congr (suffix_expand_prefix context index (row+1) hc)
      (suffix_expand_prefix context index (row+1) hz) hkey

theorem blocker_nonroot_bad {array : ValidArray} (context : ExpansionContext array)
    (hI : DepthRegular array.raw) {index copy source row oldP : Nat}
    {oldTop newTop : Nat → Nat} (ht : TopCopies context index oldTop newTop)
    (hS : RowS array.raw oldTop row) (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hOldP : parent row array.raw source = some oldP) (hBad : context.parentColumn ≤ oldP) :
    BlockerAt (array.expand index).raw newTop row (copyColumn context copy source) := by
  have hParentLt := parent_some_lt hOldP
  have hSourceBad : context.parentColumn < source := by omega
  have hNonroot : source ≠ context.parentColumn := by omega
  intro q p hQ hP hdist
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP] at hP
  simp only [Option.map_some, Option.some.injEq] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hdistOld : oldP ≠ oldQ := by
        intro he
        apply hdist
        rw [← hP, ← hQ, he]
      obtain ⟨z, hpath, hzp, hkey⟩ := hS source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hdistOld
      have hq := previousParent_some_lt hOldQ
      have hz : z < source := by
        rcases hpath with he | ha
        · omega
        · have := isAncestor_lt ha; omega
      have hpz := parent_some_lt hzp
      have hzb : context.parentColumn < z := by omega
      refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
      · rcases hpath with he | ha
        · exact Or.inl ((congrArg (copyColumn context copy) he).trans hQ)
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
          exact ha
      · rw [parent_copyColumn_nonroot context hCopy (by omega) (by omega) row, hzp]
        simpa only [Option.map_some] using congrArg some hP
      · rw [ht copy hCopy source hSource, ht copy hCopy z (by omega)]
        exact copied_le context hI hCopy hSource (by omega) hSourceBad hzb
          (show previousParent array.raw (row+1) source = previousParent array.raw (row+1) z
            from hOldP.trans hzp.symm) hkey

theorem blocker_nonroot_good {array : ValidArray} (context : ExpansionContext array)
    {index copy source row oldP : Nat} {oldTop newTop : Nat → Nat}
    (ht : TopCopies context index oldTop newTop) (hS : RowS array.raw oldTop row)
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex) (hNonroot : source ≠ context.parentColumn)
    (hRow : row < context.maximalRow) (hOldP : parent row array.raw source = some oldP)
    (hGood : oldP < context.parentColumn) :
    BlockerAt (array.expand index).raw newTop row (copyColumn context copy source) := by
  intro q p hQ hP hdist
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_nonroot context hCopy hSource hNonroot row, hOldP,
    Option.map_some, copyColumn_good context copy hGood] at hP
  have hPEq : oldP = p := Option.some.inj hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hdistOld : oldP ≠ oldQ := by
        intro he
        apply hdist
        rw [← hPEq, ← hQ, ← he, copyColumn_good context copy hGood]
      obtain ⟨z, hpath, hzp, hkey⟩ := hS source oldQ oldP
        (by rw [context.array_length]; omega) hOldQ hOldP hdistOld
      have hq := previousParent_some_lt hOldQ
      have hz : z < source := by
        rcases hpath with he | ha
        · omega
        · have := isAncestor_lt ha; omega
      have hsourcekey := suffix_copyColumn_parent_good context hCopy hSource hNonroot hOldP hGood
      by_cases hroot : z = context.parentColumn
      · subst z
        refine ⟨context.parentColumn, ?_, ?_, ?_⟩
        · rw [← hQ]
          exact zero_root_path_copy context hCopy hRow (by omega) hpath
        · rw [parent_expand_prefix context index row context.parentColumn_lt_lastIndex, hzp, hPEq]
        · rw [ht copy hCopy source hSource, top_prefix context ht context.parentColumn_lt_lastIndex]
          exact congr hsourcekey
            (suffix_expand_prefix context index (row+1) context.parentColumn_lt_lastIndex) hkey
      · refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
        · rcases hpath with he | ha
          · exact Or.inl ((congrArg (copyColumn context copy) he).trans hQ)
          · apply Or.inr
            rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
            exact ha
        · rw [parent_copyColumn_nonroot context hCopy (by omega) hroot row, hzp,
            Option.map_some, copyColumn_good context copy hGood, hPEq]
        · rw [ht copy hCopy source hSource, ht copy hCopy z (by omega)]
          exact congr hsourcekey
            (suffix_copyColumn_parent_good context hCopy (by omega) hroot hzp hGood) hkey

theorem blocker_root_below {array : ValidArray} (context : ExpansionContext array)
    (hI : DepthRegular array.raw) {index copy row : Nat} {oldTop newTop : Nat → Nat}
    (ht : TopCopies context index oldTop newTop) (hS : RowS array.raw oldTop row)
    (hCopy : copy+1 ≤ index) (hRow : row < context.maximalRow) :
    BlockerAt (array.expand index).raw newTop row (context.copyPosition (copy+1) 0) := by
  intro q p hQ hP hdist
  rw [previousParent_copied_root_low context hCopy (Nat.le_of_lt hRow)] at hQ
  rw [parent_copied_root_low_of_le context hCopy (by omega) hRow] at hP
  simp only [Nat.add_sub_cancel] at hP
  cases hOldQ : previousParent array.raw row context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw context.lastIndex with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
          have hdistOld : oldP ≠ oldQ := by
            intro he
            apply hdist
            rw [← hP, ← hQ, he]
          obtain ⟨z, hpath, hzp, hkey⟩ := hS context.lastIndex oldQ oldP
            (by rw [context.array_length]; omega) hOldQ hOldP hdistOld
          have hq := previousParent_some_lt hOldQ
          have hz : z < context.lastIndex := by
            rcases hpath with he | ha
            · omega
            · have := isAncestor_lt ha; omega
          have hrootAnc := isAncestor_of_lt_row hRow (direct_parent_isAncestor context.parent_eq)
          have hpb := ancestor_le_parent hOldP hrootAnc
          have hpz := parent_some_lt hzp
          have hzb : context.parentColumn < z := by omega
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hpath with he | ha
            · exact Or.inl ((congrArg (copyColumn context copy) he).trans hQ)
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context (by omega) hz hq]
              exact ha
          · rw [parent_copyColumn_nonroot context (by omega) hz (by omega) row, hzp]
            simpa only [Option.map_some] using congrArg some hP
          · rw [ht copy (by omega) z hz]
            have hlift := lifted_le context hI (by rw [context.array_length]; omega)
              (by rw [context.array_length]; omega) context.parentColumn_lt_lastIndex hzb
              (show previousParent array.raw (row+1) context.lastIndex = previousParent array.raw (row+1) z
                from hOldP.trans hzp.symm) hkey copy
            have hstrict := strict_of_lt_of_le (a := newTop (context.copyPosition (copy+1) 0))
              (newroot_suffix_lt_ghost context hCopy hRow) hlift
            exact congr (ColumnEq.refl _)
              (suffix_copyColumn_eq_lifted context (by omega) hz (by omega) (row+1)) hstrict

end OneY.DecoratedColumn

#print axioms OneY.DecoratedColumn.blocker_nonroot_bad
#print axioms OneY.DecoratedColumn.blocker_nonroot_good
#print axioms OneY.DecoratedColumn.blocker_root_below
