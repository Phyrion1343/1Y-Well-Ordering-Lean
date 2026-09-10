import OneY.DecoratedBlocker

/-! # Decorated blocker preservation through and below the active row -/

namespace OneY.DecoratedColumn

open ZeroY YesMetaZFC.BMS
open ZeroY.BMS

theorem blocker_nonroot_high {array : ValidArray} (context : ExpansionContext array)
    {index copy source row : Nat} {oldTop newTop : Nat → Nat}
    (ht : TopCopies context index oldTop newTop) (hS : RowS array.raw oldTop row)
    (hCopy : copy ≤ index) (hSource : source < context.lastIndex)
    (hNonroot : source ≠ context.parentColumn) (hRow : context.maximalRow ≤ row) :
    BlockerAt (array.expand index).raw newTop row (copyColumn context copy source) := by
  intro q p hQ hP hdist
  rw [previousParent_copyColumn_nonroot context hCopy hSource hNonroot row] at hQ
  rw [parent_copyColumn_high context hCopy hSource hRow] at hP
  cases hOldQ : previousParent array.raw row source with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      cases hOldP : parent row array.raw source with
      | none => simp [hOldP] at hP
      | some oldP =>
          simp only [hOldP, Option.map_some, Option.some.injEq] at hP
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
          refine ⟨copyColumn context copy z, ?_, ?_, ?_⟩
          · rcases hpath with he | ha
            · exact Or.inl ((congrArg (copyColumn context copy) he).trans hQ)
            · apply Or.inr
              rw [← hQ, isAncestor_copyColumn context hCopy (by omega) (by omega)]
              exact ha
          · rw [parent_copyColumn_high context hCopy (by omega) hRow, hzp]
            simpa only [Option.map_some] using congrArg some hP
          · rw [ht copy hCopy source hSource, ht copy hCopy z (by omega)]
            exact congr (suffix_copyColumn_high context hCopy hSource (by omega : context.maximalRow ≤ row+1))
              (suffix_copyColumn_high context hCopy (by omega) (by omega : context.maximalRow ≤ row+1)) hkey

theorem blocker_root_at {array : ValidArray} (context : ExpansionContext array)
    {index copy : Nat} {oldTop newTop : Nat → Nat}
    (ht : TopCopies context index oldTop newTop) (hS : RowS array.raw oldTop context.maximalRow)
    (hCopy : copy+1 ≤ index) :
    BlockerAt (array.expand index).raw newTop context.maximalRow (context.copyPosition (copy+1) 0) := by
  intro q p hQ hP _
  rw [previousParent_copied_root_low context hCopy (Nat.le_refl _)] at hQ
  rw [parent_copied_root_high_of_le context hCopy (Nat.le_refl _)] at hP
  cases hOldQ : previousParent array.raw context.maximalRow context.lastIndex with
  | none => simp [hOldQ] at hQ
  | some oldQ =>
      simp only [hOldQ, Option.map_some, Option.some.injEq] at hQ
      have hq := previousParent_some_lt hOldQ
      have hrootPath : context.parentColumn = oldQ ∨
          isAncestor array.raw context.maximalRow context.parentColumn oldQ = true := by
        by_cases he : context.parentColumn = oldQ
        · exact Or.inl he
        · obtain ⟨z, hpath, hzp, _⟩ := hS context.lastIndex oldQ context.parentColumn
            (by rw [context.array_length]; omega) hOldQ context.parent_eq he
          apply Or.inr
          rcases hpath with hze | ha
          · rw [← hze]
            exact direct_parent_isAncestor hzp
          · exact isAncestor_trans (direct_parent_isAncestor hzp) ha
      refine ⟨copyColumn context copy context.parentColumn, ?_, ?_, ?_⟩
      · rcases hrootPath with he | ha
        · exact Or.inl ((congrArg (copyColumn context copy) he).trans hQ)
        · apply Or.inr
          rw [← hQ, isAncestor_copyColumn context (by omega) context.parentColumn_lt_lastIndex hq]
          exact ha
      · rw [copyColumn_bad context copy (Nat.le_refl _), Nat.sub_self,
          parent_copied_root_high_of_le context (by omega) (Nat.le_refl _)]
        exact hP
      · have hL := suffix_copyColumn_high context hCopy context.parentColumn_lt_lastIndex
          (start := context.maximalRow+1) (by omega)
        have hR := suffix_copyColumn_high context (show copy ≤ index by omega) context.parentColumn_lt_lastIndex
          (start := context.maximalRow+1) (by omega)
        rw [copyColumn_bad context (copy+1) (Nat.le_refl _), Nat.sub_self] at hL
        have htL := ht (copy+1) hCopy context.parentColumn context.parentColumn_lt_lastIndex
        rw [copyColumn_bad context (copy+1) (Nat.le_refl _), Nat.sub_self] at htL
        exact Or.inr ⟨hL.trans hR.symm, by
          rw [htL, ht copy (by omega) context.parentColumn context.parentColumn_lt_lastIndex]
          exact Nat.le_refl _⟩

theorem rowS_expand_le {array : ValidArray} (context : ExpansionContext array)
    (hI : DepthRegular array.raw) {index row : Nat} {oldTop newTop : Nat → Nat}
    (ht : TopCopies context index oldTop newTop) (hS : RowS array.raw oldTop row)
    (hrow : row ≤ context.maximalRow) : RowS (array.expand index).raw newTop row := by
  intro column q p hc hQ hP hdist
  have hAt : BlockerAt (array.expand index).raw newTop row column := by
    by_cases hpref : column < context.lastIndex
    · exact blocker_prefix context ht hS hpref
    · have hng : context.parentColumn ≤ column := by have := context.parentColumn_lt_lastIndex; omega
      obtain ⟨copy, localColumn, hCopy, hLocal, he⟩ := context.exists_copyPosition_of_not_good hc hng
      rw [he]
      have hs : context.parentColumn+localColumn < context.lastIndex := by
        have := context.parentColumn_lt_lastIndex
        simp only [ExpansionContext.blockLength] at hLocal
        omega
      by_cases hzero : localColumn = 0
      · subst localColumn
        cases copy with
        | zero =>
            have hcol : column = context.parentColumn := by simpa only [ExpansionContext.copyPosition_zero, Nat.add_zero] using he
            exact False.elim (hpref (hcol ▸ context.parentColumn_lt_lastIndex))
        | succ copy =>
            by_cases hl : row < context.maximalRow
            · exact blocker_root_below context hI ht hS hCopy hl
            · have heq : row = context.maximalRow := by omega
              subst row
              exact blocker_root_at context ht hS hCopy
      · rw [← copyColumn_local context copy localColumn]
        have hnonroot : context.parentColumn+localColumn ≠ context.parentColumn := by omega
        by_cases hl : row < context.maximalRow
        · cases hold : parent row array.raw (context.parentColumn+localColumn) with
          | none =>
              intro q p hQ hP hdist
              rw [parent_copyColumn_nonroot context hCopy hs hnonroot row, hold, Option.map_none] at hP
              contradiction
          | some oldP =>
              by_cases hg : oldP < context.parentColumn
              · exact blocker_nonroot_good context ht hS hCopy hs hnonroot hl hold hg
              · exact blocker_nonroot_bad context hI ht hS hCopy hs hold (by omega)
        · exact blocker_nonroot_high context ht hS hCopy hs hnonroot (by omega)
  exact hAt q p hQ hP hdist

end OneY.DecoratedColumn

#print axioms OneY.DecoratedColumn.blocker_root_at
#print axioms OneY.DecoratedColumn.rowS_expand_le
