import ZeroY.Forest.MatrixParents
import ZeroY.Mountain.CommonChain

/-! # 共用候选链时，提高标签保持所有已有严格祖先 -/

namespace ZeroY.Forest

theorem nearestSmaller_ancestor_mono {parent : ParentMap} (hLeft : Leftward parent)
    {value : Nat → Nat} {left right ancestor : Nat}
    (hChain : ∀ candidate, Ancestor parent left candidate ↔ Ancestor parent right candidate)
    (hValue : value left ≤ value right)
    (hAncestor : Ancestor (nearestSmaller parent value) left ancestor) :
    Ancestor (nearestSmaller parent value) right ancestor := by
  cases hl : nearestSmaller parent value left with
  | none =>
      rcases YesMetaZFC.BMS.transGen_head hAncestor with hd | ⟨next, hn, _⟩
      · simp [hl] at hd
      · simp [hl] at hn
  | some p =>
      obtain ⟨hpAnc, hpVal, _⟩ := (nearestSmaller_some_iff hLeft).mp hl
      have hpRight : Ancestor parent right p := (hChain p).mp hpAnc
      have hpValRight : value p < value right := by omega
      cases hr : nearestSmaller parent value right with
      | none =>
          have := (nearestSmaller_none_iff hLeft).mp hr p hpRight
          omega
      | some q =>
          obtain ⟨hqAnc, _, hqMax⟩ := (nearestSmaller_some_iff hLeft).mp hr
          have hpLe := hqMax p hpRight hpValRight
          rcases Nat.eq_or_lt_of_le hpLe with heq | hlt
          · subst q
            exact (ancestor_iff_of_parent_eq (hl.trans hr.symm) ancestor).mp hAncestor
          · have hQP := nearestSmaller_ancestor_of_between hLeft hl ((hChain q).mpr hqAnc) hlt
            have hRP : Ancestor (nearestSmaller parent value) right p :=
              ancestor_trans (Relation.TransGen.single hr) hQP
            rcases YesMetaZFC.BMS.transGen_head hAncestor with hd | ⟨next, hn, hRest⟩
            · have heq : ancestor = p := Option.some.inj (hd.symm.trans hl)
              subst ancestor
              exact hRP
            · have heq : next = p := Option.some.inj (hn.symm.trans hl)
              subst next
              exact ancestor_trans hRP hRest

end ZeroY.Forest

namespace ZeroY

open YesMetaZFC.BMS

/-- 任意矩形矩阵中，共前行父项且坐标提高时保留本行的所有严格祖先。 -/
theorem matrix_ancestor_mono_of_previous_eq {array : Matrix}
    (hRect : rectangular array = true) {row left right ancestor : Nat}
    (hPrevious : previousParent array row left = previousParent array row right)
    (hValue : matrixEntry array left row ≤ matrixEntry array right row)
    (hAncestor : isAncestor array row ancestor left = true) :
    isAncestor array row ancestor right = true := by
  have hLeft : Forest.Leftward (previousParent array row) := by
    intro target found hp
    cases row with
    | zero => exact linearParent_leftward hp
    | succ row => exact parent_some_lt hp
  have hChain := Forest.ancestor_iff_of_parent_eq hPrevious
  have hRaw : Forest.Ancestor (parent row array) left ancestor :=
    isAncestor_iff_strictAncestor.mp hAncestor
  have hParent := parent_eq_nearestSmaller hRect row
  rw [hParent] at hRaw
  have hResult := Forest.nearestSmaller_ancestor_mono hLeft hChain hValue hRaw
  rw [← hParent] at hResult
  exact isAncestor_iff_strictAncestor.mpr hResult

end ZeroY
