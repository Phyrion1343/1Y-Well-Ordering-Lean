import OneY.TerminalCopyComparison
import OneY.ReconstructionComparison
import OneY.DecoratedBlockerExpansion

/-! # The actual old numerical mountain supplies decorated blockers -/

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS LowerCopy.Context

theorem matrix_decorated_rowS (base : Row) (hpos : ∀ c, 0 < base.value c) (width cap : Nat)
    (hcap : ∀ c, c < width → base.value c ≤ cap) (r : Nat) :
    DecoratedColumn.RowS (matrix base width cap).raw (topValue base) (width+1+r) := by
  intro c q p hc hQ hP hdist
  rw [matrix_length] at hc
  rw [matrix_numeric_previous base (hcap c hc) hc r] at hQ
  rw [matrix_numeric_parent_all base (hcap c hc) hc r] at hP
  cases r with
  | zero =>
      simp only [↓reduceIte] at hQ
      have he : p = q := Option.some.inj (hP.symm.trans hQ)
      exact False.elim (hdist he)
  | succ r =>
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at hQ
      obtain ⟨z, hpath, hzparent, hkey⟩ := (rows base r).next_exists_key_blocker hQ hP hdist
      have hqlt := (rows base r).forest.parent_left hQ
      have hzq : z ≤ q := by
        rcases hpath with he | ha
        · omega
        · have := ha.lt; omega
      have hz : z < width := by omega
      refine ⟨z, ?_, ?_, ?_⟩
      · rcases hpath with he | ha
        · exact Or.inl he
        · apply Or.inr
          unfold isAncestor
          apply (Forest.ancestorChain_contains_iff (fun h => parent_some_lt h)).mpr
          exact Forest.ancestor_transfer_prefix (rows base (r+1)).forest.parent_left
            (by omega : q < width)
            (fun i hi => (matrix_numeric_parent_all base (hcap i hi) hi (r+1)).symm)
            (ParentForest.ancestor_to_zeroY ha)
      · rw [matrix_numeric_parent_all base (hcap z hz) hz (r+1)]
        exact hzparent
      · have he : width+1+(r+1)+1 = width+1+(r+2) := by omega
        rw [he]
        let M := mountain base hpos
        have hclive : r+1 < M.height c := M.parent_source hP
        have hzlive : r+1 < M.height z := M.parent_source hzparent
        have hnextc : 0 < (rows base (r+1)).next.value c :=
          ((rows base (r+1)).difference_pos_iff c).mpr ⟨p, hP⟩
        have hnextz : 0 < (rows base (r+1)).next.value z :=
          ((rows base (r+1)).difference_pos_iff z).mpr ⟨p, hzparent⟩
        have hnextle := (keyLE_next_iff_of_common_parent (rows base (r+1)) hnextc hnextz
          (hP.trans hzparent.symm)).mp hkey
        have hgeomKey : KeyLEFrom M (topValue base) (r+2) c z := by
          apply (Reconstruction.keyLEFrom_iff_value_le M (topValue base)
            (fun q => topValue_pos base (hpos q)) (r+1)
            (fun u _ q => Reconstruction.restrictedParent_numeric_reconstruction base hpos u q)
            hclive hzlive (hP.trans hzparent.symm)).mpr
          rw [Reconstruction.value_numeric_cell base hpos,
            Reconstruction.value_numeric_cell base hpos]
          exact hnextle
        apply (DecoratedColumn.keyLEFrom_iff_columns M (topValue base) (matrix base width cap).raw
          (width+1) (r+2) c z
          (fun u => matrix_numeric_entry_all base (hcap c hc) hc u)
          (fun u => matrix_numeric_entry_all base (hcap z hz) hz u)).mp
        exact hgeomKey

theorem badAt_topCopies (a : RootedRow) {K d x y cap index : Nat} (hbad : BadAt a K d x y)
    (hcap : (layers a K).row.value x ≤ cap) :
    DecoratedColumn.TopCopies (badAtContext a hbad hcap) index (topValue (layers a K).row)
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) := by
  intro b _ s hs
  rw [badAt_copyColumn_eq]
  exact (badAtTerminalContext a hbad).ordinaryContext.copyValue_parentCopy _ hs b

theorem badAt_expanded_decorated_rowS (a : RootedRow) {K d x y cap index u : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ c, c < x+1 → (layers a K).row.value c ≤ cap) (hu : u ≤ d) :
    DecoratedColumn.RowS ((matrix (layers a K).row (x+1) cap).expand index).raw
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) ((x+1)+1+u) :=
  DecoratedColumn.rowS_expand_le (badAtContext a hbad (hcap x (Nat.lt_succ_self x)))
    (matrix_depthRegular _ _ _) (badAt_topCopies a hbad _) (matrix_decorated_rowS _ (layers a K).positive _ _ hcap u)
    (by change (x+1)+1+u ≤ (x+1)+1+d; omega)

end OneY.NumericFrame

#print axioms OneY.NumericFrame.matrix_decorated_rowS
#print axioms OneY.NumericFrame.badAt_expanded_decorated_rowS
