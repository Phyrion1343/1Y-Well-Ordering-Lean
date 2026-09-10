import OneY.NumericFrame
import OneY.RelativeBlocker

/-! # Proved relative blocker conditions above the concrete candidate frame -/

namespace OneY.Numeric

theorem rows_rows (base : Row) (r s : Nat) : rows (rows base r) s = rows base (r+s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      change (rows (rows base r) s).next = (rows base (r+s)).next
      rw [ih]

theorem Row.next_exists_key_blocker (a : Row) {c q p : Nat}
    (hQ : a.forest.parent c = some q) (hP : a.next.forest.parent c = some p)
    (hdist : p ≠ q) :
    ∃ z, (z = q ∨ a.next.forest.Ancestor z q) ∧
      a.next.forest.parent z = some p ∧ KeyLE a.next.next c z := by
  have hqpos : 0 < a.difference q := by
    by_cases hz : a.difference q = 0
    · have hn := a.difference_zero_parent_none hz
      have ha := (restrictedParent_spec a.forest a.difference hP).1
      rcases ZeroY.Forest.ancestor_eq_or_below_parent hQ ha with he | ha
      · exact False.elim (hdist he)
      · have h := ParentForest.ancestor_of_zeroY ha
        cases h with
        | direct hp => rw [hn] at hp; contradiction
        | step _ hp => rw [hn] at hp; contradiction
    · omega
  obtain ⟨z, hpath, hpz, hle⟩ := restrictedParent_exists_blocker
    a.forest a.difference hQ hP hdist hqpos
  have hcz : a.next.value c ≤ a.next.value z := hle
  have hpc : 0 < a.next.next.value c := (a.next.difference_pos_iff c).mpr ⟨p, hP⟩
  have hpzz : a.next.forest.parent z = some p := hpz
  have hpzpos : 0 < a.next.next.value z := (a.next.difference_pos_iff z).mpr ⟨p, hpzz⟩
  refine ⟨z, hpath, hpzz, ?_⟩
  apply (keyLE_next_iff_of_common_parent a.next hpc hpzpos (hP.trans hpzz.symm)).mpr
  change a.next.difference c ≤ a.next.difference z
  simp only [Row.difference, hP, hpzz]
  omega

end OneY.Numeric

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS

theorem matrix_numeric_previous (base : Row) {width cap c : Nat}
    (hcap : base.value c ≤ cap) (hc : c < width) (r : Nat) :
    previousParent (matrix base width cap).raw (width+1+r) c =
      (if r = 0 then base.forest.parent c else (rows base (r-1)).forest.parent c) := by
  cases r with
  | zero =>
      simp only [Nat.add_zero, ↓reduceIte]
      change parent width (matrix base width cap).raw c = base.forest.parent c
      rw [matrix_parent base (by omega : width < width+1+cap) hc, forest_boundary]
  | succ r =>
      have he : width+1+(r+1) = (width+1+r)+1 := by omega
      rw [he]
      change parent (width+1+r) (matrix base width cap).raw c = _
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      exact matrix_numeric_parent_all base hcap hc r

theorem columnLe_of_numeric_key (base : Row) {width cap c z start : Nat}
    (hc : c < width) (hz : z < width) (hcapc : base.value c ≤ cap) (hcapz : base.value z ≤ cap)
    (hkey : KeyLE (rows base start) c z) :
    ColumnLe (columnSuffix (matrix base width cap).raw c (width+1+start))
      (columnSuffix (matrix base width cap).raw z (width+1+start)) := by
  have hentry (q : Nat) (hq : q < width) (hcapq : base.value q ≤ cap) (i : Nat) :
      columnEntry (columnSuffix (matrix base width cap).raw q (width+1+start)) i =
        (rows (rows base start) i).forest.depth q := by
    rw [columnEntry_suffix]
    have he : width+1+start+i = width+1+(start+i) := by omega
    rw [he, matrix_numeric_entry_all base hcapq hq, rows_rows]
  have hequal (h : DepthsEqual (rows base start) c z) :
      ColumnEq (columnSuffix (matrix base width cap).raw c (width+1+start))
        (columnSuffix (matrix base width cap).raw z (width+1+start)) := by
    intro i
    rw [hentry c hc hcapc, hentry z hz hcapz]
    exact h i
  rcases hkey with (⟨i, hbefore, hlt⟩ | ⟨heq, _⟩) | ⟨heq, _⟩
  · refine Or.inr ⟨i, ?_, ?_⟩
    · intro j hj
      rw [hentry c hc hcapc, hentry z hz hcapz]
      exact hbefore j hj
    · rw [hentry c hc hcapc, hentry z hz hcapz]
      exact hlt
  · exact Or.inl (hequal heq)
  · exact Or.inl (hequal heq)

theorem matrix_rowS (base : Row) (width cap : Nat)
    (hcap : ∀ c, c < width → base.value c ≤ cap) (r : Nat) :
    RelativeBlocker.RowS (matrix base width cap).raw (width+1+r) := by
  intro c q p hc hQ hP hdist
  rw [matrix_length] at hc
  have hQc := matrix_numeric_previous base (hcap c hc) hc r
  rw [hQc] at hQ
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
        apply columnLe_of_numeric_key base hc hz (hcap c hc) (hcap z hz)
        exact hkey

theorem matrix_aboveS (base : Row) (width cap : Nat)
    (hcap : ∀ c, c < width → base.value c ≤ cap) :
    RelativeBlocker.AboveS (matrix base width cap).raw (width+1) := by
  intro r hr
  have he : width+1+(r-(width+1)) = r := by omega
  rw [← he]
  exact matrix_rowS base width cap hcap (r-(width+1))

end OneY.NumericFrame

#print axioms OneY.Numeric.Row.next_exists_key_blocker
#print axioms OneY.NumericFrame.matrix_aboveS
