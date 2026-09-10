import OneY.LowerCopyDominance
import OneY.LowerCopyRoots
import OneY.SparseBlocker
import OneY.ReconstructionComparison

/-! # The good-parent branches of lower-copy sparse NS recovery -/

namespace OneY.LowerCopy.Context

open Reconstruction

/-- The precise upper-layer C input. It concerns only copied top values of
nonroot bad-part sources whose *computed extracted parent* is good or absent.
It contains no assertion about the current lower layer's canonicality. -/
def UpperFixed (C : Context) (oldTop newTop : Nat → Nat) : Prop :=
  ∀ s, C.coordinates.y < s → s < C.coordinates.x →
    (∀ q, Numeric.restrictedParent (Pseudo.forest C.mountain) oldTop s = some q →
      q < C.coordinates.y) →
    ∀ b, oldTop s = newTop (C.coordinates.parentCopy b s)

theorem value_tail_eq_from_upperFixed (C : Context) (oldTop newTop : Nat → Nat)
    (hGoodTop : ∀ q, q < C.coordinates.y → oldTop q = newTop q)
    (hUpper : C.UpperFixed oldTop newTop) {s p r : Nat}
    (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hp : (C.mountain.row r).parent s = some p) (hGood : p < C.coordinates.y) (b : Nat) :
    ∀ u, r ≤ u → value C.mountain oldTop u s =
      value C.toRowMountain newTop u (C.coordinates.parentCopy b s) := by
  have hTop := hUpper s hs hx (fun _ hq => C.extracted_parent_good_of_row_parent_good oldTop hp hGood hq) b
  exact C.value_tail_eq_of_good_parent oldTop newTop hGoodTop hs hx hp hGood b hTop

theorem value_original_prefix_eq (C : Context) (oldTop newTop : Nat → Nat)
    (hTop : ∀ s, s < C.coordinates.x → oldTop s = newTop s)
    {s : Nat} (hs : s < C.coordinates.x) (r : Nat) :
    value C.mountain oldTop r s = value C.toRowMountain newTop r s := by
  exact value_prefix_congr C.mountain C.toRowMountain oldTop newTop C.coordinates.x
    (fun _ hc => (C.height_original (Nat.le_of_lt hc)).symm)
    (fun _ _ hc => (C.parent_original (Nat.le_of_lt hc)).symm) hTop s hs r

theorem not_inCone_nonroot_good_parent (C : Context) {s p r : Nat}
    (hNot : s ≠ C.coordinates.y) (hp : (C.mountain.row r).parent s = some p)
    (hGood : p < C.coordinates.y) : ¬ C.InCone s := by
  by_cases hs : s < C.coordinates.y
  · exact C.not_inCone_of_good hs
  · exact C.not_inCone_of_good_parent (by omega) hp hGood

def blockerCopy (C : Context) (b z : Nat) : Nat :=
  if z = C.coordinates.y then C.coordinates.y else C.coordinates.parentCopy b z

theorem good_blocker_path (C : Context) {r q z p : Nat}
    (hq : q ≤ C.coordinates.x) (b : Nat)
    (hPath : z = q ∨ (C.mountain.row r).Ancestor z q)
    (hParent : (C.mountain.row r).parent z = some p) (hGood : p < C.coordinates.y) :
    C.blockerCopy b z = C.coordinates.parentCopy b q ∨
      (C.row r).Ancestor (C.blockerCopy b z) (C.coordinates.parentCopy b q) := by
  by_cases hRoot : z = C.coordinates.y
  · subst z
    rw [blockerCopy, if_pos rfl]
    have hr : r < C.floor := C.mountain.parent_source hParent
    exact C.zero_root_path_copy_low hr hq b hPath
  · rw [blockerCopy, if_neg hRoot]
    rcases hPath with he | ha
    · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
    · by_cases hLow : r < C.floor
      · exact Or.inr (C.low_ancestor_copy hLow ha hq b)
      · have hOutZ := C.not_inCone_nonroot_good_parent hRoot hParent hGood
        have hOutQ : ¬ C.InCone q := by
          intro hCone
          exact hOutZ (C.high_ancestor_inCone (by omega) hCone ha)
        exact Or.inr (C.outside_ancestor_copy (by omega) hOutQ ha hq b)

theorem good_blocker_parent (C : Context) {r z p : Nat}
    (hz : z < C.coordinates.x) (b : Nat)
    (hParent : (C.mountain.row r).parent z = some p) (hGood : p < C.coordinates.y) :
    C.parent r (C.blockerCopy b z) = some p := by
  by_cases hRoot : z = C.coordinates.y
  · rw [blockerCopy, if_pos hRoot, ← hRoot, C.parent_original (Nat.le_of_lt hz)]
    exact hParent
  · have hOut := C.not_inCone_nonroot_good_parent hRoot hParent hGood
    rw [blockerCopy, if_neg hRoot]
    have ht := C.parent_rowCopy (Nat.le_of_lt hz) hRoot hParent b
    rw [C.rowCopy_outside hOut, C.coordinates.parentCopy_good b hGood] at ht
    exact ht

theorem good_blocker_value (C : Context) (oldTop newTop : Nat → Nat)
    (hPrefixTop : ∀ s, s < C.coordinates.x → oldTop s = newTop s)
    (hUpper : C.UpperFixed oldTop newTop) {r z p : Nat}
    (hz : z < C.coordinates.x) (b : Nat)
    (hParent : (C.mountain.row r).parent z = some p) (hGood : p < C.coordinates.y) :
    value C.mountain oldTop r z = value C.toRowMountain newTop r (C.blockerCopy b z) := by
  by_cases hRoot : z = C.coordinates.y
  · rw [blockerCopy, if_pos hRoot, ← hRoot]
    exact C.value_original_prefix_eq oldTop newTop hPrefixTop hz r
  · rw [blockerCopy, if_neg hRoot]
    by_cases hBefore : z < C.coordinates.y
    · rw [C.coordinates.parentCopy_good b hBefore]
      exact C.value_original_prefix_eq oldTop newTop hPrefixTop hz r
    · exact C.value_tail_eq_from_upperFixed oldTop newTop
        (fun q hq => hPrefixTop q (by have := C.coordinates.root_lt_last; omega))
        hUpper (by omega) hz hParent hGood b r (Nat.le_refl _)

/-- The row used in sparse NS recovery is the actual numerical reconstruction
of the specified graph; its parent inequalities follow from positive sums. -/
def reconstructedRow (C : Context) (top : Nat → Nat) (hTop : ∀ c, 0 < top c) (r : Nat) : Numeric.Row where
  value := value C.toRowMountain top r
  forest := C.row r
  parent_values hp := ⟨value_pos C.toRowMountain top hTop (C.parent_endpoint hp),
    parent_value_lt C.toRowMountain top hTop hp⟩

/-- Complete local sparse NS recovery in the good-parent branch. Both the
ordinary blocker and the `z=y` original-root exception are transported here.
The only new-row correctness assumption is the strict already-processed
column prefix, exactly the induction hypothesis used by a row reconstruction. -/
theorem restrictedParent_good_copy_of_blocker (C : Context) (oldTop newTop : Nat → Nat)
    (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → oldTop s = newTop s)
    (hUpper : C.UpperFixed oldTop newTop)
    {u s q p z : Nat} (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hQ : (C.mountain.row u).parent s = some q)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hGood : p < C.coordinates.y)
    (hZ : z = q ∨ (C.mountain.row (u+1)).Ancestor z q)
    (hZParent : (C.mountain.row (u+1)).parent z = some p)
    (hOldUpper : value C.mountain oldTop (u+1) s ≤ value C.mountain oldTop (u+1) z)
    (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some p := by
  have hOut := C.not_inCone_of_good_parent hs hP hGood
  have hNewP := C.parent_rowCopy (Nat.le_of_lt hx) (by omega) hP b
  rw [C.rowCopy_outside hOut, C.coordinates.parentCopy_good b hGood] at hNewP
  have hNewQ := C.parent_rowCopy (Nat.le_of_lt hx) (by omega) hQ b
  rw [C.rowCopy_outside hOut] at hNewQ
  have hQLt := (C.mountain.row u).parent_left hQ
  have hZLt : z < C.coordinates.x := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hNewPath := C.good_blocker_path (by omega) b hZ hZParent hGood
  have hNewZParent := C.good_blocker_parent hZLt b hZParent hGood
  have hTargetValue := C.value_tail_eq_from_upperFixed oldTop newTop
    (fun q hq => hPrefixTop q (by have := C.coordinates.root_lt_last; omega))
    hUpper hs hx hP hGood b (u+1) (Nat.le_refl _)
  have hWitnessValue := C.good_blocker_value oldTop newTop hPrefixTop hUpper hZLt b hZParent hGood
  have hNewUpper : value C.toRowMountain newTop (u+1) (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop (u+1) (C.blockerCopy b z) := by
    rw [← hTargetValue, ← hWitnessValue]
    exact hOldUpper
  exact Numeric.restrictedParent_eq_of_blocker (C.reconstructedRow newTop hPositive (u+1))
    (C.row u) hNewQ hNewP (C.nested_succ u hNewP) hPrefix hNewPath hNewZParent hNewUpper

/-- The old blocker is produced by the old row's actual sparse NS equation.
No blocker witness or inequality is assumed by this public recovery theorem. -/
theorem restrictedParent_good_copy (C : Context) (oldTop newTop : Nat → Nat)
    (hOldPositive : ∀ c, 0 < oldTop c) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → oldTop s = newTop s)
    (hUpper : C.UpperFixed oldTop newTop) {u s p : Nat}
    (hOldCanonical : ∀ i, Numeric.restrictedParent (C.mountain.row u)
      (value C.mountain oldTop (u+1)) i = (C.mountain.row (u+1)).parent i)
    (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hGood : p < C.coordinates.y)
    (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some p := by
  have ha := C.mountain.nested_succ u hP
  cases hQ : (C.mountain.row u).parent s with
  | none =>
      cases ha with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      by_cases hEqual : p = q
      · subst q
        have hOut := C.not_inCone_of_good_parent hs hP hGood
        have hNewP := C.parent_rowCopy (Nat.le_of_lt hx) (by omega) hP b
        rw [C.rowCopy_outside hOut, C.coordinates.parentCopy_good b hGood] at hNewP
        have hNewQ := C.parent_rowCopy (Nat.le_of_lt hx) (by omega) hQ b
        rw [C.rowCopy_outside hOut, C.coordinates.parentCopy_good b hGood] at hNewQ
        exact Numeric.restrictedParent_eq_of_direct_parent
          (C.reconstructedRow newTop hPositive (u+1)) (C.row u) hNewP hNewQ
      · have hQLive : u+1 ≤ C.mountain.height q := by
          rcases ancestor_parent_or_eq (C.mountain.row u) ha hQ with hPath | he
          · cases hPath with
            | direct hp => have := C.mountain.parent_source hp; omega
            | step _ hp => have := C.mountain.parent_source hp; omega
          · rw [← he]
            exact C.mountain.parent_endpoint hP
        have hQPos := value_pos C.mountain oldTop hOldPositive hQLive
        have hSparseP : Numeric.restrictedParent (C.mountain.row u)
            (value C.mountain oldTop (u+1)) s = some p := (hOldCanonical s).trans hP
        obtain ⟨z, hZ, hZP, hLe⟩ := Numeric.restrictedParent_exists_blocker
          (C.mountain.row u) (value C.mountain oldTop (u+1)) hQ hSparseP hEqual hQPos
        have hForest : (Numeric.select (C.mountain.row u) (value C.mountain oldTop (u+1))).forest =
            C.mountain.row (u+1) := Numeric.parentForest_eq_of_parent_eq _ _ hOldCanonical
        rw [hForest] at hZ
        rw [hOldCanonical z] at hZP
        exact C.restrictedParent_good_copy_of_blocker oldTop newTop hPositive hPrefixTop hUpper
          hs hx hQ hP hGood hZ hZP hLe b hPrefix

/-- Specialization to an actual original numerical mountain: the old-row NS
equation and old top positivity are proved by the existing numeric round trip. -/
theorem restrictedParent_good_copy_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hUpper : C.UpperFixed (Numeric.topValue base) newTop) {u s p : Nat}
    (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hGood : p < C.coordinates.y)
    (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some p := by
  apply C.restrictedParent_good_copy (Numeric.topValue base) newTop
    (fun c => Numeric.topValue_pos base (hBase c)) hPositive hPrefixTop hUpper
    (u := u) (s := s) (p := p) ?_ hs hx hP hGood b hPrefix
  intro i
  rw [hMountain]
  exact restrictedParent_numeric_reconstruction base hBase u i

/-- The nontrivial bad-parent branch below the root floor. The copied blocker
inequality is derived from actual depth transport and the upper top-value B
property; it is not supplied as an assumption. -/
theorem restrictedParent_bad_low_copy_of_blocker (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hOldPositive : ∀ c, 0 < oldTop c) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder oldTop newTop)
    (hOldCanonical : ∀ r i, Numeric.restrictedParent (C.mountain.row r)
      (value C.mountain oldTop (r+1)) i = (C.mountain.row (r+1)).parent i)
    {u s q p z : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hLow : u+1 < C.floor)
    (hQ : (C.mountain.row u).parent s = some q)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (hZ : z = q ∨ (C.mountain.row (u+1)).Ancestor z q)
    (hZParent : (C.mountain.row (u+1)).parent z = some p)
    (hOldUpper : value C.mountain oldTop (u+1) s ≤ value C.mountain oldTop (u+1) z)
    (b : Nat)
    (hHigher : ∀ r, u+1 ≤ r → ∀ i,
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have hQLt := (C.mountain.row u).parent_left hQ
  have hZLt : z < s := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hPZLt := (C.mountain.row (u+1)).parent_left hZParent
  have hZAfter : C.coordinates.y < z := by omega
  have hInitial : (C.mountain.row (u+1)).parent s = (C.mountain.row (u+1)).parent z :=
    hP.trans hZParent.symm
  have hOldNext : value C.mountain oldTop (u+1+1) s ≤ value C.mountain oldTop (u+1+1) z := by
    rw [value_recurrence C.mountain oldTop hP, value_recurrence C.mountain oldTop hZParent] at hOldUpper
    omega
  have hOldKey := (keyLEFrom_iff_value_le C.mountain oldTop hOldPositive (u+1)
    (fun r _ => hOldCanonical r) (C.mountain.parent_source hP)
    (C.mountain.parent_source hZParent) hInitial).mpr hOldNext
  have hNewKey := C.keyLE_low_start hRegular oldTop newTop hUpper hZAfter hZLt hx
    (C.mountain.parent_source hP) (C.mountain.parent_source hZParent) hLow hInitial hOldKey b
  have hNewP := C.parent_rowCopy hx (by omega) hP b
  have hNewZP := C.parent_rowCopy (by omega) (by omega) hZParent b
  have hNewQ := C.parent_rowCopy hx (by omega) hQ b
  rw [C.rowCopy_low hLow] at hNewP hNewZP
  rw [C.rowCopy_low (by omega : u < C.floor)] at hNewQ
  have hNewNext := (keyLEFrom_iff_value_le C.toRowMountain newTop hPositive (u+1)
    hHigher (C.parent_source hNewP) (C.parent_source hNewZP) (hNewP.trans hNewZP.symm)).mp hNewKey
  have hNewUpper : value C.toRowMountain newTop (u+1) (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop (u+1) (C.coordinates.parentCopy b z) := by
    rw [value_recurrence C.toRowMountain newTop hNewP,
      value_recurrence C.toRowMountain newTop hNewZP]
    omega
  have hNewPath : C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
      (C.row (u+1)).Ancestor (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
    rcases hZ with he | ha
    · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
    · exact Or.inr (C.low_ancestor_copy hLow ha (by omega) b)
  exact Numeric.restrictedParent_eq_of_blocker (C.reconstructedRow newTop hPositive (u+1))
    (C.row u) hNewQ hNewP (C.nested_succ u hNewP) hPrefix hNewPath hNewZP hNewUpper

theorem restrictedParent_bad_low_copy (C : Context) (hRegular : C.DepthRegular)
    (oldTop newTop : Nat → Nat) (hOldPositive : ∀ c, 0 < oldTop c) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder oldTop newTop)
    (hOldCanonical : ∀ r i, Numeric.restrictedParent (C.mountain.row r)
      (value C.mountain oldTop (r+1)) i = (C.mountain.row (r+1)).parent i)
    {u s p : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hLow : u+1 < C.floor)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (b : Nat)
    (hHigher : ∀ r, u+1 ≤ r → ∀ i,
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have ha := C.mountain.nested_succ u hP
  cases hQ : (C.mountain.row u).parent s with
  | none =>
      cases ha with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      by_cases hEqual : p = q
      · subst q
        have hNewP := C.parent_rowCopy hx (by omega) hP b
        have hNewQ := C.parent_rowCopy hx (by omega) hQ b
        rw [C.rowCopy_low hLow] at hNewP
        rw [C.rowCopy_low (by omega : u < C.floor)] at hNewQ
        exact Numeric.restrictedParent_eq_of_direct_parent
          (C.reconstructedRow newTop hPositive (u+1)) (C.row u) hNewP hNewQ
      · have hQLive : u+1 ≤ C.mountain.height q := by
          rcases ancestor_parent_or_eq (C.mountain.row u) ha hQ with hPath | he
          · cases hPath with
            | direct hp => have := C.mountain.parent_source hp; omega
            | step _ hp => have := C.mountain.parent_source hp; omega
          · rw [← he]
            exact C.mountain.parent_endpoint hP
        have hQPos := value_pos C.mountain oldTop hOldPositive hQLive
        have hSparseP : Numeric.restrictedParent (C.mountain.row u)
            (value C.mountain oldTop (u+1)) s = some p := (hOldCanonical u s).trans hP
        obtain ⟨z, hZ, hZP, hLe⟩ := Numeric.restrictedParent_exists_blocker
          (C.mountain.row u) (value C.mountain oldTop (u+1)) hQ hSparseP hEqual hQPos
        have hForest : (Numeric.select (C.mountain.row u) (value C.mountain oldTop (u+1))).forest =
            C.mountain.row (u+1) := Numeric.parentForest_eq_of_parent_eq _ _ (hOldCanonical u)
        rw [hForest] at hZ
        rw [hOldCanonical u z] at hZP
        exact C.restrictedParent_bad_low_copy_of_blocker hRegular oldTop newTop hOldPositive hPositive
          hUpper hOldCanonical hs hx hLow hQ hP hBad hZ hZP hLe b hHigher hPrefix

theorem restrictedParent_bad_low_copy_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop) {u s p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hLow : u+1 < C.floor)
    (hP : (C.mountain.row (u+1)).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (b : Nat)
    (hHigher : ∀ r, u+1 ≤ r → ∀ i,
      Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1)) i = C.parent (u+1) i) :
    Numeric.restrictedParent (C.row u) (value C.toRowMountain newTop (u+1))
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  apply C.restrictedParent_bad_low_copy (C.depthRegular_numeric base hBase hMountain)
    (Numeric.topValue base) newTop (fun c => Numeric.topValue_pos base (hBase c)) hPositive hUpper
    ?_ hs hx hLow hP hBad b hHigher hPrefix
  intro r i
  rw [hMountain]
  exact restrictedParent_numeric_reconstruction base hBase r i

#print axioms value_tail_eq_from_upperFixed
#print axioms good_blocker_path
#print axioms good_blocker_value
#print axioms restrictedParent_good_copy_of_blocker
#print axioms restrictedParent_good_copy
#print axioms restrictedParent_good_copy_numeric
#print axioms restrictedParent_bad_low_copy_numeric

end OneY.LowerCopy.Context
