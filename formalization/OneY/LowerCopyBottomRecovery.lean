import OneY.LowerCopyBottom

/-! # Sparse NS recovery against the transported inherited bottom frame -/

namespace OneY.LowerCopy.Context

open Reconstruction

theorem bottom_refines_of_selected (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c) :
    (C.mountain.row 0).Refines F := by
  intro c p hp
  rw [hMountain] at hp
  have hActual : base.forest.parent c = some p := hp
  exact ParentForest.ancestor_of_zeroY (Numeric.restrictedParent_spec F base.value ((hSelected c).trans hActual)).1

theorem bottom_value_le_copy_of_common_parent (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hFinite : ∀ r i, Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    {s z p : Nat} (hz : C.coordinates.y < z) (hZS : z < s) (hsx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row 0).parent s = some p) (hZP : (C.mountain.row 0).parent z = some p)
    (hLe : base.value s ≤ base.value z) (b : Nat) :
    value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop 0 (C.coordinates.parentCopy b z) := by
  have hOldLe : value C.mountain (Numeric.topValue base) 0 s ≤ value C.mountain (Numeric.topValue base) 0 z := by
    rw [hMountain, value_numeric_base, value_numeric_base]
    exact hLe
  have hOldNext : value C.mountain (Numeric.topValue base) 1 s ≤ value C.mountain (Numeric.topValue base) 1 z := by
    rw [value_recurrence C.mountain (Numeric.topValue base) hP,
      value_recurrence C.mountain (Numeric.topValue base) hZP] at hOldLe
    exact Nat.le_of_add_le_add_right hOldLe
  have hOldCan : ∀ r i, Numeric.restrictedParent (C.mountain.row r)
      (value C.mountain (Numeric.topValue base) (r+1)) i = (C.mountain.row (r+1)).parent i := by
    intro r i
    rw [hMountain]
    exact restrictedParent_numeric_reconstruction base hBase r i
  have hOldKey := (keyLEFrom_iff_value_le C.mountain (Numeric.topValue base)
    (fun c => Numeric.topValue_pos base (hBase c)) 0 (fun r _ => hOldCan r)
    (C.mountain.parent_source hP) (C.mountain.parent_source hZP) (hP.trans hZP.symm)).mpr hOldNext
  have hNewKey := C.keyLE_bottom_parent (C.depthRegular_numeric base hBase hMountain)
    (Numeric.topValue base) newTop hUpper hz hZS hsx hP hZP hOldKey b
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_zero_parentCopy (by omega) hsx b, hP, Option.map_some]
  have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_zero_parentCopy hz (by omega) b, hZP, Option.map_some]
  have hNewNext := (keyLEFrom_iff_value_le C.toRowMountain newTop hPositive 0 (fun r _ => hFinite r)
    (C.parent_source hNewP) (C.parent_source hNewZP) (hNewP.trans hNewZP.symm)).mp hNewKey
  rw [value_recurrence C.toRowMountain newTop hNewP, value_recurrence C.toRowMountain newTop hNewZP]
  exact Nat.add_le_add_right hNewNext _

theorem restrictedParent_bottom_bad_of_blocker (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hFinite : ∀ r i, Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    {s q p z : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hQ : F.parent s = some q)
    (hP : (C.mountain.row 0).parent s = some p) (hBad : C.coordinates.y ≤ p)
    (hZ : z = q ∨ (C.mountain.row 0).Ancestor z q)
    (hZP : (C.mountain.row 0).parent z = some p) (hLe : base.value s ≤ base.value z)
    (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0) i = C.parent 0 i) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0)
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have hQLt := F.parent_left hQ
  have hZLt : z < s := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hPZLt := (C.mountain.row 0).parent_left hZP
  have hZAfter : C.coordinates.y < z := by omega
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_zero_parentCopy hs hx b, hP, Option.map_some]
  have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_zero_parentCopy hZAfter (by omega) b, hZP, Option.map_some]
  have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b q) := by
    rw [FrameCopy.parent_nonroot C.coordinates F hx (by omega) b, hQ, Option.map_some]
  have hNewPath : C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
      (C.row 0).Ancestor (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
    rcases hZ with he | ha
    · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
    · rw [C.zero_forest_eq_frameCopy]
      exact Or.inr (FrameCopy.ancestor_copy C.coordinates (C.mountain.row 0) C.root_ancestor_last_zero ha (by omega) b)
  have hNewUpper := C.bottom_value_le_copy_of_common_parent base hBase hMountain newTop hPositive hUpper hFinite
    hZAfter hZLt hx hP hZP hLe b
  exact Numeric.restrictedParent_eq_of_blocker (C.reconstructedRow newTop hPositive 0)
    (FrameCopy.forest C.coordinates F) hNewQ hNewP
    (C.zero_refines_frameCopy F (C.bottom_refines_of_selected base hBase hMountain F hSelected) hNewP)
    hPrefix hNewPath hNewZP hNewUpper

theorem restrictedParent_bottom_good_of_blocker (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    {s q p z : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hQ : F.parent s = some q)
    (hP : (C.mountain.row 0).parent s = some p) (hGood : p < C.coordinates.y)
    (hZ : z = q ∨ (C.mountain.row 0).Ancestor z q)
    (hZP : (C.mountain.row 0).parent z = some p) (hLe : base.value s ≤ base.value z)
    (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0) i = C.parent 0 i) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0)
      (C.coordinates.parentCopy b s) = some p := by
  have hQLt := F.parent_left hQ
  have hZLt : z < C.coordinates.x := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hOut := C.not_inCone_of_good_parent hs hP hGood
  have hsx : s < C.coordinates.x := by
    by_cases he : s = C.coordinates.x
    · subst s; exact False.elim (hOut C.last_inCone)
    · omega
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some p := by
    rw [C.parent_zero_parentCopy hs hx b, hP, Option.map_some, C.coordinates.parentCopy_good b hGood]
  have hNewZP := C.good_blocker_parent hZLt b hZP hGood
  have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b q) := by
    rw [FrameCopy.parent_nonroot C.coordinates F hx (by omega) b, hQ, Option.map_some]
  have hSValue := C.value_tail_eq_from_upperFixed (Numeric.topValue base) newTop
    (fun q hq => hPrefixTop q (by have := C.coordinates.root_lt_last; omega)) hFixed hs hsx hP hGood b 0 (Nat.le_refl _)
  have hZValue := C.good_blocker_value (Numeric.topValue base) newTop hPrefixTop hFixed hZLt b hZP hGood
  have hNewUpper : value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) ≤
      value C.toRowMountain newTop 0 (C.blockerCopy b z) := by
    rw [← hSValue, ← hZValue, hMountain, value_numeric_base, value_numeric_base]
    exact hLe
  exact Numeric.restrictedParent_eq_of_blocker (C.reconstructedRow newTop hPositive 0)
    (FrameCopy.forest C.coordinates F) hNewQ hNewP
    (C.zero_refines_frameCopy F (C.bottom_refines_of_selected base hBase hMountain F hSelected) hNewP)
    hPrefix (C.good_blocker_path (by omega) b hZ hZP hGood) hNewZP hNewUpper

theorem restrictedParent_bottom_some (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hFinite : ∀ r i, Numeric.restrictedParent (C.row r) (value C.toRowMountain newTop (r+1)) i = C.parent (r+1) i)
    {s p : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row 0).parent s = some p) (b : Nat)
    (hPrefix : ∀ i, i < C.coordinates.parentCopy b s →
      Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0) i = C.parent 0 i) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0)
      (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
  have hSelected' : ∀ i, Numeric.restrictedParent F base.value i = (C.mountain.row 0).parent i := by
    intro i
    rw [hMountain]
    exact hSelected i
  have hSparse := (hSelected' s).trans hP
  have ha := C.bottom_refines_of_selected base hBase hMountain F hSelected hP
  cases hQ : F.parent s with
  | none =>
      cases ha with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      by_cases he : p = q
      · subst q
        have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
          rw [C.parent_zero_parentCopy hs hx b, hP, Option.map_some]
        have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
          rw [FrameCopy.parent_nonroot C.coordinates F hx (by omega) b, hQ, Option.map_some]
        exact Numeric.restrictedParent_eq_of_direct_parent (C.reconstructedRow newTop hPositive 0)
          (FrameCopy.forest C.coordinates F) hNewP hNewQ
      · obtain ⟨z, hZ, hZP, hLe⟩ := Numeric.restrictedParent_exists_blocker F base.value hQ hSparse he (hBase q)
        have hForest : (Numeric.select F base.value).forest = C.mountain.row 0 :=
          Numeric.parentForest_eq_of_parent_eq _ _ hSelected'
        rw [hForest] at hZ
        rw [hSelected' z] at hZP
        by_cases hBad : C.coordinates.y ≤ p
        · exact C.restrictedParent_bottom_bad_of_blocker base hBase hMountain F hSelected newTop hPositive
            hUpper hFinite hs hx hQ hP hBad hZ hZP hLe b hPrefix
        · have hGood : p < C.coordinates.y := by omega
          rw [C.coordinates.parentCopy_good b hGood]
          exact C.restrictedParent_bottom_good_of_blocker base hBase hMountain F hSelected newTop hPositive
            hPrefixTop hFixed hs hx hQ hP hGood hZ hZP hLe b hPrefix

/-- Empty bottom parents are covered by the actual roots-one invariant. This
does not assert physical-row preservation for lifted empty finite cells. -/
theorem value_bottom_none_eq_one (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat) (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    {s : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row 0).parent s = none) (b : Nat) :
    value C.toRowMountain newTop 0 (C.coordinates.parentCopy b s) = 1 := by
  have hHeight : C.mountain.height s = 0 := by
    have := (C.mountain.parent_none_iff 0 s).mp hP
    omega
  have hOut : ¬ C.InCone s := by
    intro hCone
    have := C.height_lt_of_inCone hCone hs
    omega
  have hxStrict : s < C.coordinates.x := by
    by_cases he : s = C.coordinates.x
    · subst s; exact False.elim (hOut C.last_inCone)
    · omega
  have hNewHeight : C.toRowMountain.height (C.coordinates.parentCopy b s) = 0 := by
    change C.height _ = 0
    rw [C.height_parentCopy hx b, if_neg hOut, hHeight]
  have hPseudo : (Pseudo.forest C.mountain).parent s = none := (Pseudo.parent_none_iff C.mountain s).mpr hHeight
  have hTopEq := hFixed s hs hxStrict (by
    intro q hq
    have ha := ParentForest.ancestor_of_zeroY (Numeric.restrictedParent_spec _ _ hq).1
    cases ha with
    | direct hp => rw [hPseudo] at hp; contradiction
    | step _ hp => rw [hPseudo] at hp; contradiction) b
  have hBaseP : base.forest.parent s = none := by
    rw [hMountain] at hP
    exact hP
  have hTopOne : Numeric.topValue base s = 1 :=
    (Numeric.topValue_eq_of_no_parent base (hBase s) hBaseP).trans (hRoots s hBaseP)
  rw [← hNewHeight, value_top, ← hTopEq, hTopOne]

theorem restrictedParent_bottom_none (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (newTop : Nat → Nat)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    {s : Nat} (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hP : (C.mountain.row 0).parent s = none) (b : Nat) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0)
      (C.coordinates.parentCopy b s) = none := by
  apply (Numeric.restrictedParent_none_iff _ _ _).mpr
  intro q _ hq
  rw [C.value_bottom_none_eq_one base hBase hRoots hMountain newTop hFixed hs hx hP b]
  exact hq

theorem restrictedParent_bottom_original_prefix (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    {c : Nat} (hc : c < C.coordinates.x) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0) c = C.parent 0 c := by
  rw [Numeric.restrictedParent_agreesBelow (FrameCopy.forest C.coordinates F) F
    (value C.toRowMountain newTop 0) base.value C.coordinates.x
    (fun q hq => FrameCopy.parent_original C.coordinates F (Nat.le_of_lt hq))
    (fun q hq => by
      rw [← C.value_original_prefix_eq (Numeric.topValue base) newTop hPrefixTop hq 0,
        hMountain, value_numeric_base]) hc, hSelected c, C.parent_original (Nat.le_of_lt hc), hMountain]
  rfl

/-- Bottom recovery with no left-prefix or higher-row correctness hypothesis.
The remaining inputs are explicitly the upper layer's B/C and pseudo-top
bound, plus the old inherited-frame selection equation. -/
theorem restrictedParent_bottom_numeric (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hRoots : base.RootsOne)
    (hMountain : C.mountain = Numeric.mountain base hBase)
    (F : ParentForest) (hSelected : ∀ c, Numeric.restrictedParent F base.value c = base.forest.parent c)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hPrefixTop : ∀ s, s < C.coordinates.x → Numeric.topValue base s = newTop s)
    (hFixed : C.UpperFixed (Numeric.topValue base) newTop)
    (hUpper : C.UpperOrder (Numeric.topValue base) newTop)
    (hBound : PseudoTopBound C.toRowMountain newTop) (c : Nat) :
    Numeric.restrictedParent (FrameCopy.forest C.coordinates F) (value C.toRowMountain newTop 0) c = C.parent 0 c := by
  have hFinite := C.restrictedParent_next_numeric base hBase hMountain newTop hPositive hPrefixTop hFixed hUpper hBound
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases hOriginal : c < C.coordinates.x
      · exact C.restrictedParent_bottom_original_prefix base hBase hMountain F hSelected newTop hPrefixTop hOriginal
      · have hAfter : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
        have hs := C.coordinates.source_bounds c
        have he : C.coordinates.parentCopy (C.coordinates.block c) (C.coordinates.source c) = c := by
          rw [C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)]
          exact C.coordinates.encode_coordinates hAfter
        have hParent := C.parent_zero_parentCopy hs.1 hs.2 (C.coordinates.block c)
        rw [he] at hParent
        cases hp : (C.mountain.row 0).parent (C.coordinates.source c) with
        | none =>
            simp only [hp, Option.map_none] at hParent
            rw [hParent]
            have ht := C.restrictedParent_bottom_none base hBase hRoots hMountain F newTop hFixed
              hs.1 hs.2 hp (C.coordinates.block c)
            simpa only [he] using ht
        | some p =>
            simp only [hp, Option.map_some] at hParent
            rw [hParent]
            have ht := C.restrictedParent_bottom_some base hBase hMountain F hSelected newTop hPositive
              hPrefixTop hFixed hUpper hFinite hs.1 hs.2 hp (C.coordinates.block c)
              (by simpa only [he] using ih)
            simpa only [he] using ht

#print axioms bottom_value_le_copy_of_common_parent
#print axioms restrictedParent_bottom_bad_of_blocker
#print axioms restrictedParent_bottom_good_of_blocker
#print axioms restrictedParent_bottom_some
#print axioms restrictedParent_bottom_none
#print axioms restrictedParent_bottom_numeric

end OneY.LowerCopy.Context
