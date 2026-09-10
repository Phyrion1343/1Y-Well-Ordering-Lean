import OneY.TerminalCopyBottom

/-! # Bottom-row blockers against the copied inherited frame -/

namespace OneY.TerminalCopy.Context

def bottomBlockerCopy (C : Context) (b z : Nat) : Nat :=
  if z = C.coordinates.y ∧ 0 < C.level then z else C.coordinates.parentCopy b z

theorem root_ancestor_copied_root_low (C : Context) (hr : 0 < C.level) (b : Nat) :
    C.coordinates.y = C.coordinates.parentCopy b C.coordinates.y ∨
      (C.row 0).Ancestor C.coordinates.y (C.coordinates.parentCopy b C.coordinates.y) := by
  induction b with
  | zero => exact Or.inl (C.coordinates.parentCopy_zero _).symm
  | succ b ih =>
      have hStep := C.low_ancestor_same_block hr (C.root_ancestor_last (Nat.zero_le _))
        (Nat.le_refl _) (Nat.le_refl _) b
      have hTarget : C.coordinates.parentCopy (b+1) C.coordinates.y =
          C.coordinates.x+b*C.coordinates.length := by
        rw [C.coordinates.parentCopy_bad _ (Nat.le_refl _), C.root_copy_succ_eq]
      rw [hTarget]
      have hSource : C.coordinates.parentCopy b C.coordinates.y = C.coordinates.y+b*C.coordinates.length :=
        C.coordinates.parentCopy_bad _ (Nat.le_refl _)
      rw [← hSource] at hStep
      exact Or.inr (by
        rcases ih with he | ha
        · rw [← he] at hStep; exact hStep
        · exact ha.trans hStep)

theorem bottom_good_blocker_path (C : Context) {z q : Nat}
    (hq : q < C.coordinates.x) (b : Nat)
    (hZ : z = q ∨ (C.mountain.row 0).Ancestor z q) :
    C.bottomBlockerCopy b z = C.coordinates.parentCopy b q ∨
      (C.row 0).Ancestor (C.bottomBlockerCopy b z) (C.coordinates.parentCopy b q) := by
  have hCopied : C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
      (C.row 0).Ancestor (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
    rcases hZ with he | ha
    · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
    · exact Or.inr (C.ancestor_parentCopy ha hq b)
  unfold bottomBlockerCopy
  split
  · rename_i hSpecial
    rcases C.root_ancestor_copied_root_low hSpecial.2 b with he | ha
    · rw [hSpecial.1] at hCopied
      rw [hSpecial.1, he]; exact hCopied
    · rw [hSpecial.1]
      rcases hCopied with ht | ht
      · rw [hSpecial.1] at ht
        exact Or.inr (by rw [← ht]; exact ha)
      · rw [hSpecial.1] at ht
        exact Or.inr (ha.trans ht)
  · exact hCopied

theorem bottom_good_blocker_parent (C : Context) {z p : Nat}
    (hz : z < C.coordinates.x) (b : Nat) (hP : (C.mountain.row 0).parent z = some p)
    (hGood : p < C.coordinates.y) : C.parent 0 (C.bottomBlockerCopy b z) = some p := by
  unfold bottomBlockerCopy
  split
  · exact (C.parent_original hz 0).trans hP
  · rename_i hNotSpecial
    by_cases hroot : z = C.coordinates.y
    · subst z
      have hLevel : C.level = 0 := by omega
      rw [C.coordinates.parentCopy_bad _ (Nat.le_refl _), C.parent_root_copy_high (by omega) b]
      exact hP
    · rw [C.parent_parentCopy_nonroot hz hroot b 0, hP, Option.map_some,
        C.coordinates.parentCopy_good b hGood]

theorem bottom_good_blocker_value (C : Context) (top : Nat → Nat) {z p : Nat}
    (hz : z < C.coordinates.x) (b : Nat) (hP : (C.mountain.row 0).parent z = some p)
    (hGood : p < C.coordinates.y) :
    Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue top) 0 (C.bottomBlockerCopy b z) =
      Reconstruction.value C.mountain top 0 z := by
  unfold bottomBlockerCopy
  split
  · exact C.value_original top hz 0
  · rename_i hNotSpecial
    by_cases hroot : z = C.coordinates.y
    · have hLevel : C.level = 0 := by omega
      rw [C.value_above top (by omega)]
      have he : C.ordinaryContext.source0 (C.coordinates.parentCopy b z) = z :=
        C.ordinaryContext.source0_parentCopy hz b
      rw [he]
    · exact C.value_copy_of_good_base_parent top hz hroot (by
        intro q hq
        have he := Option.some.inj (hP.symm.trans hq)
        omega) b 0

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_external_after_blocker (a : RootedRow) {K d x y s q p z : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (hs : y < s) (hx : s < x) (hQ : F.parent s = some q)
    (hP : (layers a K).row.forest.parent s = some p)
    (hz : y < z) (hZ : z = q ∨ (layers a K).row.forest.Ancestor z q)
    (hZP : (layers a K).row.forest.parent z = some p)
    (hLe : (layers a K).row.value s ≤ (layers a K).row.value z) (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.parentCopy b s →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) =
        some ((badAtTerminalContext a hbad).coordinates.parentCopy b p) := by
  let C := badAtTerminalContext a hbad
  have hQLt := F.parent_left hQ
  have hZLt : z < s := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_parentCopy_nonroot hx (by change s ≠ y; omega) b 0]
    change ((layers a K).row.forest.parent s).map _ = _
    rw [hP, Option.map_some]
  have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
    rw [C.parent_parentCopy_nonroot (by change z < x; omega) (by change z ≠ y; omega) b 0]
    change ((layers a K).row.forest.parent z).map _ = _
    rw [hZP, Option.map_some]
  have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b q) := by
    rw [FrameCopy.parent_nonroot C.coordinates F (Nat.le_of_lt hx) (by change s ≠ y; omega) b,
      hQ, Option.map_some]
  have hNewPath : C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
      (C.row 0).Ancestor (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
    rcases hZ with he | ha
    · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
    · exact Or.inr (C.ancestor_parentCopy (r := 0) ha (by change q < x; omega) b)
  exact restrictedParent_eq_of_blocker (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F)
    hNewQ hNewP (C.zero_refines_frameCopy F (badAtTerminal_bottom_refines a hbad F hSelected) hNewP)
    hPrefix hNewPath hNewZP
    (badAtTerminalBase_order_of_common_parent a hbad hs hx hz (by omega) hP hZP hLe b)

theorem badAtTerminal_external_good_blocker (a : RootedRow) {K d x y s q p z : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (hs : y < s) (hx : s < x) (hQ : F.parent s = some q)
    (hP : (layers a K).row.forest.parent s = some p) (hGood : p < y)
    (hZ : z = q ∨ (layers a K).row.forest.Ancestor z q)
    (hZP : (layers a K).row.forest.parent z = some p)
    (hLe : (layers a K).row.value s ≤ (layers a K).row.value z) (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.parentCopy b s →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) = some p := by
  let C := badAtTerminalContext a hbad
  have hQLt := F.parent_left hQ
  have hZLt : z < x := by
    rcases hZ with he | ha
    · omega
    · have := ha.lt; omega
  have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some p := by
    rw [C.parent_parentCopy_nonroot hx (by change s ≠ y; omega) b 0]
    change ((layers a K).row.forest.parent s).map _ = _
    rw [hP, Option.map_some, C.coordinates.parentCopy_good b hGood]
  have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b q) := by
    rw [FrameCopy.parent_nonroot C.coordinates F (Nat.le_of_lt hx) (by change s ≠ y; omega) b,
      hQ, Option.map_some]
  have hSValue := badAtTerminalBase_fixed_of_good_parent a hbad hs hx (by
    intro q hq
    have := Option.some.inj (hP.symm.trans hq)
    omega) b
  have hZValue : (badAtTerminalBase a hbad).value (C.bottomBlockerCopy b z) = (layers a K).row.value z := by
    change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row))
      0 (C.bottomBlockerCopy b z) = _
    rw [C.bottom_good_blocker_value (topValue (layers a K).row) hZLt b hZP hGood]
    exact Reconstruction.value_numeric_base (layers a K).row (layers a K).positive z
  have hNewUpper : (badAtTerminalBase a hbad).value (C.coordinates.parentCopy b s) ≤
      (badAtTerminalBase a hbad).value (C.bottomBlockerCopy b z) := by
    rw [hSValue, hZValue]
    exact hLe
  exact restrictedParent_eq_of_blocker (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F)
    hNewQ hNewP (C.zero_refines_frameCopy F (badAtTerminal_bottom_refines a hbad F hSelected) hNewP)
    hPrefix (C.bottom_good_blocker_path (by change q < x; omega) b hZ)
    (C.bottom_good_blocker_parent hZLt b hZP hGood) hNewUpper

theorem badAtTerminal_external_nonroot_some (a : RootedRow) {K d x y s p : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (hs : y < s) (hx : s < x) (hP : (layers a K).row.forest.parent s = some p) (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.parentCopy b s →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) =
        some ((badAtTerminalContext a hbad).coordinates.parentCopy b p) := by
  let C := badAtTerminalContext a hbad
  have hSparse := (hSelected s).trans hP
  have hAnc := badAtTerminal_bottom_refines a hbad F hSelected hP
  cases hQ : F.parent s with
  | none =>
      cases hAnc with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      by_cases he : p = q
      · subst q
        have hNewP : C.parent 0 (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
          rw [C.parent_parentCopy_nonroot hx (by change s ≠ y; omega) b 0]
          change ((layers a K).row.forest.parent s).map _ = _
          rw [hP, Option.map_some]
        have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.parentCopy b s) = some (C.coordinates.parentCopy b p) := by
          rw [FrameCopy.parent_nonroot C.coordinates F (Nat.le_of_lt hx) (by change s ≠ y; omega) b,
            hQ, Option.map_some]
        exact restrictedParent_eq_of_direct_parent (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F) hNewP hNewQ
      · obtain ⟨z, hZ, hZP, hLe⟩ := restrictedParent_exists_blocker F _ hQ hSparse he ((layers a K).positive q)
        have hForest : (select F (layers a K).row.value).forest = (layers a K).row.forest :=
          parentForest_eq_of_parent_eq _ _ hSelected
        rw [hForest] at hZ
        rw [hSelected z] at hZP
        by_cases hBad : y ≤ p
        · have hpz := (layers a K).row.forest.parent_left hZP
          exact badAtTerminal_external_after_blocker a hbad F hSelected hs hx hQ hP
            (by omega) hZ hZP hLe b hPrefix
        · have hGood : p < y := by omega
          rw [C.coordinates.parentCopy_good b hGood]
          exact badAtTerminal_external_good_blocker a hbad F hSelected hs hx hQ hP hGood hZ hZP hLe b hPrefix

theorem badAtTerminalBase_none_eq_one (a : RootedRow) {K d x y c : Nat}
    (hbad : BadAt a K d x y) (hp : (badAtTerminalContext a hbad).parent 0 c = none) :
    (badAtTerminalBase a hbad).value c = 1 := by
  let C := badAtTerminalContext a hbad
  have hh : C.toRowMountain.height c = 0 := by
    have h := (C.toRowMountain.parent_none_iff 0 c).mp hp
    omega
  have holdH := C.height_parentCopy (C.ordinaryContext.source0_bounds c) (C.ordinaryContext.block0 c)
  have he : C.coordinates.parentCopy (C.ordinaryContext.block0 c) (C.ordinaryContext.source0 c) = c :=
    C.ordinaryContext.parentCopy_coordinates c
  rw [he] at holdH
  have hOldZero : height (layers a K).row (C.ordinaryContext.source0 c) = 0 := holdH.symm.trans hh
  change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 c = 1
  rw [← hh, Reconstruction.value_top]
  exact topValue_eq_one_of_height_zero (layers a K).row (layers a K).positive (layers a K).rootsOne hOldZero

theorem badAtTerminal_external_none (a : RootedRow) {K d x y c : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hp : (badAtTerminalContext a hbad).parent 0 c = none) :
    restrictedParent F (badAtTerminalBase a hbad).value c = none := by
  apply (restrictedParent_none_iff _ _ _).mpr
  intro q _ hq
  rw [badAtTerminalBase_none_eq_one a hbad hp]
  exact hq

theorem badAtTerminal_external_prefix (a : RootedRow) {K d x y c : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ q, restrictedParent F (layers a K).row.value q = (layers a K).row.forest.parent q)
    (hc : c < x) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value c = (badAtTerminalContext a hbad).parent 0 c := by
  let C := badAtTerminalContext a hbad
  rw [C.parent_original hc 0]
  change _ = (layers a K).row.forest.parent c
  rw [← hSelected c]
  apply restrictedParent_prefix_congr _ _ _ _ hc
  · intro q hq
    exact FrameCopy.parent_original C.coordinates F (Nat.le_of_lt hq)
  · intro q hq
    change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 q = _
    rw [C.value_original (topValue (layers a K).row) hq 0]
    exact Reconstruction.value_numeric_base (layers a K).row (layers a K).positive q

theorem badAtTerminal_external_nonroot (a : RootedRow) {K d x y s : Nat}
    (hbad : BadAt a K d x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (hs : y < s) (hx : s < x) (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.parentCopy b s →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.parentCopy b s) =
        (badAtTerminalContext a hbad).parent 0 ((badAtTerminalContext a hbad).coordinates.parentCopy b s) := by
  let C := badAtTerminalContext a hbad
  have hParent : C.parent 0 (C.coordinates.parentCopy b s) =
      ((layers a K).row.forest.parent s).map (C.coordinates.parentCopy b) :=
    C.parent_parentCopy_nonroot hx (by change s ≠ y; omega) b 0
  cases hp : (layers a K).row.forest.parent s with
  | none =>
      have hn : C.parent 0 (C.coordinates.parentCopy b s) = none := by rw [hParent, hp]; rfl
      rw [hn]
      exact badAtTerminal_external_none a hbad _ hn
  | some p =>
      rw [hParent, hp, Option.map_some]
      exact badAtTerminal_external_nonroot_some a hbad F hSelected hs hx hp b hPrefix

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminal_external_after_blocker
#print axioms OneY.Numeric.badAtTerminal_external_nonroot
#print axioms OneY.Numeric.badAtTerminalBase_none_eq_one
