import OneY.TerminalCopySeamComparison

/-! # Actual external-frame selection at every terminal seam -/

namespace OneY.TerminalCopy.Context

theorem ordinary_source_seam (C : Context) (b : Nat) :
    C.ordinaryContext.source0 (C.coordinates.encode C.coordinates.x b) = C.coordinates.y := by
  have ht := C.ordinaryContext.source0_parentCopy C.coordinates.root_lt_last (b+1)
  have he : C.coordinates.parentCopy (b+1) C.coordinates.y = C.coordinates.encode C.coordinates.x b := by
    rw [C.coordinates.parentCopy_bad _ (Nat.le_refl _)]
    exact C.root_copy_succ_eq b
  change C.ordinaryContext.source0 (C.coordinates.parentCopy (b+1) C.coordinates.y) = _ at ht
  rwa [he] at ht

end OneY.TerminalCopy.Context

namespace OneY.Numeric

theorem badAtTerminal_external_seam_low (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (hLow : 0 < d) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.encode x b →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.encode x b) =
        (badAtTerminalContext a hbad).parent 0 ((badAtTerminalContext a hbad).coordinates.encode x b) := by
  let C := badAtTerminalContext a hbad
  have hRoot := C.root_ancestor_last (Nat.zero_le C.level)
  change (C.mountain.row 0).Ancestor y x at hRoot
  have hLastHeight : C.mountain.height x = d+1 := C.last_height
  obtain ⟨p, hP⟩ := C.mountain.parent_exists 0 x (by omega)
  have hBad : y ≤ p := by
    rcases ZeroY.Forest.ancestor_eq_or_below_parent hP (ParentForest.ancestor_to_zeroY hRoot) with he | ha
    · omega
    · have := ZeroY.Forest.ancestor_lt (C.mountain.row 0).parent_left ha; omega
  have hPbase : (layers a K).row.forest.parent x = some p := hP
  have hNewP : C.parent 0 (C.coordinates.encode x b) = some (C.coordinates.parentCopy b p) := by
    have he := C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hLow b
    change C.parent 0 (C.coordinates.encode x b) = ((C.mountain.row 0).parent x).map _ at he
    rw [he, hP, Option.map_some]
  rw [hNewP]
  have hAnc := badAtTerminal_bottom_refines a hbad F hSelected hP
  cases hQ : F.parent x with
  | none =>
      cases hAnc with
      | direct hp => rw [hQ] at hp; contradiction
      | step _ hp => rw [hQ] at hp; contradiction
  | some q =>
      have hQLt := F.parent_left hQ
      have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.encode x b) = some (C.coordinates.parentCopy b q) := by
        have he := FrameCopy.parent_encode C.coordinates F C.coordinates.root_lt_last (Nat.le_refl _) b
        change FrameCopy.parent C.coordinates F (C.coordinates.encode x b) = (F.parent x).map _ at he
        rw [he, hQ, Option.map_some]
      by_cases hDirect : p = q
      · subst q
        exact restrictedParent_eq_of_direct_parent (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F) hNewP hNewQ
      · obtain ⟨z, hZ, hZP, hLe⟩ := restrictedParent_exists_blocker F _ hQ ((hSelected x).trans hPbase)
          hDirect ((layers a K).positive q)
        have hForest : (select F (layers a K).row.value).forest = (layers a K).row.forest :=
          parentForest_eq_of_parent_eq _ _ hSelected
        rw [hForest] at hZ
        rw [hSelected z] at hZP
        have hZLt : z < x := by
          rcases hZ with he | ha
          · omega
          · have := ha.lt; omega
        have hpz := (layers a K).row.forest.parent_left hZP
        have hz : y < z := by omega
        have hNewZP : C.parent 0 (C.coordinates.parentCopy b z) = some (C.coordinates.parentCopy b p) := by
          rw [C.parent_parentCopy_nonroot hZLt (by change z ≠ y; omega) b 0]
          change ((layers a K).row.forest.parent z).map _ = _
          rw [hZP, Option.map_some]
        have hNewPath : C.coordinates.parentCopy b z = C.coordinates.parentCopy b q ∨
            (C.row 0).Ancestor (C.coordinates.parentCopy b z) (C.coordinates.parentCopy b q) := by
          rcases hZ with he | ha
          · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
          · exact Or.inr (C.ancestor_parentCopy (r := 0) ha hQLt b)
        exact restrictedParent_eq_of_blocker (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F)
          hNewQ hNewP (C.zero_refines_frameCopy F (badAtTerminal_bottom_refines a hbad F hSelected) hNewP)
          hPrefix hNewPath hNewZP (badAtTerminalBase_seam_order a hbad hLow hz hZLt hPbase hZP hLe b)

theorem badAtTerminal_external_seam_zero (a : RootedRow) {K x y : Nat}
    (hbad : BadAt a K 0 x y) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a K).row.value c = (layers a K).row.forest.parent c)
    (b : Nat)
    (hPrefix : ∀ i, i < (badAtTerminalContext a hbad).coordinates.encode x b →
      restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
        (badAtTerminalBase a hbad).value i = (badAtTerminalContext a hbad).parent 0 i) :
    restrictedParent (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F)
      (badAtTerminalBase a hbad).value ((badAtTerminalContext a hbad).coordinates.encode x b) =
        (badAtTerminalContext a hbad).parent 0 ((badAtTerminalContext a hbad).coordinates.encode x b) := by
  let C := badAtTerminalContext a hbad
  have hParentRoot : C.parent 0 (C.coordinates.encode x b) = (layers a K).row.forest.parent y := by
    have he := C.parent_encode C.coordinates.root_lt_last (Nat.le_refl _) b 0
    rw [if_pos ⟨rfl, Nat.le_refl _⟩] at he
    exact he
  cases hP : (layers a K).row.forest.parent y with
  | none =>
      have hn : C.parent 0 (C.coordinates.encode x b) = none := hParentRoot.trans hP
      rw [hn]
      exact badAtTerminal_external_none a hbad _ hn
  | some p =>
      have hNewP : C.parent 0 (C.coordinates.encode x b) = some p := hParentRoot.trans hP
      rw [hNewP]
      have hSparse : restrictedParent F (layers a K).row.value x = some y := (hSelected x).trans hbad.1
      have hAnc := ParentForest.ancestor_of_zeroY (restrictedParent_spec F _ hSparse).1
      cases hQ : F.parent x with
      | none =>
          cases hAnc with
          | direct hp => rw [hQ] at hp; contradiction
          | step _ hp => rw [hQ] at hp; contradiction
      | some q =>
          have hQLt := F.parent_left hQ
          have hPath : y = q ∨ (layers a K).row.forest.Ancestor y q := by
            by_cases he : y = q
            · exact Or.inl he
            · obtain ⟨z, hZ, hZP, _⟩ := restrictedParent_exists_blocker F _ hQ hSparse he ((layers a K).positive q)
              have hForest : (select F (layers a K).row.value).forest = (layers a K).row.forest :=
                parentForest_eq_of_parent_eq _ _ hSelected
              rw [hForest] at hZ
              rw [hSelected z] at hZP
              rcases hZ with hzq | ha
              · exact Or.inr (by rw [← hzq]; exact ParentForest.Ancestor.direct hZP)
              · exact Or.inr ((ParentForest.Ancestor.direct hZP).trans ha)
          have hNewQ : FrameCopy.parent C.coordinates F (C.coordinates.encode x b) = some (C.coordinates.parentCopy b q) := by
            have he := FrameCopy.parent_encode C.coordinates F C.coordinates.root_lt_last (Nat.le_refl _) b
            change FrameCopy.parent C.coordinates F (C.coordinates.encode x b) = (F.parent x).map _ at he
            rw [he, hQ, Option.map_some]
          have hNewZP : C.parent 0 (C.coordinates.parentCopy b y) = some p := by
            rw [C.coordinates.parentCopy_bad b (by change y ≤ y; omega)]
            have he := C.parent_root_copy_high (Nat.le_refl C.level) b
            exact he.trans hP
          have hNewPath : C.coordinates.parentCopy b y = C.coordinates.parentCopy b q ∨
              (C.row 0).Ancestor (C.coordinates.parentCopy b y) (C.coordinates.parentCopy b q) := by
            rcases hPath with he | ha
            · exact Or.inl (congrArg (C.coordinates.parentCopy b) he)
            · exact Or.inr (C.ancestor_parentCopy (r := 0) ha hQLt b)
          have hValTarget : (badAtTerminalBase a hbad).value (C.coordinates.encode x b) = (layers a K).row.value y := by
            change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 _ = _
            rw [C.value_above _ (show C.level ≤ 0 from Nat.le_refl 0)]
            have he : C.ordinaryContext.source0 (C.coordinates.encode x b) = y := C.ordinary_source_seam b
            rw [he]
            exact Reconstruction.value_numeric_base (layers a K).row (layers a K).positive y
          have hValWitness : (badAtTerminalBase a hbad).value (C.coordinates.parentCopy b y) = (layers a K).row.value y := by
            change Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) 0 _ = _
            rw [C.value_above _ (show C.level ≤ 0 from Nat.le_refl 0)]
            have he : C.ordinaryContext.source0 (C.coordinates.parentCopy b y) = y :=
              C.ordinaryContext.source0_parentCopy C.coordinates.root_lt_last b
            rw [he]
            exact Reconstruction.value_numeric_base (layers a K).row (layers a K).positive y
          exact restrictedParent_eq_of_blocker (badAtTerminalBase a hbad) (FrameCopy.forest C.coordinates F)
            hNewQ hNewP (C.zero_refines_frameCopy F (badAtTerminal_bottom_refines a hbad F hSelected) hNewP)
            hPrefix hNewPath hNewZP (by rw [hValTarget, hValWitness]; exact Nat.le_refl _)

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminal_external_seam_low
#print axioms OneY.Numeric.badAtTerminal_external_seam_zero
