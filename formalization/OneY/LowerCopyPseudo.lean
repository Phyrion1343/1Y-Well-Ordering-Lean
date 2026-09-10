import OneY.LowerCopyPseudoLow
import OneY.FrameCopy
import OneY.SingleContraction

/-! # The full lower pseudo-parent formula and its single contraction -/

namespace OneY.FrameCopy

theorem root_ancestor_or_eq_copy (C : CopyCoordinates.Context) (F : ParentForest)
    (hRoot : F.Ancestor C.y C.x) (b : Nat) :
    C.y = C.y+b*C.length ∨ (forest C F).Ancestor C.y (C.y+b*C.length) := by
  induction b with
  | zero => exact Or.inl (by omega)
  | succ b ih =>
      right
      rw [root_copy_succ_eq]
      have ha := ancestor_same_block C F hRoot (Nat.le_refl _) (Nat.le_refl _) b
      rcases ih with he | hi
      · rw [← he] at ha
        exact ha
      · exact hi.trans ha

end OneY.FrameCopy

namespace OneY.LowerCopy.Context

theorem pseudo_parent_original (C : Context) {c : Nat} (hc : c ≤ C.coordinates.x) :
    Pseudo.parent C.toRowMountain c = Pseudo.parent C.mountain c := by
  by_cases hz : C.mountain.height c = 0
  · have hNew : Pseudo.parent C.toRowMountain c = none :=
      (Pseudo.parent_none_iff C.toRowMountain c).mpr ((C.height_original hc).trans hz)
    rw [hNew, (Pseudo.parent_none_iff C.mountain c).mpr hz]
  · have hOld : 0 < C.mountain.height c := by omega
    have hNew : 0 < C.toRowMountain.height c := by change 0 < C.height c; rwa [C.height_original hc]
    rw [Pseudo.parent_eq_firstMatch C.toRowMountain hNew, Pseudo.parent_eq_firstMatch C.mountain hOld]
    change (C.row (C.height c-1)).firstMatch (fun q => decide (C.height q ≤ C.height c)) c = _
    rw [C.height_original hc]
    exact C.firstMatch_original hc

theorem pseudo_parent_parentCopy (C : Context) (hRegular : C.DepthRegular) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat) :
    Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b s) =
      if C.mountain.height s = C.floor ∧ Pseudo.parent C.mountain s = some C.coordinates.y then
        some C.coordinates.y else (Pseudo.parent C.mountain s).map (C.coordinates.parentCopy b) := by
  by_cases hCone : C.InCone s
  · have hh := C.height_lt_of_inCone hCone hs
    rw [if_neg (by intro h; omega), C.pseudo_parent_lifted hs hx hCone b]
  · by_cases hHigh : C.floor < C.mountain.height s
    · rw [if_neg (by intro h; omega), C.pseudo_parent_outside_high hx hCone hHigh b]
    · by_cases hZero : C.mountain.height s = 0
      · have hOld := (Pseudo.parent_none_iff C.mountain s).mpr hZero
        have hNew : Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b s) = none := by
          apply (Pseudo.parent_none_iff _ _).mpr
          change C.height _ = 0
          rw [C.height_parentCopy hx b, if_neg hCone, hZero]
        simp only [hNew, hOld, Option.map_none, reduceCtorEq, and_false, ↓reduceIte]
      · rw [C.pseudo_parent_low hRegular hs hx (by omega) (by omega) b]
        cases hp : Pseudo.parent C.mountain s with
        | none => simp only [Option.map_none, reduceCtorEq, and_false, ↓reduceIte]
        | some p =>
            rw [Option.map_some]
            by_cases he : p = C.coordinates.y
            · subst p
              have hh := Pseudo.parent_height C.mountain hp
              have hHeight : C.mountain.height s = C.floor := by
                change C.floor = C.mountain.height s ∨ C.floor+1 = C.mountain.height s at hh
                omega
              rw [if_pos ⟨hHeight, rfl⟩, C.lowParentCopy_root]
            · rw [if_neg (by intro h; exact he (Option.some.inj h.2)), Option.map_some,
                C.lowParentCopy_nonroot b he]

/-- The selected upper parent is good at exactly the columns whose
pseudo-parent edge is contracted. This is supplied by upper recovery. -/
def ContractedSelectionGood (C : Context) (newTop : Nat → Nat) : Prop :=
  ∀ s, C.coordinates.y < s → s ≤ C.coordinates.x →
    C.mountain.height s = C.floor → Pseudo.parent C.mountain s = some C.coordinates.y →
    ∀ b p, Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop
      (C.coordinates.parentCopy b s) = some p → p < C.coordinates.y

theorem pseudo_select_eq_frameCopy (C : Context) (hRegular : C.DepthRegular)
    (hRoot : (Pseudo.forest C.mountain).Ancestor C.coordinates.y C.coordinates.x)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hGood : C.ContractedSelectionGood newTop) (c : Nat) :
    Numeric.restrictedParent (Pseudo.forest C.toRowMountain) newTop c =
      Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop c := by
  apply Numeric.select_eq_single_contraction _ _ newTop hPositive C.coordinates.y
  · intro i hi
    change Pseudo.parent C.toRowMountain i = FrameCopy.parent C.coordinates (Pseudo.forest C.mountain) i
    rw [C.pseudo_parent_original (by have := C.coordinates.root_lt_last; omega),
      FrameCopy.parent_original C.coordinates (Pseudo.forest C.mountain) (by have := C.coordinates.root_lt_last; omega)]
    rfl
  · intro i
    by_cases hOld : i ≤ C.coordinates.x
    · left
      change Pseudo.parent C.toRowMountain i = FrameCopy.parent C.coordinates (Pseudo.forest C.mountain) i
      rw [C.pseudo_parent_original hOld, FrameCopy.parent_original C.coordinates (Pseudo.forest C.mountain) hOld]
      rfl
    · have hs := C.coordinates.source_bounds i
      have he : C.coordinates.parentCopy (C.coordinates.block i) (C.coordinates.source i) = i := by
        rw [C.coordinates.parentCopy_bad _ (Nat.le_of_lt hs.1)]
        exact C.coordinates.encode_coordinates (by have := C.coordinates.root_lt_last; omega)
      have ht := C.pseudo_parent_parentCopy hRegular hs.1 hs.2 (C.coordinates.block i)
      by_cases hSpecial : C.mountain.height (C.coordinates.source i) = C.floor ∧
          Pseudo.parent C.mountain (C.coordinates.source i) = some C.coordinates.y
      · right
        rw [if_pos hSpecial, he] at ht
        refine ⟨ht, ?_, ?_⟩
        · have hDirect : (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)).Ancestor
              (C.coordinates.y+C.coordinates.block i*C.coordinates.length) i := by
            apply ParentForest.Ancestor.direct
            change FrameCopy.parent _ _ i = _
            have hG := FrameCopy.parent_nonroot C.coordinates (Pseudo.forest C.mountain) hs.2
              (by omega : C.coordinates.source i ≠ C.coordinates.y) (C.coordinates.block i)
            rw [he] at hG
            rw [hG]
            change (Pseudo.parent C.mountain (C.coordinates.source i)).map _ = _
            rw [hSpecial.2, Option.map_some, C.coordinates.parentCopy_bad _ (Nat.le_refl _)]
          rcases FrameCopy.root_ancestor_or_eq_copy C.coordinates (Pseudo.forest C.mountain) hRoot (C.coordinates.block i) with hy | ha
          · rw [← hy] at hDirect
            exact hDirect
          · exact ha.trans hDirect
        · intro p hp
          exact hGood (C.coordinates.source i) hs.1 hs.2 hSpecial.1 hSpecial.2
            (C.coordinates.block i) p (by simpa only [he] using hp)
      · left
        rw [if_neg hSpecial, he] at ht
        change Pseudo.parent C.toRowMountain i = FrameCopy.parent C.coordinates (Pseudo.forest C.mountain) i
        have hG := FrameCopy.parent_nonroot C.coordinates (Pseudo.forest C.mountain) hs.2
          (by omega : C.coordinates.source i ≠ C.coordinates.y) (C.coordinates.block i)
        rw [he] at hG
        rw [ht, hG]
        rfl

#print axioms pseudo_parent_parentCopy
#print axioms pseudo_select_eq_frameCopy

end OneY.LowerCopy.Context
