import OneY.LowerCopyPseudoOutside
import OneY.FirstMatch

/-! # Threshold search through the lower copied seams -/

namespace OneY.LowerCopy.Context

def lowParentCopy (C : Context) (b p : Nat) : Nat :=
  if p = C.coordinates.y then p else C.coordinates.parentCopy b p

theorem lowParentCopy_root (C : Context) (b : Nat) : C.lowParentCopy b C.coordinates.y = C.coordinates.y := by
  simp only [lowParentCopy, ↓reduceIte]

theorem lowParentCopy_nonroot (C : Context) (b : Nat) {p : Nat} (hp : p ≠ C.coordinates.y) :
    C.lowParentCopy b p = C.coordinates.parentCopy b p := by rw [lowParentCopy, if_neg hp]

theorem lowParentCopy_good (C : Context) (b : Nat) {p : Nat} (hp : p < C.coordinates.y) :
    C.lowParentCopy b p = p := by
  rw [C.lowParentCopy_nonroot b (by omega), C.coordinates.parentCopy_good b hp]

theorem lowParentCopy_zero (C : Context) (p : Nat) : C.lowParentCopy 0 p = p := by
  unfold lowParentCopy
  split
  · rfl
  · exact C.coordinates.parentCopy_zero p

theorem firstMatch_original (C : Context) {r c t : Nat} (hc : c ≤ C.coordinates.x) :
    (C.row r).firstMatch (fun q => decide (C.height q ≤ t)) c =
      (C.mountain.row r).firstMatch (fun q => decide (C.mountain.height q ≤ t)) c :=
  ParentForest.firstMatch_prefix_congr _ _ _ _ (C.coordinates.x+1)
    (fun q hq => C.parent_original (by omega))
    (fun q hq => by rw [C.height_original (by omega : q ≤ C.coordinates.x)]) (by omega)

theorem lowTest_copy_nonroot (C : Context) {q t : Nat} (hq : q ≤ C.coordinates.x)
    (hNot : q ≠ C.coordinates.y) (ht : t ≤ C.floor) (b : Nat) :
    decide (C.height (C.coordinates.parentCopy b q) ≤ t) = decide (C.mountain.height q ≤ t) := by
  rw [C.height_parentCopy hq b]
  by_cases hCone : C.InCone q
  · rw [if_pos hCone]
    have hHigh := C.height_lt_of_inCone hCone (by have := C.root_le_of_inCone hCone; omega)
    have hOld : ¬ C.mountain.height q ≤ t := by omega
    have hNew : ¬ C.mountain.height q+b*C.rise ≤ t := by omega
    simp only [hOld, hNew, decide_false]
  · rw [if_neg hCone]

theorem firstMatch_old_last (C : Context) (hRegular : C.DepthRegular) {t : Nat}
    (hPos : 0 < t) (ht : t ≤ C.floor) :
    (C.mountain.row (t-1)).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.x =
      if decide (C.floor ≤ t) then some C.coordinates.y else
        (C.mountain.row (t-1)).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.y := by
  have hAnc := C.root_ancestor_last_low (by omega : t-1 < C.floor)
  apply ParentForest.firstMatch_skipTo _ _ hAnc
  intro q hq hAfter
  have hh := C.seam_intermediate_height hRegular hPos ht hq hAfter
  simp only [Nat.not_le.mpr hh, decide_false]

theorem map_firstMatch_root (C : Context) (r t b : Nat) :
    ((C.mountain.row r).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.y).map
      (C.lowParentCopy b) =
      (C.mountain.row r).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.y := by
  cases hp : (C.mountain.row r).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.y with
  | none => rfl
  | some p =>
      have hlt := ((C.mountain.row r).firstMatch_some_spec _ hp).1.lt
      rw [Option.map_some, C.lowParentCopy_good b hlt]

theorem firstMatch_copy_low (C : Context) (hRegular : C.DepthRegular) {t : Nat}
    (hPos : 0 < t) (ht : t ≤ C.floor) {s : Nat}
    (hs : s ≤ C.coordinates.x) (hNot : s ≠ C.coordinates.y) (b : Nat) :
    (C.row (t-1)).firstMatch (fun q => decide (C.height q ≤ t)) (C.coordinates.parentCopy b s) =
      ((C.mountain.row (t-1)).firstMatch (fun q => decide (C.mountain.height q ≤ t)) s).map
        (C.lowParentCopy b) := by
  have hr : t-1 < C.floor := by omega
  have hParent : ∀ {s}, s ≤ C.coordinates.x → s ≠ C.coordinates.y → ∀ b,
      C.parent (t-1) (C.coordinates.parentCopy b s) =
        ((C.mountain.row (t-1)).parent s).map (C.coordinates.parentCopy b) := by
    intro s hs hNot b
    by_cases hGood : s < C.coordinates.y
    · rw [C.coordinates.parentCopy_good b hGood, C.parent_original hs]
      cases hp : (C.mountain.row (t-1)).parent s with
      | none => rfl
      | some p =>
          rw [Option.map_some, C.coordinates.parentCopy_good b (by have := (C.mountain.row (t-1)).parent_left hp; omega)]
    · rw [C.coordinates.parentCopy_bad b (by omega)]
      exact C.parent_encode_low (by omega) hs hr b
  have main : ∀ b s, s ≤ C.coordinates.x → s ≠ C.coordinates.y →
      (C.row (t-1)).firstMatch (fun q => decide (C.height q ≤ t)) (C.coordinates.parentCopy b s) =
        ((C.mountain.row (t-1)).firstMatch (fun q => decide (C.mountain.height q ≤ t)) s).map
          (C.lowParentCopy b) := by
    intro b
    induction b with
    | zero =>
        intro s hs _
        rw [C.coordinates.parentCopy_zero, C.firstMatch_original hs]
        have he : C.lowParentCopy 0 = id := funext C.lowParentCopy_zero
        rw [he, Option.map_id]
        rfl
    | succ b ih =>
        have hRoot : (C.row (t-1)).firstMatch (fun q => decide (C.height q ≤ t))
            (C.coordinates.parentCopy (b+1) C.coordinates.y) =
            if decide (C.floor ≤ t) then some C.coordinates.y else
              (C.mountain.row (t-1)).firstMatch (fun q => decide (C.mountain.height q ≤ t)) C.coordinates.y := by
          rw [C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.root_copy_succ_eq,
            ← C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last),
            ih C.coordinates.x (Nat.le_refl _) (by have := C.coordinates.root_lt_last; omega),
            C.firstMatch_old_last hRegular hPos ht]
          split
          · rw [Option.map_some, C.lowParentCopy_root]
          · exact C.map_firstMatch_root (t-1) t b
        intro s
        induction s using Nat.strongRecOn with
        | ind s ihCol =>
            intro hs hNot
            cases hp : (C.mountain.row (t-1)).parent s with
            | none =>
                have hNew : (C.row (t-1)).parent (C.coordinates.parentCopy (b+1) s) = none := by
                  change C.parent _ _ = _
                  rw [hParent hs hNot (b+1), hp, Option.map_none]
                rw [ParentForest.firstMatch_of_none _ _ hNew, ParentForest.firstMatch_of_none _ _ hp, Option.map_none]
            | some p =>
                have hlt := (C.mountain.row (t-1)).parent_left hp
                have hNew : (C.row (t-1)).parent (C.coordinates.parentCopy (b+1) s) = some (C.coordinates.parentCopy (b+1) p) := by
                  change C.parent _ _ = _
                  rw [hParent hs hNot (b+1), hp, Option.map_some]
                rw [ParentForest.firstMatch_of_some _ _ hNew, ParentForest.firstMatch_of_some _ _ hp]
                by_cases he : p = C.coordinates.y
                · subst p
                  have hHigh : ¬ C.height (C.coordinates.parentCopy (b+1) C.coordinates.y) ≤ t := by
                    rw [C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.height_root_copy]
                    have hRise := C.rise_pos
                    rw [Nat.add_mul, Nat.one_mul]
                    omega
                  rw [decide_eq_false hHigh]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [hRoot]
                  change (if decide (C.floor ≤ t) then some C.coordinates.y else _) =
                    (if decide (C.floor ≤ t) then some C.coordinates.y else _).map _
                  split
                  · rw [Option.map_some, C.lowParentCopy_root]
                  · exact (C.map_firstMatch_root (t-1) t (b+1)).symm
                · rw [C.lowTest_copy_nonroot (by omega) he ht (b+1)]
                  split
                  · rw [Option.map_some, C.lowParentCopy_nonroot (b+1) he]
                  · exact ihCol p hlt (by omega) he
  exact main b s hs hNot

theorem pseudo_parent_low (C : Context) (hRegular : C.DepthRegular) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hHeight : 0 < C.mountain.height s) (hLow : C.mountain.height s ≤ C.floor) (b : Nat) :
    Pseudo.parent C.toRowMountain (C.coordinates.parentCopy b s) =
      (Pseudo.parent C.mountain s).map (C.lowParentCopy b) := by
  have hOut : ¬ C.InCone s := by
    intro hc
    have := C.height_lt_of_inCone hc hs
    omega
  have hNewHeight : C.toRowMountain.height (C.coordinates.parentCopy b s) = C.mountain.height s := by
    change C.height _ = _
    rw [C.height_parentCopy hx b, if_neg hOut]
  rw [Pseudo.parent_eq_firstMatch C.toRowMountain (by rw [hNewHeight]; exact hHeight),
    hNewHeight, Pseudo.parent_eq_firstMatch C.mountain hHeight]
  exact C.firstMatch_copy_low hRegular hHeight hLow hx (by omega) b

#print axioms firstMatch_copy_low
#print axioms pseudo_parent_low

end OneY.LowerCopy.Context
