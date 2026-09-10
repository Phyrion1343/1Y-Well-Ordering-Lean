import OneY.LowerCopyNesting

/-! # Computed component roots after lower-layer copying -/

namespace OneY.LowerCopy.Context

theorem high_ancestor_inCone (C : Context) {u a c : Nat}
    (hu : C.floor ≤ u) (hCone : C.InCone c)
    (ha : (C.mountain.row u).Ancestor a c) : C.InCone a := by
  induction ha with
  | direct hp => exact C.high_parent_inCone hCone hu hp
  | step _ hp ih => exact ih (C.high_parent_inCone hCone hu hp)

theorem high_root_inCone (C : Context) {u c : Nat}
    (hu : C.floor ≤ u) (hCone : C.InCone c) :
    C.InCone (C.mountain.rootAt u c) := by
  rcases (C.mountain.row u).root_ancestor_or_eq c with ha | he
  · exact C.high_ancestor_inCone hu hCone ha
  · change C.mountain.rootAt u c = c at he
    rw [he]
    exact hCone

/-- In a lifted contour, the root is copied from the corresponding old row.
This also holds above the source top, where both roots are the column itself. -/
theorem rootAt_lifted (C : Context) {s u : Nat}
    (_hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (hu : C.floor ≤ u) (b : Nat) :
    C.toRowMountain.rootAt (u+b*C.rise) (C.coordinates.encode s b) =
      C.mountain.rootAt u s+b*C.coordinates.length := by
  have hqCone := C.high_root_inCone hu hCone
  have hqRoot := C.root_le_of_inCone hqCone
  have hqLe := C.mountain.rootAt_le u s
  have hqNone := C.mountain.parent_rootAt u s
  have hqHeight := (C.mountain.parent_none_iff u _).mp hqNone
  have hNewHeight : C.height (C.mountain.rootAt u s+b*C.coordinates.length) =
      C.mountain.height (C.mountain.rootAt u s)+b*C.rise := by
    rw [← C.coordinates.parentCopy_bad b hqRoot,
      C.height_parentCopy (by omega) b, if_pos hqCone]
  apply (C.row (u+b*C.rise)).root_unique
  · change C.parent (u+b*C.rise) _ = none
    apply (C.parent_none_iff _ _).mpr
    rw [hNewHeight]
    omega
  · rcases (C.mountain.row u).root_ancestor_or_eq s with ha | he
    · exact Or.inl (C.lifted_ancestor_copy hu hCone ha hx b)
    · exact Or.inr (congrArg (fun q => q+b*C.coordinates.length) he)

theorem rootAt_high (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat) (hr : C.floor+b*C.rise ≤ r) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) =
      C.coordinates.parentCopy b (C.mountain.rootAt (r-b*C.rise) s) := by
  have hu : C.floor ≤ r-b*C.rise := by omega
  have hq := C.root_le_of_inCone (C.high_root_inCone hu hCone)
  rw [C.coordinates.parentCopy_bad b hq]
  have ht := C.rootAt_lifted hs hx hCone hu b
  have he : r-b*C.rise+b*C.rise = r := by omega
  rw [he] at ht
  exact ht

theorem reference_ancestor_copy (C : Context) {r a c : Nat}
    (hCone : C.InCone c) (ha : (C.mountain.row C.floor).Ancestor a c)
    (hc : c ≤ C.coordinates.x) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r ≤ C.floor+b*C.rise) :
    (C.row r).Ancestor (a+b*C.coordinates.length) (c+b*C.coordinates.length) := by
  induction ha with
  | direct hp =>
      have hParent := C.high_parent_inCone hCone (Nat.le_refl _) hp
      have hRoot := C.root_le_of_inCone hParent
      have hLeft := (C.mountain.row C.floor).parent_left hp
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode _ b) = _
      rw [C.parent_encode_reference (by omega) hc hCone b hr hTop, hp, Option.map_some]
  | @step p c ha hp ih =>
      have hParent := C.high_parent_inCone hCone (Nat.le_refl _) hp
      have hRoot := C.root_le_of_inCone hParent
      have hLeft := (C.mountain.row C.floor).parent_left hp
      apply ParentForest.Ancestor.step (ih hParent (by omega))
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode_reference (by omega) hc hCone b hr hTop, hp, Option.map_some]

theorem rootAt_reference_eq (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r ≤ C.floor+b*C.rise) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) =
      C.toRowMountain.rootAt r (C.coordinates.y+b*C.coordinates.length) := by
  have ha : (C.mountain.row C.floor).Ancestor C.coordinates.y s := by
    rcases (C.mountain.rootAt_eq_iff_path (r := C.floor)
      (q := C.coordinates.y) (c := s) rfl).mp hCone.2 with ha | he
    · exact ha
    · omega
  exact ParentForest.root_eq_of_ancestor (C.reference_ancestor_copy hCone ha hx b hr hTop)

/-- Before the contour reaches block `b`, its component root is found in the
unique earlier block whose old last-column vertical interval contains the row. -/
theorem rootAt_fill_block (C : Context) (b : Nat) {s j t : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (hj : j < b)
    (ht : C.floor ≤ t) (htTop : t < C.floor+C.rise) :
    C.toRowMountain.rootAt (t+j*C.rise) (C.coordinates.encode s b) =
      C.mountain.rootAt t C.coordinates.x+j*C.coordinates.length := by
  induction b generalizing s with
  | zero => omega
  | succ b ih =>
      have hjLe : j ≤ b := by omega
      have hmul := Nat.mul_le_mul_right C.rise hjLe
      have hTop : t+j*C.rise ≤ C.floor+(b+1)*C.rise := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [C.rootAt_reference_eq hs hx hCone (b+1) (by omega) hTop,
        C.root_copy_succ_eq]
      by_cases hEq : j = b
      · subst j
        exact C.rootAt_lifted C.coordinates.root_lt_last (Nat.le_refl _)
          C.last_inCone ht b
      · exact ih C.coordinates.root_lt_last (Nat.le_refl _) C.last_inCone (by omega)

/-- Exact quotient/remainder formula for the root of an inserted reference row. -/
theorem rootAt_fill (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r < C.floor+b*C.rise) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) =
      C.mountain.rootAt (C.floor+(r-C.floor)%C.rise) C.coordinates.x+
        ((r-C.floor)/C.rise)*C.coordinates.length := by
  have hDelta := C.rise_pos
  have hRem := Nat.mod_lt (r-C.floor) hDelta
  have hDiv := Nat.mod_add_div' (r-C.floor) C.rise
  have hj : (r-C.floor)/C.rise < b := by
    by_cases hj' : b ≤ (r-C.floor)/C.rise
    · have hm := Nat.mul_le_mul_right C.rise hj'
      omega
    · omega
  have he : C.floor+(r-C.floor)%C.rise+((r-C.floor)/C.rise)*C.rise = r := by
    omega
  have ht := C.rootAt_fill_block b hs hx hCone hj
    (by omega : C.floor ≤ C.floor+(r-C.floor)%C.rise) (by omega)
  rw [he] at ht
  exact ht

theorem rootAt_original (C : Context) {r c : Nat} (hc : c ≤ C.coordinates.x) :
    C.toRowMountain.rootAt r c = C.mountain.rootAt r c := by
  have hq := C.mountain.rootAt_le r c
  apply (C.row r).root_unique
  · change C.parent r _ = none
    rw [C.parent_original (by omega)]
    exact C.mountain.parent_rootAt r c
  · rcases (C.mountain.row r).root_ancestor_or_eq c with ha | he
    · exact Or.inl (C.prefix_ancestor ha hc)
    · exact Or.inr he

theorem rootAt_contour_floor (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat) :
    C.toRowMountain.rootAt (C.floor+b*C.rise) (C.coordinates.encode s b) =
      C.coordinates.y+b*C.coordinates.length := by
  rw [C.rootAt_lifted hs hx hCone (Nat.le_refl _) b, hCone.2]

/-- Every inserted reference component root is strictly before the current
copied root, the strict index comparison needed for relation weakening. -/
theorem rootAt_fill_lt_rootCopy (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat) (hTop : r < C.floor+b*C.rise) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) <
      C.coordinates.y+b*C.coordinates.length := by
  have hLive : C.floor+b*C.rise ≤ C.toRowMountain.height (C.coordinates.encode s b) := by
    change C.floor+b*C.rise ≤ C.height _
    rw [C.height_encode hs hx b, if_pos hCone]
    have := hCone.1
    omega
  have ht := C.toRowMountain.rootAt_strict_mono hTop hLive
  rw [C.rootAt_contour_floor hs hx hCone b] at ht
  exact ht

theorem rootAt_low (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hr : r < C.floor) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) =
      C.coordinates.parentCopy b (C.mountain.rootAt r s) := by
  have hq := C.mountain.rootAt_le r s
  have hHeight := (C.mountain.parent_none_iff r _).mp (C.mountain.parent_rootAt r s)
  have hOut : ¬ C.InCone (C.mountain.rootAt r s) := by intro h; have := h.1; omega
  apply (C.row r).root_unique
  · change C.parent r _ = none
    apply (C.parent_none_iff _ _).mpr
    rw [C.height_parentCopy (by omega) b, if_neg hOut]
    exact hHeight
  · rcases (C.mountain.row r).root_ancestor_or_eq s with ha | he
    · have ht := C.low_ancestor_copy hr ha hx b
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)] at ht
      exact Or.inl ht
    · have ht := congrArg (C.coordinates.parentCopy b) he
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)] at ht
      exact Or.inr ht

theorem rootAt_low_cone (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (hr : r < C.floor) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) = C.mountain.rootAt r s := by
  have hq := C.mountain.rootAt_strict_mono hr hCone.1
  rw [hCone.2] at hq
  rw [C.rootAt_low hs hx hr b, C.coordinates.parentCopy_good b hq]

theorem high_ancestor_outside (C : Context) {u a c : Nat}
    (hu : C.floor ≤ u) (hOut : ¬ C.InCone c)
    (ha : (C.mountain.row u).Ancestor a c) : ¬ C.InCone a := by
  induction ha with
  | direct hp => exact C.high_parent_outside hu hOut hp
  | step _ hp ih => exact ih (C.high_parent_outside hu hOut hp)

theorem rootAt_outside (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hOut : ¬ C.InCone s) (b : Nat) :
    C.toRowMountain.rootAt r (C.coordinates.encode s b) =
      C.coordinates.parentCopy b (C.mountain.rootAt r s) := by
  by_cases hLow : r < C.floor
  · exact C.rootAt_low hs hx hLow b
  · have hr : C.floor ≤ r := by omega
    have hq := C.mountain.rootAt_le r s
    have hqOut : ¬ C.InCone (C.mountain.rootAt r s) := by
      rcases (C.mountain.row r).root_ancestor_or_eq s with ha | he
      · exact C.high_ancestor_outside hr hOut ha
      · change C.mountain.rootAt r s = s at he
        rw [he]
        exact hOut
    apply (C.row r).root_unique
    · change C.parent r _ = none
      apply (C.parent_none_iff _ _).mpr
      rw [C.height_parentCopy (by omega) b, if_neg hqOut]
      exact (C.mountain.parent_none_iff r _).mp (C.mountain.parent_rootAt r s)
    · rcases (C.mountain.row r).root_ancestor_or_eq s with ha | he
      · have ht := C.outside_ancestor_copy hr hOut ha hx b
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)] at ht
        exact Or.inl ht
      · have ht := congrArg (C.coordinates.parentCopy b) he
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)] at ht
        exact Or.inr ht

#print axioms rootAt_lifted
#print axioms rootAt_reference_eq
#print axioms rootAt_fill
#print axioms rootAt_low_cone
#print axioms rootAt_outside

end OneY.LowerCopy.Context
