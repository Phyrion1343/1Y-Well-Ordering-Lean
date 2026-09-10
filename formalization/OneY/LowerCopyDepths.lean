import OneY.LowerCopyDominance

/-! # Actual depth formulas for lower-layer copy forests -/

namespace OneY.LowerCopy.Context

theorem depth_lifted (C : Context) {s u : Nat}
    (hs : s ≤ C.coordinates.x) (hCone : C.InCone s) (hu : C.floor ≤ u) (b : Nat) :
    (C.row (u+b*C.rise)).depth (C.coordinates.parentCopy b s) = (C.mountain.row u).depth s := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
      cases hp : (C.mountain.row u).parent s with
      | none =>
          have hHeight := (C.mountain.parent_none_iff u s).mp hp
          have hNewNone : C.parent (u+b*C.rise) (C.coordinates.parentCopy b s) = none := by
            apply (C.parent_none_iff _ _).mpr
            rw [C.height_parentCopy hs b, if_pos hCone]
            omega
          rw [(C.row _).depth_of_parent_none hNewNone, (C.mountain.row u).depth_of_parent_none hp]
      | some p =>
          have hpCone := C.high_parent_inCone hCone hu hp
          have hpRoot := C.root_le_of_inCone hpCone
          have hpLeft := (C.mountain.row u).parent_left hp
          have hNewParent : C.parent (u+b*C.rise) (C.coordinates.parentCopy b s) =
              some (C.coordinates.parentCopy b p) := by
            have hsAfter : C.coordinates.y < s := by omega
            rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hsAfter),
              C.coordinates.parentCopy_bad b hpRoot]
            change C.parent (u+b*C.rise) (C.coordinates.encode s b) = _
            rw [C.parent_encode_lifted hsAfter hs hCone hu b, hp, Option.map_some]
          rw [(C.row _).depth_of_parent_some hNewParent,
            (C.mountain.row u).depth_of_parent_some hp, ih p hpLeft (by omega) hpCone]

theorem depth_reference_ancestor (C : Context) {a c r : Nat}
    (hc : c ≤ C.coordinates.x) (hCone : C.InCone c)
    (ha : (C.mountain.row C.floor).Ancestor a c) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r ≤ C.floor+b*C.rise) :
    (C.row r).depth (c+b*C.coordinates.length)+(C.mountain.row C.floor).depth a =
      (C.row r).depth (a+b*C.coordinates.length)+(C.mountain.row C.floor).depth c := by
  induction ha with
  | @direct c hp =>
      have hpCone := C.high_parent_inCone hCone (Nat.le_refl _) hp
      have hpRoot := C.root_le_of_inCone hpCone
      have hpLeft := (C.mountain.row C.floor).parent_left hp
      have hNew : C.parent r (c+b*C.coordinates.length) = some (a+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_reference (by omega) hc hCone b hr hTop, hp, Option.map_some]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row C.floor).depth_of_parent_some hp]
      omega
  | @step p c ha hp ih =>
      have hpCone := C.high_parent_inCone hCone (Nat.le_refl _) hp
      have hpRoot := C.root_le_of_inCone hpCone
      have hpLeft := (C.mountain.row C.floor).parent_left hp
      have hPrev := ih (by omega) hpCone
      have hNew : C.parent r (c+b*C.coordinates.length) = some (p+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_reference (by omega) hc hCone b hr hTop, hp, Option.map_some]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row C.floor).depth_of_parent_some hp]
      omega

theorem depth_reference_root (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hCone : C.InCone s)
    (b : Nat) (hr : C.floor ≤ r) (hTop : r ≤ C.floor+b*C.rise) :
    (C.row r).depth (C.coordinates.encode s b) =
      (C.mountain.row C.floor).depth s+(C.row r).depth (C.coordinates.y+b*C.coordinates.length) := by
  have ha : (C.mountain.row C.floor).Ancestor C.coordinates.y s := by
    rcases (C.mountain.rootAt_eq_iff_path (r := C.floor) (q := C.coordinates.y) (c := s) rfl).mp hCone.2 with ha | he
    · exact ha
    · omega
  have ht := C.depth_reference_ancestor hx hCone ha b hr hTop
  have hZero := (C.mountain.row C.floor).depth_of_parent_none
    ((C.mountain.parent_none_iff C.floor C.coordinates.y).mpr (Nat.le_refl _))
  rw [hZero] at ht
  change (C.row r).depth (s+b*C.coordinates.length) = _
  omega

theorem depth_fill_block (C : Context) (b : Nat) {s j t : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (hj : j < b)
    (ht : C.floor ≤ t) (htTop : t < C.floor+C.rise) :
    (C.row (t+j*C.rise)).depth (C.coordinates.encode s b) =
      (C.mountain.row C.floor).depth s+
        (b-j-1)*(C.mountain.row C.floor).depth C.coordinates.x+
        (C.mountain.row t).depth C.coordinates.x := by
  induction b generalizing s with
  | zero => omega
  | succ b ih =>
      have hjLe : j ≤ b := by omega
      have hmul := Nat.mul_le_mul_right C.rise hjLe
      have hTop : t+j*C.rise ≤ C.floor+(b+1)*C.rise := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [C.depth_reference_root hs hx hCone (b+1) (by omega) hTop,
        C.root_copy_succ_eq]
      by_cases hEq : j = b
      · subst j
        have hLift := C.depth_lifted (Nat.le_refl _) C.last_inCone ht b
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last)] at hLift
        rw [hLift]
        simp
      · have hPrev := ih C.coordinates.root_lt_last (Nat.le_refl _) C.last_inCone (by omega)
        change (C.row (t+j*C.rise)).depth (C.coordinates.x+b*C.coordinates.length) = _ at hPrev
        rw [hPrev]
        have he : b+1-j-1 = (b-j-1)+1 := by omega
        rw [he, Nat.add_mul, Nat.one_mul]
        omega

theorem depth_fill (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r < C.floor+b*C.rise) :
    (C.row r).depth (C.coordinates.encode s b) =
      (C.mountain.row C.floor).depth s+
        (b-(r-C.floor)/C.rise-1)*(C.mountain.row C.floor).depth C.coordinates.x+
        (C.mountain.row (C.floor+(r-C.floor)%C.rise)).depth C.coordinates.x := by
  have hDelta := C.rise_pos
  have hRem := Nat.mod_lt (r-C.floor) hDelta
  have hDiv := Nat.mod_add_div' (r-C.floor) C.rise
  have hj : (r-C.floor)/C.rise < b := by
    by_cases hj' : b ≤ (r-C.floor)/C.rise
    · have hm := Nat.mul_le_mul_right C.rise hj'
      omega
    · omega
  have he : C.floor+(r-C.floor)%C.rise+((r-C.floor)/C.rise)*C.rise = r := by omega
  have ht := C.depth_fill_block b hs hx hCone hj
    (by omega : C.floor ≤ C.floor+(r-C.floor)%C.rise) (by omega)
  rw [he] at ht
  exact ht

theorem depth_original (C : Context) {r c : Nat} (hc : c ≤ C.coordinates.x) :
    (C.row r).depth c = (C.mountain.row r).depth c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : (C.mountain.row r).parent c with
      | none =>
          have hNew : (C.row r).parent c = none := by
            change C.parent r c = none
            rw [C.parent_original hc, hp]
          rw [(C.row r).depth_of_parent_none hNew,
            (C.mountain.row r).depth_of_parent_none hp]
      | some p =>
          have hpLeft := (C.mountain.row r).parent_left hp
          have hNew : (C.row r).parent c = some p := by
            change C.parent r c = some p
            rw [C.parent_original hc, hp]
          rw [(C.row r).depth_of_parent_some hNew,
            (C.mountain.row r).depth_of_parent_some hp, ih p hpLeft (by omega)]

theorem depth_low_ancestor (C : Context) {a c r : Nat}
    (hc : c ≤ C.coordinates.x) (haRoot : C.coordinates.y ≤ a)
    (ha : (C.mountain.row r).Ancestor a c) (b : Nat) (hr : r < C.floor) :
    (C.row r).depth (c+b*C.coordinates.length)+(C.mountain.row r).depth a =
      (C.row r).depth (a+b*C.coordinates.length)+(C.mountain.row r).depth c := by
  induction ha with
  | @direct c hp =>
      have hpLeft := (C.mountain.row r).parent_left hp
      have hNew : C.parent r (c+b*C.coordinates.length) = some (a+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
          C.coordinates.parentCopy_bad b haRoot]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp]
      omega
  | @step p c ha hp ih =>
      have hpLeft := (C.mountain.row r).parent_left hp
      have haLeft := ha.lt
      have hPrev := ih (by omega)
      have hNew : C.parent r (c+b*C.coordinates.length) = some (p+b*C.coordinates.length) := by
        change C.parent r (C.coordinates.encode c b) = _
        rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
          C.coordinates.parentCopy_bad b (by omega)]
      rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp]
      omega

/-- Each passage through the old last column adds the old root-to-last distance. -/
theorem depth_root_low (C : Context) {r : Nat} (hr : r < C.floor) (b : Nat) :
    (C.row r).depth (C.coordinates.y+b*C.coordinates.length) =
      (C.mountain.row r).depth C.coordinates.y+
        b*((C.mountain.row r).depth C.coordinates.x-(C.mountain.row r).depth C.coordinates.y) := by
  have hPath := C.root_ancestor_last_low hr
  have hDepth := hPath.depth_lt
  induction b with
  | zero =>
      simpa using C.depth_original (r := r) (Nat.le_of_lt C.coordinates.root_lt_last)
  | succ b ih =>
      rw [C.root_copy_succ_eq]
      have he := C.depth_low_ancestor (Nat.le_refl _) (Nat.le_refl _) hPath b hr
      rw [ih] at he
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem depth_low_of_root_ancestor (C : Context) {s r : Nat}
    (hs : s ≤ C.coordinates.x)
    (hPath : C.coordinates.y = s ∨ (C.mountain.row r).Ancestor C.coordinates.y s)
    (hr : r < C.floor) (b : Nat) :
    (C.row r).depth (C.coordinates.parentCopy b s) =
      (C.mountain.row r).depth s+
        b*((C.mountain.row r).depth C.coordinates.x-(C.mountain.row r).depth C.coordinates.y) := by
  rcases hPath with he | ha
  · subst s
    rw [C.coordinates.parentCopy_bad b (Nat.le_refl _)]
    exact C.depth_root_low hr b
  · have hLeft := ha.lt
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hLeft)]
    have ht := C.depth_low_ancestor hs (Nat.le_refl _) ha b hr
    rw [C.depth_root_low hr b] at ht
    omega

theorem depth_low_of_no_root_ancestor (C : Context) {s r : Nat}
    (hs : s ≤ C.coordinates.x) (hne : s ≠ C.coordinates.y)
    (hNo : ¬ (C.mountain.row r).Ancestor C.coordinates.y s)
    (hr : r < C.floor) (b : Nat) :
    (C.row r).depth (C.coordinates.parentCopy b s) = (C.mountain.row r).depth s := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
      have hOut : ¬ C.InCone s := by
        intro hCone
        rcases (C.mountain.rootAt_eq_iff_path (r := C.floor)
          (q := C.coordinates.y) (c := s) rfl).mp hCone.2 with ha | he
        · exact hNo (ParentForest.Refines.ancestor (C.mountain.refines_le (Nat.le_of_lt hr)) ha)
        · exact hne he.symm
      cases hp : (C.mountain.row r).parent s with
      | none =>
          have hHeight := (C.mountain.parent_none_iff r s).mp hp
          have hNew : (C.row r).parent (C.coordinates.parentCopy b s) = none := by
            change C.parent r _ = none
            apply (C.parent_none_iff _ _).mpr
            rw [C.height_parentCopy hs b, if_neg hOut]
            exact hHeight
          rw [(C.row r).depth_of_parent_none hNew, (C.mountain.row r).depth_of_parent_none hp]
      | some p =>
          have hpLeft := (C.mountain.row r).parent_left hp
          have hpNe : p ≠ C.coordinates.y := by
            intro he
            subst p
            exact hNo (ParentForest.Ancestor.direct hp)
          have hpNo : ¬ (C.mountain.row r).Ancestor C.coordinates.y p := by
            intro ha
            exact hNo (ParentForest.Ancestor.step ha hp)
          have hNew := C.parent_rowCopy hs hne hp b
          rw [C.rowCopy_low hr] at hNew
          rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp,
            ih p hpLeft (by omega) hpNe hpNo]

theorem depth_outside_high (C : Context) {s r : Nat}
    (hs : s ≤ C.coordinates.x) (hOut : ¬ C.InCone s)
    (hr : C.floor ≤ r) (b : Nat) :
    (C.row r).depth (C.coordinates.parentCopy b s) = (C.mountain.row r).depth s := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
      cases hp : (C.mountain.row r).parent s with
      | none =>
          have hHeight := (C.mountain.parent_none_iff r s).mp hp
          have hNew : (C.row r).parent (C.coordinates.parentCopy b s) = none := by
            change C.parent r _ = none
            apply (C.parent_none_iff _ _).mpr
            rw [C.height_parentCopy hs b, if_neg hOut]
            exact hHeight
          rw [(C.row r).depth_of_parent_none hNew, (C.mountain.row r).depth_of_parent_none hp]
      | some p =>
          have hpLeft := (C.mountain.row r).parent_left hp
          have hpOut := C.high_parent_outside hr hOut hp
          have hNe : s ≠ C.coordinates.y := by intro he; subst s; exact hOut C.root_inCone
          have hNew := C.parent_rowCopy hs hNe hp b
          rw [C.rowCopy_outside hOut] at hNew
          rw [(C.row r).depth_of_parent_some hNew, (C.mountain.row r).depth_of_parent_some hp,
            ih p hpLeft (by omega) hpOut]

theorem depth_floor_inCone (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hCone : C.InCone s) (b : Nat) :
    (C.row C.floor).depth (C.coordinates.parentCopy b s) =
      (C.mountain.row C.floor).depth s+b*(C.mountain.row C.floor).depth C.coordinates.x := by
  rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs)]
  cases b with
  | zero =>
      simpa using C.depth_original (r := C.floor) hx
  | succ b =>
      have ht := C.depth_fill_block (b+1) (j := 0) (t := C.floor) hs hx hCone
        (by omega) (Nat.le_refl _) (by have := C.rise_pos; omega)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.add_sub_cancel] at ht
      change (C.row C.floor).depth (C.coordinates.encode s (b+1)) = _
      rw [ht, Nat.add_mul, Nat.one_mul]
      omega

#print axioms depth_lifted
#print axioms depth_reference_root
#print axioms depth_fill
#print axioms depth_low_of_root_ancestor
#print axioms depth_low_of_no_root_ancestor
#print axioms depth_outside_high

end OneY.LowerCopy.Context
