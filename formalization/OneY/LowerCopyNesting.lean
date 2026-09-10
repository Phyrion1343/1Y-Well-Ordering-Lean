import OneY.LowerCopy

/-! # Adjacent-row refinement for the computed lower copy graph -/

namespace OneY.LowerCopy.Context

theorem parent_encode (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b r : Nat) :
    C.parent r (C.coordinates.encode s b) =
      if C.InCone s ∧ C.floor ≤ r then
        if r < C.floor+b*C.rise then
          ((C.mountain.row C.floor).parent s).map (fun p => p+b*C.coordinates.length)
        else
          ((C.mountain.row (r-b*C.rise)).parent s).map (fun p => p+b*C.coordinates.length)
      else ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  cases b with
  | zero =>
      simp only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero,
        C.parent_original hx, Nat.sub_zero]
      by_cases h : C.InCone s ∧ C.floor ≤ r
      · rw [if_pos h, if_neg (by omega : ¬r < C.floor)]
        simp
      · rw [if_neg h]
        have hf : C.coordinates.parentCopy 0 = id := by
          funext p
          exact C.coordinates.parentCopy_zero p
        rw [hf, Option.map_id]
        rfl
  | succ b =>
      have hn := C.encode_succ_gt_last hs b
      simp only [parent, Nat.not_le_of_gt hn, ↓reduceIte,
        C.coordinates.source_encode hs hx (b+1), C.coordinates.block_encode hs hx (b+1)]

theorem parent_encode_low (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hr : r < C.floor) (b : Nat) :
    C.parent r (C.coordinates.encode s b) =
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  rw [C.parent_encode hs hx b r, if_neg (by intro h; omega)]

theorem prefix_ancestor (C : Context) {r a c : Nat}
    (ha : (C.mountain.row r).Ancestor a c) (hc : c ≤ C.coordinates.x) :
    (C.row r).Ancestor a c := by
  induction ha with
  | direct hp =>
      exact ParentForest.Ancestor.direct (by change C.parent r _ = _; rw [C.parent_original hc]; exact hp)
  | @step p c ha hp ih =>
      have hLeft := (C.mountain.row r).parent_left hp
      exact ParentForest.Ancestor.step (ih (by omega))
        (by change C.parent r c = _; rw [C.parent_original hc]; exact hp)

/-- Paths ending at the copied root do not need its outgoing seam edge. -/
theorem low_ancestor_same_block (C : Context) {r a c : Nat}
    (hr : r < C.floor) (ha : (C.mountain.row r).Ancestor a c)
    (hy : C.coordinates.y ≤ a) (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (a+b*C.coordinates.length) (c+b*C.coordinates.length) := by
  induction ha with
  | direct hp =>
      have hLeft := (C.mountain.row r).parent_left hp
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode _ b) = _
      rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
        C.coordinates.parentCopy_bad b hy]
  | @step p c ha hp ih =>
      have hAC := ha.lt
      have hPC := (C.mountain.row r).parent_left hp
      apply ParentForest.Ancestor.step (ih (by omega))
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
        C.coordinates.parentCopy_bad b (by omega)]

theorem root_ancestor_last_low (C : Context) {r : Nat} (hr : r < C.floor) :
    (C.mountain.row r).Ancestor C.coordinates.y C.coordinates.x := by
  have hRoot : (C.mountain.row C.floor).Ancestor C.coordinates.y C.coordinates.x := by
    have h := (C.mountain.rootAt_eq_iff_path (r := C.floor)
      (q := C.coordinates.y) (c := C.coordinates.x) rfl).mp C.last_root
    rcases h with h | h
    · exact h
    · have := C.coordinates.root_lt_last
      omega
  exact ParentForest.Refines.ancestor (C.mountain.refines_le (Nat.le_of_lt hr)) hRoot

theorem root_copy_succ_eq (C : Context) (b : Nat) :
    C.coordinates.y+(b+1)*C.coordinates.length =
      C.coordinates.x+b*C.coordinates.length := by
  have h := C.coordinates.root_add_length
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The outgoing path from a copied root can wind through arbitrarily many
older blocks, but it still reaches every old good-part ancestor. -/
theorem root_good_ancestor (C : Context) {r a : Nat}
    (hr : r < C.floor) (ha : (C.mountain.row r).Ancestor a C.coordinates.y)
    (b : Nat) :
    (C.row r).Ancestor a (C.coordinates.y+b*C.coordinates.length) := by
  induction b with
  | zero =>
      simpa only [Nat.zero_mul, Nat.add_zero] using
        C.prefix_ancestor ha (Nat.le_of_lt C.coordinates.root_lt_last)
  | succ b ih =>
      rw [C.root_copy_succ_eq]
      exact ih.trans (C.low_ancestor_same_block hr (C.root_ancestor_last_low hr)
        (Nat.le_refl _) (Nat.le_refl _) b)

theorem low_parent_path (C : Context) {r c p : Nat}
    (hr : r < C.floor) (hp : (C.mountain.row r).parent c = some p)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b p) (C.coordinates.parentCopy b c) := by
  have hLeft := (C.mountain.row r).parent_left hp
  by_cases hBefore : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hBefore,
      C.coordinates.parentCopy_good b (by omega)]
    exact C.prefix_ancestor (ParentForest.Ancestor.direct hp) hc
  · by_cases hEqual : c = C.coordinates.y
    · subst c
      rw [C.coordinates.parentCopy_bad b (Nat.le_refl _),
        C.coordinates.parentCopy_good b hLeft]
      exact C.root_good_ancestor hr (ParentForest.Ancestor.direct hp) b
    · have hAfter : C.coordinates.y < c := by omega
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hAfter)]
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode_low hAfter hc hr b, hp, Option.map_some]

theorem low_ancestor_copy (C : Context) {r a c : Nat}
    (hr : r < C.floor) (ha : (C.mountain.row r).Ancestor a c)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp => exact C.low_parent_path hr hp hc b
  | @step p c ha hp ih =>
      have hLeft := (C.mountain.row r).parent_left hp
      exact (ih (by omega)).trans (C.low_parent_path hr hp hc b)

theorem high_parent_outside (C : Context) {r c p : Nat}
    (hr : C.floor ≤ r) (hc : ¬ C.InCone c)
    (hp : (C.mountain.row r).parent c = some p) : ¬ C.InCone p := by
  intro hCone
  apply hc
  exact ⟨Nat.le_trans hr (Nat.le_of_lt (C.mountain.parent_source hp)),
    (C.mountain.nested_roots hr hp).trans hCone.2⟩

theorem outside_parent_path (C : Context) {r c p : Nat}
    (hOut : ¬ C.InCone c) (hp : (C.mountain.row r).parent c = some p)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b p) (C.coordinates.parentCopy b c) := by
  have hLeft := (C.mountain.row r).parent_left hp
  by_cases hBefore : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hBefore,
      C.coordinates.parentCopy_good b (by omega)]
    exact C.prefix_ancestor (ParentForest.Ancestor.direct hp) hc
  · have hAfter : C.coordinates.y < c := by
      by_cases heq : c = C.coordinates.y
      · subst c; exact False.elim (hOut C.root_inCone)
      · omega
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hAfter)]
    apply ParentForest.Ancestor.direct
    change C.parent r (C.coordinates.encode c b) = _
    rw [C.parent_encode hAfter hc b r,
      if_neg (by intro h; exact hOut h.1), hp, Option.map_some]

theorem outside_ancestor_copy (C : Context) {r a c : Nat}
    (hr : C.floor ≤ r) (hOut : ¬ C.InCone c)
    (ha : (C.mountain.row r).Ancestor a c)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp => exact C.outside_parent_path hOut hp hc b
  | @step p c ha hp ih =>
      have hLeft := (C.mountain.row r).parent_left hp
      exact (ih (C.high_parent_outside hr hOut hp) (by omega)).trans
        (C.outside_parent_path hOut hp hc b)

theorem parent_encode_lifted (C : Context) {s u : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (hu : C.floor ≤ u) (b : Nat) :
    C.parent (u+b*C.rise) (C.coordinates.encode s b) =
      ((C.mountain.row u).parent s).map (fun p => p+b*C.coordinates.length) := by
  rw [C.parent_encode hs hx b (u+b*C.rise),
    if_pos ⟨hCone, by omega⟩, if_neg (by omega : ¬u+b*C.rise < C.floor+b*C.rise),
    Nat.add_sub_cancel]

theorem lifted_ancestor_copy (C : Context) {u a c : Nat}
    (hu : C.floor ≤ u) (hCone : C.InCone c)
    (ha : (C.mountain.row u).Ancestor a c)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row (u+b*C.rise)).Ancestor (a+b*C.coordinates.length) (c+b*C.coordinates.length) := by
  induction ha with
  | direct hp =>
      have hParent := C.high_parent_inCone hCone hu hp
      have hRoot := C.root_le_of_inCone hParent
      have hLeft := (C.mountain.row u).parent_left hp
      apply ParentForest.Ancestor.direct
      change C.parent (u+b*C.rise) (C.coordinates.encode _ b) = _
      rw [C.parent_encode_lifted (by omega) hc hCone hu b, hp, Option.map_some]
  | @step p c ha hp ih =>
      have hParent := C.high_parent_inCone hCone hu hp
      have hRoot := C.root_le_of_inCone hParent
      have hLeft := (C.mountain.row u).parent_left hp
      apply ParentForest.Ancestor.step (ih hParent (by omega))
      change C.parent (u+b*C.rise) (C.coordinates.encode c b) = _
      rw [C.parent_encode_lifted (by omega) hc hCone hu b, hp, Option.map_some]

theorem parent_encode_reference (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x)
    (hCone : C.InCone s) (b : Nat)
    (hr : C.floor ≤ r) (hTop : r ≤ C.floor+b*C.rise) :
    C.parent r (C.coordinates.encode s b) =
      ((C.mountain.row C.floor).parent s).map (fun p => p+b*C.coordinates.length) := by
  rw [C.parent_encode hs hx b r, if_pos ⟨hCone, hr⟩]
  split
  · rfl
  · have heq : r-b*C.rise = C.floor := by omega
    rw [heq]

theorem nested_succ_encoded (C : Context) {s r p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat)
    (hp : C.parent (r+1) (C.coordinates.encode s b) = some p) :
    (C.row r).Ancestor p (C.coordinates.encode s b) := by
  by_cases hCone : C.InCone s
  · by_cases hLow : r < C.floor
    · by_cases hUpperLow : r+1 < C.floor
      · rw [C.parent_encode_low hs hx hUpperLow b] at hp
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        have ha := C.mountain.nested_succ r hq
        have ht := C.low_ancestor_copy hLow ha hx b
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs), heq] at ht
        exact ht
      · have he : r+1 = C.floor := by omega
        rw [he, C.parent_encode_reference hs hx hCone b (Nat.le_refl _) (by omega)] at hp
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        have hqCone := C.high_parent_inCone hCone (Nat.le_refl _) hq
        have hqRoot := C.root_le_of_inCone hqCone
        have hq' : (C.mountain.row (r+1)).parent s = some q := by rw [he]; exact hq
        have ht := C.low_ancestor_copy hLow (C.mountain.nested_succ r hq') hx b
        rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs),
          C.coordinates.parentCopy_bad b hqRoot, heq] at ht
        exact ht
    · have hFloor : C.floor ≤ r := by omega
      by_cases hFill : r < C.floor+b*C.rise
      · have hSame : C.parent r (C.coordinates.encode s b) =
            C.parent (r+1) (C.coordinates.encode s b) := by
          rw [C.parent_encode_reference hs hx hCone b hFloor (by omega),
            C.parent_encode_reference hs hx hCone b (by omega) (by omega)]
        exact ParentForest.Ancestor.direct (hSame.trans hp)
      · have hu : C.floor ≤ r-b*C.rise := by omega
        have he : r-b*C.rise+b*C.rise = r := by omega
        have heSucc : (r-b*C.rise+1)+b*C.rise = r+1 := by omega
        have hp' : C.parent ((r-b*C.rise+1)+b*C.rise)
            (C.coordinates.encode s b) = some p := by rw [heSucc]; exact hp
        rw [C.parent_encode_lifted hs hx hCone (by omega) b] at hp'
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp'
        have ht := C.lifted_ancestor_copy hu hCone
          (C.mountain.nested_succ (r-b*C.rise) hq) hx b
        rw [he, heq] at ht
        exact ht
  · rw [C.parent_encode hs hx b (r+1),
      if_neg (by intro h; exact hCone h.1)] at hp
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
    have ha := C.mountain.nested_succ r hq
    have ht : (C.row r).Ancestor (C.coordinates.parentCopy b q)
        (C.coordinates.parentCopy b s) := by
      by_cases hLow : r < C.floor
      · exact C.low_ancestor_copy hLow ha hx b
      · exact C.outside_ancestor_copy (by omega) hCone ha hx b
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs), heq] at ht
    exact ht

/-- The computed three-part graph is nested, including both insertion boundaries
and the seam paths through earlier blocks. -/
theorem nested_succ (C : Context) (r : Nat) : (C.row (r+1)).Refines (C.row r) := by
  intro c p hp
  change C.parent (r+1) c = some p at hp
  by_cases hOld : c ≤ C.coordinates.x
  · rw [C.parent_original hOld] at hp
    exact C.prefix_ancestor (C.mountain.nested_succ r hp) hOld
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have he := C.coordinates.encode_coordinates hc
    have hs := C.coordinates.source_bounds c
    have hp' : C.parent (r+1)
        (C.coordinates.encode (C.coordinates.source c) (C.coordinates.block c)) = some p := by
      rw [he]; exact hp
    have ht := C.nested_succ_encoded hs.1 hs.2 (C.coordinates.block c) hp'
    rw [he] at ht
    exact ht

/-- A genuine row mountain obtained from the explicit copy formulas. -/
def toRowMountain (C : Context) : RootGeometry.RowMountain where
  height := C.height
  row := C.row
  parent_exists := fun _ _ h => C.parent_exists h
  parent_source := C.parent_source
  parent_endpoint := C.parent_endpoint
  nested_succ := C.nested_succ

@[simp] theorem toRowMountain_height (C : Context) (c : Nat) :
    C.toRowMountain.height c = C.height c := rfl

@[simp] theorem toRowMountain_row (C : Context) (r : Nat) :
    C.toRowMountain.row r = C.row r := rfl

#print axioms root_good_ancestor
#print axioms low_ancestor_copy
#print axioms outside_ancestor_copy
#print axioms lifted_ancestor_copy
#print axioms nested_succ
#print axioms toRowMountain

end OneY.LowerCopy.Context
