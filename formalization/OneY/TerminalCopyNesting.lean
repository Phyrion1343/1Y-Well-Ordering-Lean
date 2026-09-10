import OneY.TerminalCopy

/-! # Adjacent-row refinement for the active finite copy graph -/

namespace OneY.TerminalCopy.Context

theorem parent_encode_low (C : Context) {s r : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (hr : r < C.level) (b : Nat) :
    C.parent r (C.coordinates.encode s b) =
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  rw [C.parent_encode hs hx b r, if_neg (by intro h; omega)]

theorem prefix_ancestor (C : Context) {r a c : Nat}
    (ha : (C.mountain.row r).Ancestor a c) (hc : c < C.coordinates.x) :
    (C.row r).Ancestor a c := by
  induction ha with
  | direct hp =>
      exact ParentForest.Ancestor.direct
        (by change C.parent r _ = _; rw [C.parent_original hc r]; exact hp)
  | @step p c ha hp ih =>
      have hleft := (C.mountain.row r).parent_left hp
      exact ParentForest.Ancestor.step (ih (by omega))
        (by change C.parent r c = _; rw [C.parent_original hc r]; exact hp)

theorem low_ancestor_same_block (C : Context) {r a c : Nat}
    (hr : r < C.level) (ha : (C.mountain.row r).Ancestor a c)
    (hy : C.coordinates.y ≤ a) (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (a+b*C.coordinates.length) (c+b*C.coordinates.length) := by
  induction ha with
  | direct hp =>
      have hleft := (C.mountain.row r).parent_left hp
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode _ b) = _
      rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
        C.coordinates.parentCopy_bad b hy]
  | @step p c ha hp ih =>
      have hap := ha.lt
      have hpc := (C.mountain.row r).parent_left hp
      apply ParentForest.Ancestor.step (ih (by omega))
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode_low (by omega) hc hr b, hp, Option.map_some,
        C.coordinates.parentCopy_bad b (by omega)]

theorem root_ancestor_last (C : Context) {r : Nat} (hr : r ≤ C.level) :
    (C.mountain.row r).Ancestor C.coordinates.y C.coordinates.x :=
  C.mountain.refines_le hr C.last_parent

theorem root_copy_succ_eq (C : Context) (b : Nat) :
    C.coordinates.y+(b+1)*C.coordinates.length = C.coordinates.x+b*C.coordinates.length := by
  have h := C.coordinates.root_add_length
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem root_good_ancestor_low (C : Context) {r a : Nat}
    (hr : r < C.level) (ha : (C.mountain.row r).Ancestor a C.coordinates.y) (b : Nat) :
    (C.row r).Ancestor a (C.coordinates.y+b*C.coordinates.length) := by
  induction b with
  | zero =>
      simpa only [Nat.zero_mul, Nat.add_zero] using
        C.prefix_ancestor ha C.coordinates.root_lt_last
  | succ b ih =>
      rw [C.root_copy_succ_eq]
      exact ih.trans (C.low_ancestor_same_block hr
        (C.root_ancestor_last (Nat.le_of_lt hr)) (Nat.le_refl _) (Nat.le_refl _) b)

theorem low_parent_path (C : Context) {r c p : Nat}
    (hr : r < C.level) (hp : (C.mountain.row r).parent c = some p)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b p) (C.coordinates.parentCopy b c) := by
  have hleft := (C.mountain.row r).parent_left hp
  by_cases hbefore : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hbefore,
      C.coordinates.parentCopy_good b (by omega)]
    exact C.prefix_ancestor (ParentForest.Ancestor.direct hp)
      (by have := C.coordinates.root_lt_last; omega)
  · by_cases hequal : c = C.coordinates.y
    · subst c
      rw [C.coordinates.parentCopy_bad b (Nat.le_refl _),
        C.coordinates.parentCopy_good b hleft]
      exact C.root_good_ancestor_low hr (ParentForest.Ancestor.direct hp) b
    · have hafter : C.coordinates.y < c := by omega
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hafter)]
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode_low hafter hc hr b, hp, Option.map_some]

theorem low_ancestor_copy (C : Context) {r a c : Nat}
    (hr : r < C.level) (ha : (C.mountain.row r).Ancestor a c)
    (hc : c ≤ C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp => exact C.low_parent_path hr hp hc b
  | @step p c ha hp ih =>
      have hleft := (C.mountain.row r).parent_left hp
      exact (ih (by omega)).trans (C.low_parent_path hr hp hc b)

theorem parent_root_copy_high (C : Context) {r : Nat} (hr : C.level ≤ r) (b : Nat) :
    C.parent r (C.coordinates.y+b*C.coordinates.length) =
      (C.mountain.row r).parent C.coordinates.y := by
  cases b with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact C.parent_original C.coordinates.root_lt_last r
  | succ b =>
      rw [C.root_copy_succ_eq]
      change C.parent r (C.coordinates.encode C.coordinates.x b) = _
      rw [C.parent_encode C.coordinates.root_lt_last (Nat.le_refl _) b r,
        if_pos ⟨rfl, hr⟩]

theorem high_parent_path (C : Context) {r c p : Nat}
    (hr : C.level ≤ r) (hp : (C.mountain.row r).parent c = some p)
    (hc : c < C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b p) (C.coordinates.parentCopy b c) := by
  have hleft := (C.mountain.row r).parent_left hp
  by_cases hbefore : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hbefore,
      C.coordinates.parentCopy_good b (by omega)]
    exact C.prefix_ancestor (ParentForest.Ancestor.direct hp) hc
  · by_cases hequal : c = C.coordinates.y
    · subst c
      rw [C.coordinates.parentCopy_bad b (Nat.le_refl _),
        C.coordinates.parentCopy_good b hleft]
      exact ParentForest.Ancestor.direct ((C.parent_root_copy_high hr b).trans hp)
    · have hafter : C.coordinates.y < c := by omega
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hafter)]
      apply ParentForest.Ancestor.direct
      change C.parent r (C.coordinates.encode c b) = _
      rw [C.parent_encode hafter (Nat.le_of_lt hc) b r,
        if_neg (by intro h; omega), hp, Option.map_some]

theorem high_ancestor_copy (C : Context) {r a c : Nat}
    (hr : C.level ≤ r) (ha : (C.mountain.row r).Ancestor a c)
    (hc : c < C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp => exact C.high_parent_path hr hp hc b
  | @step p c ha hp ih =>
      have hleft := (C.mountain.row r).parent_left hp
      exact (ih (by omega)).trans (C.high_parent_path hr hp hc b)

theorem nested_succ_encoded (C : Context) {s r p : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat)
    (hp : C.parent (r+1) (C.coordinates.encode s b) = some p) :
    (C.row r).Ancestor p (C.coordinates.encode s b) := by
  rw [C.parent_encode hs hx b (r+1)] at hp
  by_cases hseam : s = C.coordinates.x
  · subst s
    by_cases hhigh : C.level ≤ r+1
    · rw [if_pos ⟨rfl, hhigh⟩] at hp
      have ha := C.mountain.nested_succ r hp
      have hpGood := (C.mountain.row (r+1)).parent_left hp
      by_cases hlower : C.level ≤ r
      · have ht := C.high_ancestor_copy hlower ha C.coordinates.root_lt_last (b+1)
        rw [C.coordinates.parentCopy_good (b+1) hpGood,
          C.coordinates.parentCopy_bad (b+1) (Nat.le_refl _), C.root_copy_succ_eq] at ht
        exact ht
      · have hlow : r < C.level := by omega
        have hpath := ha.trans (C.root_ancestor_last (Nat.le_of_lt hlow))
        have ht := C.low_ancestor_copy hlow hpath (Nat.le_refl _) b
        rw [C.coordinates.parentCopy_good b hpGood,
          C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last)] at ht
        exact ht
    · rw [if_neg (by intro h; omega)] at hp
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
      have ht := C.low_ancestor_copy (by omega : r < C.level)
        (C.mountain.nested_succ r hq) (Nat.le_refl _) b
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last), heq] at ht
      exact ht
  · rw [if_neg (by intro h; exact hseam h.1)] at hp
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
    have ha := C.mountain.nested_succ r hq
    by_cases hlow : r < C.level
    · have ht := C.low_ancestor_copy hlow ha hx b
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs), heq] at ht
      exact ht
    · have ht := C.high_ancestor_copy (by omega) ha (by omega : s < C.coordinates.x) b
      rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hs), heq] at ht
      exact ht

theorem nested_succ (C : Context) (r : Nat) : (C.row (r+1)).Refines (C.row r) := by
  intro c p hp
  by_cases hold : c < C.coordinates.x
  · change C.parent (r+1) c = some p at hp
    rw [C.parent_original hold (r+1)] at hp
    exact C.prefix_ancestor (C.mountain.nested_succ r hp) hold
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have hs := C.coordinates.source_bounds c
    have he := C.coordinates.encode_coordinates hc
    have ht := C.nested_succ_encoded hs.1 hs.2 (C.coordinates.block c)
      (by rw [he]; exact hp)
    rw [he] at ht
    exact ht

def toRowMountain (C : Context) : RootGeometry.RowMountain where
  height := C.height
  row := C.row
  parent_exists _ _ hr := C.parent_exists hr
  parent_source := C.parent_source
  parent_endpoint := C.parent_endpoint
  nested_succ := C.nested_succ

end OneY.TerminalCopy.Context

#print axioms OneY.TerminalCopy.Context.root_good_ancestor_low
#print axioms OneY.TerminalCopy.Context.nested_succ
#print axioms OneY.TerminalCopy.Context.toRowMountain
