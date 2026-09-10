import OneY.CopyCoordinates
import OneY.RootGeometry

/-!
# Ordinary copies of layers above the active layer

These coordinates use sources in `[y,x)`: the new block's first column
is an ordinary copy of the root. Every parent moves within the same block,
except that parents in the good prefix retain their original positions.
-/

namespace OneY.OrdinaryCopy

structure Context where
  mountain : RootGeometry.RowMountain
  coordinates : CopyCoordinates.Context

namespace Context

def source0 (C : Context) (c : Nat) : Nat :=
  if c < C.coordinates.y then c
  else C.coordinates.y + (c-C.coordinates.y)%C.coordinates.length

def block0 (C : Context) (c : Nat) : Nat :=
  if c < C.coordinates.y then 0 else (c-C.coordinates.y)/C.coordinates.length

theorem source0_good (C : Context) {c : Nat} (hc : c < C.coordinates.y) :
    C.source0 c = c := by simp only [source0, if_pos hc]

theorem block0_good (C : Context) {c : Nat} (hc : c < C.coordinates.y) :
    C.block0 c = 0 := by simp only [block0, if_pos hc]

theorem source0_bounds (C : Context) (c : Nat) : C.source0 c < C.coordinates.x := by
  by_cases hgood : c < C.coordinates.y
  · rw [C.source0_good hgood]
    exact Nat.lt_trans hgood C.coordinates.root_lt_last
  · have hm := Nat.mod_lt (c-C.coordinates.y) C.coordinates.length_pos
    have hx := C.coordinates.root_add_length
    simp only [source0, if_neg hgood]
    omega

theorem source0_bad_ge (C : Context) {c : Nat} (hc : C.coordinates.y ≤ c) :
    C.coordinates.y ≤ C.source0 c := by
  simp only [source0, if_neg (Nat.not_lt.mpr hc)]
  omega

theorem source0_encode (C : Context) {s : Nat}
    (hs : C.coordinates.y ≤ s) (hx : s < C.coordinates.x) (b : Nat) :
    C.source0 (C.coordinates.encode s b) = s := by
  have hge : C.coordinates.y ≤ C.coordinates.encode s b := by
    unfold CopyCoordinates.Context.encode
    omega
  have hoff : C.coordinates.encode s b-C.coordinates.y =
      (s-C.coordinates.y)+b*C.coordinates.length := by
    unfold CopyCoordinates.Context.encode
    omega
  have hsmall : s-C.coordinates.y < C.coordinates.length := by
    have := C.coordinates.root_add_length
    omega
  simp only [source0, if_neg (Nat.not_lt.mpr hge), hoff,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsmall]
  omega

theorem block0_encode (C : Context) {s : Nat}
    (hs : C.coordinates.y ≤ s) (hx : s < C.coordinates.x) (b : Nat) :
    C.block0 (C.coordinates.encode s b) = b := by
  have hge : C.coordinates.y ≤ C.coordinates.encode s b := by
    unfold CopyCoordinates.Context.encode
    omega
  have hoff : C.coordinates.encode s b-C.coordinates.y =
      (s-C.coordinates.y)+b*C.coordinates.length := by
    unfold CopyCoordinates.Context.encode
    omega
  have hsmall : s-C.coordinates.y < C.coordinates.length := by
    have := C.coordinates.root_add_length
    omega
  simp only [block0, if_neg (Nat.not_lt.mpr hge), hoff,
    Nat.add_mul_div_right _ _ C.coordinates.length_pos, Nat.div_eq_of_lt hsmall,
    Nat.zero_add]

theorem encode_coordinates (C : Context) (c : Nat) :
    C.coordinates.encode (C.source0 c) (C.block0 c) = c := by
  by_cases hgood : c < C.coordinates.y
  · simp only [C.source0_good hgood, C.block0_good hgood,
      CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero]
  · have h := Nat.mod_add_div' (c-C.coordinates.y) C.coordinates.length
    simp only [source0, block0, if_neg hgood, CopyCoordinates.Context.encode]
    omega

theorem original_coordinates (C : Context) {c : Nat} (hc : c < C.coordinates.x) :
    C.source0 c = c ∧ C.block0 c = 0 := by
  by_cases hgood : c < C.coordinates.y
  · exact ⟨C.source0_good hgood, C.block0_good hgood⟩
  · have hs : C.coordinates.y ≤ c := by omega
    have he : C.coordinates.encode c 0 = c := by simp [CopyCoordinates.Context.encode]
    exact ⟨by simpa only [he] using C.source0_encode hs hc 0,
      by simpa only [he] using C.block0_encode hs hc 0⟩

theorem source0_parentCopy (C : Context) {p : Nat} (hp : p < C.coordinates.x) (b : Nat) :
    C.source0 (C.coordinates.parentCopy b p) = p := by
  by_cases hgood : p < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hgood, C.source0_good hgood]
  · rw [C.coordinates.parentCopy_bad b (by omega)]
    exact C.source0_encode (by omega) hp b

def copyValue (C : Context) (v : Nat → Nat) (c : Nat) : Nat := v (C.source0 c)

def height (C : Context) (c : Nat) : Nat := C.copyValue C.mountain.height c

def parent (C : Context) (r c : Nat) : Option Nat :=
  ((C.mountain.row r).parent (C.source0 c)).map (C.coordinates.parentCopy (C.block0 c))

theorem copyValue_original (C : Context) (v : Nat → Nat) {c : Nat}
    (hc : c < C.coordinates.x) : C.copyValue v c = v c := by
  unfold copyValue
  rw [(C.original_coordinates hc).1]

theorem copyValue_parentCopy (C : Context) (v : Nat → Nat) {p : Nat}
    (hp : p < C.coordinates.x) (b : Nat) :
    C.copyValue v (C.coordinates.parentCopy b p) = v p := by
  unfold copyValue
  rw [C.source0_parentCopy hp b]

theorem height_original (C : Context) {c : Nat} (hc : c < C.coordinates.x) :
    C.height c = C.mountain.height c := C.copyValue_original _ hc

theorem height_parentCopy (C : Context) {p : Nat} (hp : p < C.coordinates.x) (b : Nat) :
    C.height (C.coordinates.parentCopy b p) = C.mountain.height p :=
  C.copyValue_parentCopy _ hp b

theorem parent_original (C : Context) {c : Nat} (hc : c < C.coordinates.x) (r : Nat) :
    C.parent r c = (C.mountain.row r).parent c := by
  simp only [parent, (C.original_coordinates hc).1, (C.original_coordinates hc).2]
  cases (C.mountain.row r).parent c <;>
    simp only [Option.map_none, Option.map_some, C.coordinates.parentCopy_zero]

theorem parent_encode (C : Context) {s : Nat}
    (hs : C.coordinates.y ≤ s) (hx : s < C.coordinates.x) (b r : Nat) :
    C.parent r (C.coordinates.encode s b) =
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  simp only [parent, C.source0_encode hs hx b, C.block0_encode hs hx b]

theorem parent_parentCopy (C : Context) {c : Nat} (hc : c < C.coordinates.x) (b r : Nat) :
    C.parent r (C.coordinates.parentCopy b c) =
      ((C.mountain.row r).parent c).map (C.coordinates.parentCopy b) := by
  by_cases hgood : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hgood, C.parent_original hc r]
    cases hp : (C.mountain.row r).parent c with
    | none => rfl
    | some p =>
        have hleft := (C.mountain.row r).parent_left hp
        simp only [Option.map_some, C.coordinates.parentCopy_good b (by omega : p < C.coordinates.y)]
  · rw [C.coordinates.parentCopy_bad b (by omega)]
    exact C.parent_encode (by omega) hc b r

theorem parent_left (C : Context) {r c p : Nat} (hp : C.parent r c = some p) : p < c := by
  obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
  have hleft := (C.mountain.row r).parent_left hq
  have he := C.encode_coordinates c
  rw [← heq]
  unfold CopyCoordinates.Context.parentCopy
  split
  · unfold CopyCoordinates.Context.encode at he
    omega
  · unfold CopyCoordinates.Context.encode at he
    omega

theorem parent_source (C : Context) {r c p : Nat} (hp : C.parent r c = some p) :
    r < C.height c := by
  obtain ⟨q, hq, _⟩ := Option.map_eq_some_iff.mp hp
  exact C.mountain.parent_source hq

theorem parent_endpoint (C : Context) {r c p : Nat} (hp : C.parent r c = some p) :
    r ≤ C.height p := by
  obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
  have hleft := (C.mountain.row r).parent_left hq
  have hs := C.source0_bounds c
  rw [← heq, C.height_parentCopy (by omega : q < C.coordinates.x)]
  exact C.mountain.parent_endpoint hq

theorem parent_exists (C : Context) {r c : Nat} (hr : r < C.height c) :
    ∃ p, C.parent r c = some p := by
  obtain ⟨p, hp⟩ := C.mountain.parent_exists r (C.source0 c) hr
  exact ⟨C.coordinates.parentCopy (C.block0 c) p, by simp only [parent, hp, Option.map_some]⟩

theorem parent_none_iff (C : Context) (r c : Nat) :
    C.parent r c = none ↔ C.height c ≤ r := by
  constructor
  · intro hn
    by_cases hr : r < C.height c
    · obtain ⟨p, hp⟩ := C.parent_exists hr
      rw [hn] at hp
      cases hp
    · omega
  · intro hr
    cases hp : C.parent r c with
    | none => rfl
    | some p => have := C.parent_source hp; omega

def row (C : Context) (r : Nat) : ParentForest where
  parent := C.parent r
  parent_left := C.parent_left

theorem ancestor_copy (C : Context) {r a c : Nat}
    (ha : (C.mountain.row r).Ancestor a c) (hc : c < C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp =>
      exact ParentForest.Ancestor.direct
        (by change C.parent r _ = _; rw [C.parent_parentCopy hc b r, hp, Option.map_some])
  | @step p c ha hp ih =>
      have hleft := (C.mountain.row r).parent_left hp
      exact ParentForest.Ancestor.step (ih (by omega))
        (by change C.parent r _ = _; rw [C.parent_parentCopy hc b r, hp, Option.map_some])

theorem parentCopy_coordinates (C : Context) (c : Nat) :
    C.coordinates.parentCopy (C.block0 c) (C.source0 c) = c := by
  by_cases hgood : c < C.coordinates.y
  · rw [C.source0_good hgood, C.block0_good hgood, C.coordinates.parentCopy_zero]
  · rw [C.coordinates.parentCopy_bad _ (C.source0_bad_ge (by omega))]
    exact C.encode_coordinates c

theorem nested_succ (C : Context) (r : Nat) : (C.row (r+1)).Refines (C.row r) := by
  intro c p hp
  obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
  have ht := C.ancestor_copy (C.mountain.nested_succ r hq) (C.source0_bounds c) (C.block0 c)
  rw [C.parentCopy_coordinates, heq] at ht
  exact ht

def toRowMountain (C : Context) : RootGeometry.RowMountain where
  height := C.height
  row := C.row
  parent_exists _ _ hr := C.parent_exists hr
  parent_source := C.parent_source
  parent_endpoint := C.parent_endpoint
  nested_succ := C.nested_succ

end Context

#print axioms Context.encode_coordinates
#print axioms Context.parent_left
#print axioms Context.parent_endpoint
#print axioms Context.nested_succ
#print axioms Context.toRowMountain

end OneY.OrdinaryCopy
