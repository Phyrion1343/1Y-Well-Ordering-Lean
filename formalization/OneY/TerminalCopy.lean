import OneY.CopyCoordinates
import OneY.RootGeometry

/-!
# The actual parent graph copied in the active finite layer

The retained seam `x + b L = y + (b+1)L` has the root column's height.
Below the active row it keeps the old last-column parent relation; at and
above that row it uses the root column's shape, whose parents stay in the
good prefix. Other columns use the ordinary parent-copy map.
-/

namespace OneY.TerminalCopy

open RootGeometry

structure Context where
  mountain : RowMountain
  coordinates : CopyCoordinates.Context
  level : Nat
  last_parent : (mountain.row level).parent coordinates.x = some coordinates.y
  last_height : mountain.height coordinates.x = level + 1

namespace Context

theorem root_height_ge (C : Context) : C.level ≤ C.mountain.height C.coordinates.y :=
  C.mountain.parent_endpoint C.last_parent

def height (C : Context) (c : Nat) : Nat :=
  if c < C.coordinates.x then C.mountain.height c
  else if C.coordinates.source c = C.coordinates.x then C.mountain.height C.coordinates.y
  else C.mountain.height (C.coordinates.source c)

def parent (C : Context) (r c : Nat) : Option Nat :=
  if c < C.coordinates.x then (C.mountain.row r).parent c
  else if C.coordinates.source c = C.coordinates.x ∧ C.level ≤ r then
    (C.mountain.row r).parent C.coordinates.y
  else ((C.mountain.row r).parent (C.coordinates.source c)).map
    (C.coordinates.parentCopy (C.coordinates.block c))

theorem height_original (C : Context) {c : Nat} (hc : c < C.coordinates.x) :
    C.height c = C.mountain.height c := by simp only [height, if_pos hc]

theorem parent_original (C : Context) {c : Nat} (hc : c < C.coordinates.x) (r : Nat) :
    C.parent r c = (C.mountain.row r).parent c := by simp only [parent, if_pos hc]

theorem encode_succ_gt_last (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (b : Nat) : C.coordinates.x < C.coordinates.encode s (b+1) := by
  have h := C.coordinates.root_add_length
  unfold CopyCoordinates.Context.encode
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem height_encode (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.height (C.coordinates.encode s b) =
      if s = C.coordinates.x then C.mountain.height C.coordinates.y
      else C.mountain.height s := by
  cases b with
  | zero =>
      simp only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero]
      by_cases he : s = C.coordinates.x
      · subst s
        simp only [height, Nat.lt_irrefl, ↓reduceIte,
          (C.coordinates.original_coordinates C.coordinates.root_lt_last (Nat.le_refl _)).1]
      · have hsx : s < C.coordinates.x := by omega
        rw [C.height_original hsx, if_neg he]
  | succ b =>
      have hnew := C.encode_succ_gt_last hs b
      simp only [height, Nat.not_lt.mpr (Nat.le_of_lt hnew), ↓reduceIte,
        C.coordinates.source_encode hs hx (b+1)]

theorem height_root_copy (C : Context) (b : Nat) :
    C.height (C.coordinates.y+b*C.coordinates.length) =
      C.mountain.height C.coordinates.y := by
  cases b with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact C.height_original C.coordinates.root_lt_last
  | succ b =>
      have he : C.coordinates.y+(b+1)*C.coordinates.length =
          C.coordinates.encode C.coordinates.x b := by
        have h := C.coordinates.root_add_length
        unfold CopyCoordinates.Context.encode
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [he, C.height_encode C.coordinates.root_lt_last (Nat.le_refl _) b, if_pos rfl]

theorem height_parentCopy (C : Context) {p : Nat} (hp : p < C.coordinates.x)
    (b : Nat) : C.height (C.coordinates.parentCopy b p) = C.mountain.height p := by
  by_cases hgood : p < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hgood, C.height_original hp]
  · by_cases heq : p = C.coordinates.y
    · subst p
      rw [C.coordinates.parentCopy_bad b (Nat.le_refl _), C.height_root_copy]
    · have hafter : C.coordinates.y < p := by omega
      rw [C.coordinates.parentCopy_bad b (by omega)]
      change C.height (C.coordinates.encode p b) = C.mountain.height p
      rw [C.height_encode hafter (Nat.le_of_lt hp) b,
        if_neg (by omega : p ≠ C.coordinates.x)]

theorem parent_encode (C : Context) {s : Nat} (hs : C.coordinates.y < s)
    (hx : s ≤ C.coordinates.x) (b r : Nat) :
    C.parent r (C.coordinates.encode s b) =
      if s = C.coordinates.x ∧ C.level ≤ r then (C.mountain.row r).parent C.coordinates.y
      else ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  cases b with
  | zero =>
      simp only [CopyCoordinates.Context.encode, Nat.zero_mul, Nat.add_zero]
      by_cases he : s = C.coordinates.x
      · subst s
        simp only [parent, Nat.lt_irrefl, ↓reduceIte,
          (C.coordinates.original_coordinates C.coordinates.root_lt_last (Nat.le_refl _)).1,
          (C.coordinates.original_coordinates C.coordinates.root_lt_last (Nat.le_refl _)).2]
      · have hsx : s < C.coordinates.x := by omega
        rw [C.parent_original hsx r, if_neg (by simp only [he, false_and, not_false_eq_true])]
        cases (C.mountain.row r).parent s <;> simp only [Option.map_none,
          Option.map_some, C.coordinates.parentCopy_zero]
  | succ b =>
      have hnew := C.encode_succ_gt_last hs b
      simp only [parent, Nat.not_lt.mpr (Nat.le_of_lt hnew), ↓reduceIte,
        C.coordinates.source_encode hs hx (b+1), C.coordinates.block_encode hs hx (b+1)]

theorem parent_left (C : Context) {r c p : Nat} (hp : C.parent r c = some p) : p < c := by
  by_cases hold : c < C.coordinates.x
  · rw [C.parent_original hold r] at hp
    exact (C.mountain.row r).parent_left hp
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    simp only [parent, if_neg hold] at hp
    split at hp
    · have h := (C.mountain.row r).parent_left hp
      omega
    · obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
      rw [← heq]
      exact C.coordinates.parentCopy_lt_column hc ((C.mountain.row r).parent_left hq)

theorem parent_source (C : Context) {r c p : Nat} (hp : C.parent r c = some p) :
    r < C.height c := by
  by_cases hold : c < C.coordinates.x
  · rw [C.parent_original hold r] at hp
    rw [C.height_original hold]
    exact C.mountain.parent_source hp
  · simp only [parent, if_neg hold] at hp
    simp only [height, if_neg hold]
    by_cases hseam : C.coordinates.source c = C.coordinates.x
    · rw [if_pos hseam]
      by_cases hhigh : C.level ≤ r
      · rw [if_pos ⟨hseam, hhigh⟩] at hp
        exact C.mountain.parent_source hp
      · have hh := C.root_height_ge
        omega
    · rw [if_neg hseam]
      rw [if_neg (by simp only [hseam, false_and, not_false_eq_true])] at hp
      obtain ⟨q, hq, _⟩ := Option.map_eq_some_iff.mp hp
      exact C.mountain.parent_source hq

theorem parent_endpoint (C : Context) {r c p : Nat} (hp : C.parent r c = some p) :
    r ≤ C.height p := by
  by_cases hold : c < C.coordinates.x
  · rw [C.parent_original hold r] at hp
    have hleft := (C.mountain.row r).parent_left hp
    rw [C.height_original (by omega : p < C.coordinates.x)]
    exact C.mountain.parent_endpoint hp
  · simp only [parent, if_neg hold] at hp
    split at hp
    · have hleft := (C.mountain.row r).parent_left hp
      have hxy := C.coordinates.root_lt_last
      rw [C.height_original (by omega : p < C.coordinates.x)]
      exact C.mountain.parent_endpoint hp
    · obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
      have hleft := (C.mountain.row r).parent_left hq
      have hbound := (C.coordinates.source_bounds c).2
      rw [← heq, C.height_parentCopy (by omega : q < C.coordinates.x)]
      exact C.mountain.parent_endpoint hq

theorem parent_exists (C : Context) {r c : Nat} (hr : r < C.height c) :
    ∃ p, C.parent r c = some p := by
  by_cases hold : c < C.coordinates.x
  · rw [C.height_original hold] at hr
    obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hr
    exact ⟨p, by rw [C.parent_original hold r]; exact hp⟩
  · simp only [height, if_neg hold] at hr
    by_cases hseam : C.coordinates.source c = C.coordinates.x
    · rw [if_pos hseam] at hr
      by_cases hhigh : C.level ≤ r
      · obtain ⟨p, hp⟩ := C.mountain.parent_exists r C.coordinates.y hr
        exact ⟨p, by simp [parent, hold, hseam, hhigh, hp]⟩
      · have hlast := C.last_height
        obtain ⟨p, hp⟩ := C.mountain.parent_exists r C.coordinates.x (by omega)
        refine ⟨C.coordinates.parentCopy (C.coordinates.block c) p, ?_⟩
        simp [parent, hold, hseam, hhigh, hp]
    · rw [if_neg hseam] at hr
      obtain ⟨p, hp⟩ := C.mountain.parent_exists r (C.coordinates.source c) hr
      refine ⟨C.coordinates.parentCopy (C.coordinates.block c) p, ?_⟩
      simp [parent, hold, hseam, hp]

theorem parent_exists_iff (C : Context) (r c : Nat) :
    (∃ p, C.parent r c = some p) ↔ r < C.height c :=
  ⟨fun ⟨_, hp⟩ => C.parent_source hp, C.parent_exists⟩

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

theorem parent_in_width (C : Context) {N r c p : Nat}
    (hc : c < C.coordinates.width N) (hp : C.parent r c = some p) :
    p < C.coordinates.width N := Nat.lt_trans (C.parent_left hp) hc

end Context

#print axioms Context.height_parentCopy
#print axioms Context.parent_left
#print axioms Context.parent_source
#print axioms Context.parent_endpoint
#print axioms Context.parent_none_iff

end OneY.TerminalCopy
