import OneY.CopyCoordinates
import OneY.RootGeometry

/-!
# The three-part lower-layer copy graph

This is the specified graph, before any numerical nearest-smaller check.
Its height and parent maps are actual definitions.
-/

namespace OneY.LowerCopy

open RootGeometry

structure Context where
  mountain : RowMountain
  coordinates : CopyCoordinates.Context
  last_root : mountain.rootAt (mountain.height coordinates.y) coordinates.x = coordinates.y
  last_higher : mountain.height coordinates.y < mountain.height coordinates.x

namespace Context

def floor (C : Context) : Nat := C.mountain.height C.coordinates.y
def rise (C : Context) : Nat := C.mountain.height C.coordinates.x-C.floor
def InCone (C : Context) (c : Nat) : Prop :=
  C.floor ≤ C.mountain.height c ∧ C.mountain.rootAt C.floor c = C.coordinates.y

instance (C : Context) (c : Nat) : Decidable (C.InCone c) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem rise_pos (C : Context) : 0 < C.rise := by
  have h := C.last_higher
  unfold rise floor
  omega

theorem last_height (C : Context) : C.mountain.height C.coordinates.x = C.floor+C.rise := by
  have h := C.last_higher
  unfold rise floor
  omega

theorem root_inCone (C : Context) : C.InCone C.coordinates.y :=
  ⟨Nat.le_refl _, C.mountain.top_root _⟩

theorem last_inCone (C : Context) : C.InCone C.coordinates.x :=
  ⟨Nat.le_of_lt C.last_higher, C.last_root⟩

theorem root_le_of_inCone (C : Context) {c : Nat} (hc : C.InCone c) :
    C.coordinates.y ≤ c := by
  have h := C.mountain.rootAt_le C.floor c
  rw [hc.2] at h
  exact h

theorem height_lt_of_inCone (C : Context) {c : Nat}
    (hc : C.InCone c) (hy : C.coordinates.y < c) : C.floor < C.mountain.height c := by
  by_cases h : C.floor < C.mountain.height c
  · exact h
  · have heq : C.floor = C.mountain.height c := by have := hc.1; omega
    have hr := C.mountain.top_root c
    rw [← heq, hc.2] at hr
    omega

def height (C : Context) (c : Nat) : Nat :=
  if c ≤ C.coordinates.x then C.mountain.height c
  else
    let s := C.coordinates.source c
    let b := C.coordinates.block c
    if C.InCone s then C.mountain.height s+b*C.rise else C.mountain.height s

theorem height_original (C : Context) {c : Nat} (hc : c ≤ C.coordinates.x) :
    C.height c = C.mountain.height c := by simp [height, hc]

theorem encode_succ_gt_last (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (b : Nat) :
    C.coordinates.x < C.coordinates.encode s (b+1) := by
  have h := C.coordinates.root_add_length
  unfold CopyCoordinates.Context.encode
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem height_encode (C : Context) {s : Nat}
    (hs : C.coordinates.y < s) (hx : s ≤ C.coordinates.x) (b : Nat) :
    C.height (C.coordinates.encode s b) =
      if C.InCone s then C.mountain.height s+b*C.rise else C.mountain.height s := by
  cases b with
  | zero => simp [CopyCoordinates.Context.encode, C.height_original hx]
  | succ b =>
      have hn := C.encode_succ_gt_last hs b
      simp only [height, Nat.not_le_of_gt hn, ↓reduceIte,
        C.coordinates.source_encode hs hx (b+1), C.coordinates.block_encode hs hx (b+1)]

theorem height_root_copy (C : Context) (b : Nat) :
    C.height (C.coordinates.y+b*C.coordinates.length) = C.floor+b*C.rise := by
  cases b with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact C.height_original (Nat.le_of_lt C.coordinates.root_lt_last)
  | succ b =>
      have he : C.coordinates.y+(b+1)*C.coordinates.length =
          C.coordinates.encode C.coordinates.x b := by
        have h := C.coordinates.root_add_length
        unfold CopyCoordinates.Context.encode
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [he, C.height_encode C.coordinates.root_lt_last (Nat.le_refl _) b,
        if_pos C.last_inCone, C.last_height, Nat.add_mul, Nat.one_mul]
      omega

theorem height_parentCopy (C : Context) {p : Nat} (hp : p ≤ C.coordinates.x) (b : Nat) :
    C.height (C.coordinates.parentCopy b p) =
      if C.InCone p then C.mountain.height p+b*C.rise else C.mountain.height p := by
  by_cases hGood : p < C.coordinates.y
  · have hNot : ¬C.InCone p := by
      intro h
      have := C.root_le_of_inCone h
      omega
    rw [C.coordinates.parentCopy_good b hGood, C.height_original hp, if_neg hNot]
  · by_cases hEq : p = C.coordinates.y
    · subst p
      rw [C.coordinates.parentCopy_bad b (Nat.le_refl _), C.height_root_copy,
        if_pos C.root_inCone]
      rfl
    · have hAfter : C.coordinates.y < p := by omega
      rw [C.coordinates.parentCopy_bad b (by omega)]
      exact C.height_encode hAfter hp b

theorem height_parentCopy_ge (C : Context) {p : Nat} (hp : p ≤ C.coordinates.x) (b : Nat) :
    C.mountain.height p ≤ C.height (C.coordinates.parentCopy b p) := by
  rw [C.height_parentCopy hp b]
  split <;> omega

theorem high_parent_inCone (C : Context) {s p u : Nat}
    (hs : C.InCone s) (hu : C.floor ≤ u)
    (hp : (C.mountain.row u).parent s = some p) : C.InCone p := by
  have he := C.mountain.nested_roots hu hp
  exact ⟨Nat.le_trans hu (C.mountain.parent_endpoint hp), he.symm.trans hs.2⟩

def parent (C : Context) (r c : Nat) : Option Nat :=
  if c ≤ C.coordinates.x then (C.mountain.row r).parent c
  else
    let s := C.coordinates.source c
    let b := C.coordinates.block c
    if C.InCone s ∧ C.floor ≤ r then
      if r < C.floor+b*C.rise then
        ((C.mountain.row C.floor).parent s).map (fun p => p+b*C.coordinates.length)
      else
        ((C.mountain.row (r-b*C.rise)).parent s).map (fun p => p+b*C.coordinates.length)
    else
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b)

theorem parent_original (C : Context) {r c : Nat} (hc : c ≤ C.coordinates.x) :
    C.parent r c = (C.mountain.row r).parent c := by simp [parent, hc]

theorem parent_left (C : Context) {r c p : Nat} (hp : C.parent r c = some p) : p < c := by
  by_cases hOld : c ≤ C.coordinates.x
  · rw [C.parent_original hOld] at hp
    exact (C.mountain.row r).parent_left hp
  · have hc : C.coordinates.y < c := by have := C.coordinates.root_lt_last; omega
    have he := C.coordinates.encode_coordinates hc
    have hs := C.coordinates.source_bounds c
    simp only [parent, hOld, ↓reduceIte] at hp
    split at hp
    · split at hp
      · obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        have hqLt := (C.mountain.row C.floor).parent_left hq
        unfold CopyCoordinates.Context.encode at he
        omega
      · obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        have hqLt := (C.mountain.row (r-C.coordinates.block c*C.rise)).parent_left hq
        unfold CopyCoordinates.Context.encode at he
        omega
    · obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
      rw [← heq]
      exact C.coordinates.parentCopy_lt_column hc ((C.mountain.row r).parent_left hq)

theorem height_new (C : Context) {c : Nat} (hc : C.coordinates.x < c) :
    C.height c = if C.InCone (C.coordinates.source c) then
      C.mountain.height (C.coordinates.source c)+C.coordinates.block c*C.rise
      else C.mountain.height (C.coordinates.source c) := by
  simp only [height, Nat.not_le_of_gt hc, ↓reduceIte]

theorem shifted_parent_height (C : Context) {s p u : Nat}
    (hs : C.InCone s) (hx : s ≤ C.coordinates.x) (hu : C.floor ≤ u)
    (hp : (C.mountain.row u).parent s = some p) (b : Nat) :
    C.height (p+b*C.coordinates.length) = C.mountain.height p+b*C.rise := by
  have hCone := C.high_parent_inCone hs hu hp
  have hRoot := C.root_le_of_inCone hCone
  have hLeft := (C.mountain.row u).parent_left hp
  rw [← C.coordinates.parentCopy_bad b hRoot,
    C.height_parentCopy (by omega) b, if_pos hCone]

theorem parent_source (C : Context) {r c p : Nat}
    (hp : C.parent r c = some p) : r < C.height c := by
  by_cases hOld : c ≤ C.coordinates.x
  · rw [C.parent_original hOld] at hp
    rw [C.height_original hOld]
    exact C.mountain.parent_source hp
  · have hNew : C.coordinates.x < c := by omega
    rw [C.height_new hNew]
    simp only [parent, hOld, ↓reduceIte] at hp
    by_cases hMove : C.InCone (C.coordinates.source c) ∧ C.floor ≤ r
    · rw [if_pos hMove] at hp
      rw [if_pos hMove.1]
      by_cases hGap : r < C.floor+C.coordinates.block c*C.rise
      · rw [if_pos hGap] at hp
        have hh := hMove.1.1
        omega
      · rw [if_neg hGap] at hp
        obtain ⟨q, hq, _⟩ := Option.map_eq_some_iff.mp hp
        have hh := C.mountain.parent_source hq
        omega
    · rw [if_neg hMove] at hp
      obtain ⟨q, hq, _⟩ := Option.map_eq_some_iff.mp hp
      have hh := C.mountain.parent_source hq
      split <;> omega

theorem parent_endpoint (C : Context) {r c p : Nat}
    (hp : C.parent r c = some p) : r ≤ C.height p := by
  by_cases hOld : c ≤ C.coordinates.x
  · rw [C.parent_original hOld] at hp
    have hLeft := (C.mountain.row r).parent_left hp
    rw [C.height_original (by omega : p ≤ C.coordinates.x)]
    exact C.mountain.parent_endpoint hp
  · have hs := C.coordinates.source_bounds c
    simp only [parent, hOld, ↓reduceIte] at hp
    by_cases hMove : C.InCone (C.coordinates.source c) ∧ C.floor ≤ r
    · rw [if_pos hMove] at hp
      by_cases hGap : r < C.floor+C.coordinates.block c*C.rise
      · rw [if_pos hGap] at hp
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        rw [← heq, C.shifted_parent_height hMove.1 hs.2 (Nat.le_refl _) hq]
        have hh := C.mountain.parent_endpoint hq
        omega
      · rw [if_neg hGap] at hp
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
        have hFloor : C.floor ≤ r-C.coordinates.block c*C.rise := by omega
        rw [← heq, C.shifted_parent_height hMove.1 hs.2 hFloor hq]
        have hh := C.mountain.parent_endpoint hq
        omega
    · rw [if_neg hMove] at hp
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
      rw [← heq]
      have hLeft := (C.mountain.row r).parent_left hq
      exact Nat.le_trans (C.mountain.parent_endpoint hq)
        (C.height_parentCopy_ge (by omega) (C.coordinates.block c))

theorem parent_exists (C : Context) {r c : Nat} (hr : r < C.height c) :
    ∃ p, C.parent r c = some p := by
  by_cases hOld : c ≤ C.coordinates.x
  · rw [C.height_original hOld] at hr
    obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hr
    exact ⟨p, by rw [C.parent_original hOld]; exact hp⟩
  · have hNew : C.coordinates.x < c := by omega
    have hs := C.coordinates.source_bounds c
    rw [C.height_new hNew] at hr
    by_cases hCone : C.InCone (C.coordinates.source c)
    · rw [if_pos hCone] at hr
      by_cases hLow : r < C.floor
      · have hMove : ¬(C.InCone (C.coordinates.source c) ∧ C.floor ≤ r) := by
          intro h; omega
        have hh := hCone.1
        obtain ⟨q, hq⟩ := C.mountain.parent_exists r (C.coordinates.source c) (by omega)
        refine ⟨C.coordinates.parentCopy (C.coordinates.block c) q, ?_⟩
        simp only [parent, hOld, ↓reduceIte, if_neg hMove, hq, Option.map_some]
      · have hMove : C.InCone (C.coordinates.source c) ∧ C.floor ≤ r := ⟨hCone, by omega⟩
        by_cases hGap : r < C.floor+C.coordinates.block c*C.rise
        · obtain ⟨q, hq⟩ := C.mountain.parent_exists C.floor (C.coordinates.source c)
            (C.height_lt_of_inCone hCone hs.1)
          refine ⟨q+C.coordinates.block c*C.coordinates.length, ?_⟩
          simp only [parent, hOld, ↓reduceIte, if_pos hMove, if_pos hGap, hq, Option.map_some]
        · have hu : r-C.coordinates.block c*C.rise < C.mountain.height (C.coordinates.source c) := by omega
          obtain ⟨q, hq⟩ := C.mountain.parent_exists _ _ hu
          refine ⟨q+C.coordinates.block c*C.coordinates.length, ?_⟩
          simp only [parent, hOld, ↓reduceIte, if_pos hMove, if_neg hGap, hq, Option.map_some]
    · rw [if_neg hCone] at hr
      have hMove : ¬(C.InCone (C.coordinates.source c) ∧ C.floor ≤ r) := by
        intro h; exact hCone h.1
      obtain ⟨q, hq⟩ := C.mountain.parent_exists r (C.coordinates.source c) hr
      refine ⟨C.coordinates.parentCopy (C.coordinates.block c) q, ?_⟩
      simp only [parent, hOld, ↓reduceIte, if_neg hMove, hq, Option.map_some]

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

/-- Actual leftward forests, not parent maps with leftwardness postulated. -/
def row (C : Context) (r : Nat) : ParentForest where
  parent := C.parent r
  parent_left := C.parent_left

/-- Restricting to the prescribed output width never discards the parent
endpoint of a retained column. -/
theorem parent_in_width (C : Context) {N r c p : Nat}
    (hc : c < C.coordinates.width N) (hp : C.parent r c = some p) :
    p < C.coordinates.width N :=
  Nat.lt_trans (C.parent_left hp) hc

end Context

#print axioms Context.height_parentCopy
#print axioms Context.parent_left
#print axioms Context.parent_source
#print axioms Context.parent_endpoint
#print axioms Context.parent_exists

end OneY.LowerCopy
