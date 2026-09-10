import Std

/-!
# Copy coordinates, including the deleted-last-column seam

Sources belong to `(y,x]`, not `[y,x)`.  Thus source `x` denotes a seam,
and the first retained seam at column `x` has block index zero.
-/

namespace OneY.CopyCoordinates

structure Context where
  y : Nat
  x : Nat
  root_lt_last : y < x

namespace Context

def length (C : Context) : Nat := C.x-C.y
def width (C : Context) (N : Nat) : Nat := C.x + N*C.length
def source (C : Context) (c : Nat) : Nat :=
  C.y+1 + (c-C.y-1)%C.length
def block (C : Context) (c : Nat) : Nat := (c-C.y-1)/C.length
def encode (C : Context) (s b : Nat) : Nat := s+b*C.length
def parentCopy (C : Context) (b p : Nat) : Nat :=
  if p < C.y then p else p+b*C.length

theorem length_pos (C : Context) : 0 < C.length := by
  unfold length
  have := C.root_lt_last
  omega

theorem root_add_length (C : Context) : C.y+C.length = C.x := by
  unfold length
  have := C.root_lt_last
  omega

theorem source_bounds (C : Context) (c : Nat) : C.y < C.source c ∧ C.source c ≤ C.x := by
  have hm := Nat.mod_lt (c-C.y-1) C.length_pos
  have hx := C.root_add_length
  unfold source
  omega

theorem encode_coordinates (C : Context) {c : Nat} (hc : C.y < c) :
    C.encode (C.source c) (C.block c) = c := by
  have h := Nat.mod_add_div' (c-C.y-1) C.length
  unfold encode source block
  omega

theorem source_encode (C : Context) {s : Nat} (hs : C.y < s) (hx : s ≤ C.x)
    (b : Nat) : C.source (C.encode s b) = s := by
  have hSmall : s-C.y-1 < C.length := by
    have := C.root_add_length
    omega
  have hOffset : C.encode s b-C.y-1 = (s-C.y-1)+b*C.length := by
    unfold encode
    omega
  unfold source
  rw [hOffset, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hSmall]
  omega

theorem block_encode (C : Context) {s : Nat} (hs : C.y < s) (hx : s ≤ C.x)
    (b : Nat) : C.block (C.encode s b) = b := by
  have hSmall : s-C.y-1 < C.length := by
    have := C.root_add_length
    omega
  have hOffset : C.encode s b-C.y-1 = (s-C.y-1)+b*C.length := by
    unfold encode
    omega
  unfold block
  rw [hOffset, Nat.add_mul_div_right _ _ C.length_pos,
    Nat.div_eq_of_lt hSmall, Nat.zero_add]

theorem coordinates_unique (C : Context) {c s b : Nat}
    (hs : C.y < s) (hx : s ≤ C.x) (he : C.encode s b = c) :
    C.source c = s ∧ C.block c = b := by
  rw [← he]
  exact ⟨C.source_encode hs hx b, C.block_encode hs hx b⟩

theorem encode_injective (C : Context) {s t b d : Nat}
    (hs : C.y < s) (hsx : s ≤ C.x) (ht : C.y < t) (htx : t ≤ C.x)
    (he : C.encode s b = C.encode t d) : s = t ∧ b = d := by
  have h := C.coordinates_unique hs hsx he
  rw [C.source_encode ht htx d, C.block_encode ht htx d] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem original_coordinates (C : Context) {c : Nat}
    (hc : C.y < c) (hx : c ≤ C.x) : C.source c = c ∧ C.block c = 0 := by
  have he : C.encode c 0 = c := by simp [encode]
  exact C.coordinates_unique hc hx he

theorem seam_coordinates (C : Context) (b : Nat) :
    C.source (C.encode C.x b) = C.x ∧ C.block (C.encode C.x b) = b :=
  ⟨C.source_encode C.root_lt_last (Nat.le_refl _) b,
   C.block_encode C.root_lt_last (Nat.le_refl _) b⟩

theorem encoded_lt_width_iff (C : Context) {s : Nat}
    (hs : C.y < s) (hx : s ≤ C.x) (b N : Nat) :
    C.encode s b < C.width N ↔ b < N ∨ (b = N ∧ s < C.x) := by
  have hL := C.length_pos
  have hRoot := C.root_add_length
  unfold encode width
  constructor
  · intro h
    have hb : b ≤ N := by
      by_cases hb : b ≤ N
      · exact hb
      · have hm := Nat.mul_le_mul_right C.length (by omega : N+1 ≤ b)
        rw [Nat.add_mul, Nat.one_mul] at hm
        omega
    by_cases hb' : b < N
    · exact Or.inl hb'
    · have he : b = N := by omega
      apply Or.inr
      refine ⟨he, ?_⟩
      rw [he] at h
      omega
  · intro h
    rcases h with hLess | ⟨rfl, hSource⟩
    · have hm := Nat.mul_lt_mul_of_pos_right hLess hL
      omega
    · omega

theorem coordinates_in_width (C : Context) {c N : Nat}
    (hc : C.y < c) (hWidth : c < C.width N) :
    C.block c < N ∨ (C.block c = N ∧ C.source c < C.x) := by
  have hs := C.source_bounds c
  apply (C.encoded_lt_width_iff hs.1 hs.2 (C.block c) N).mp
  rw [C.encode_coordinates hc]
  exact hWidth

theorem block_le_of_in_width (C : Context) {c N : Nat}
    (hc : C.y < c) (hWidth : c < C.width N) : C.block c ≤ N := by
  rcases C.coordinates_in_width hc hWidth with h | ⟨h,_⟩ <;> omega

theorem seam_lt_width_iff (C : Context) (b N : Nat) :
    C.encode C.x b < C.width N ↔ b < N := by
  rw [C.encoded_lt_width_iff C.root_lt_last (Nat.le_refl _) b N]
  simp

theorem parentCopy_zero (C : Context) (p : Nat) : C.parentCopy 0 p = p := by
  simp [parentCopy]

theorem parentCopy_good (C : Context) (b : Nat) {p : Nat} (hp : p < C.y) :
    C.parentCopy b p = p := by simp [parentCopy, hp]

theorem parentCopy_bad (C : Context) (b : Nat) {p : Nat} (hp : C.y ≤ p) :
    C.parentCopy b p = p+b*C.length := by simp [parentCopy, Nat.not_lt.mpr hp]

theorem parentCopy_lt_encode (C : Context) {p s : Nat} (hSource : C.y < s)
    (hp : p < s) (b : Nat) : C.parentCopy b p < C.encode s b := by
  unfold parentCopy encode
  split <;> omega

theorem parentCopy_lt_column (C : Context) {p c : Nat} (hc : C.y < c)
    (hp : p < C.source c) : C.parentCopy (C.block c) p < c := by
  have h := C.parentCopy_lt_encode (C.source_bounds c).1 hp (C.block c)
  rw [C.encode_coordinates hc] at h
  exact h

end Context

#print axioms Context.coordinates_unique
#print axioms Context.encoded_lt_width_iff
#print axioms Context.parentCopy_lt_column

end OneY.CopyCoordinates
