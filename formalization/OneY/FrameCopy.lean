import OneY.CopyCoordinates
import OneY.ForestBridge

/-! # Ordinary horizontal transport of an inherited candidate forest

The retained source interval is `(y,x]`. Thus each new root seam inherits
the old last column's candidate edge. No nearest-smaller correctness is
assumed in this definition or in its ancestor transport theorems.
-/

namespace OneY.FrameCopy

open CopyCoordinates

def parent (C : Context) (F : ParentForest) (c : Nat) : Option Nat :=
  if c ≤ C.x then F.parent c
  else (F.parent (C.source c)).map (C.parentCopy (C.block c))

theorem parent_left (C : Context) (F : ParentForest) {c p : Nat}
    (hp : parent C F c = some p) : p < c := by
  unfold parent at hp
  split at hp
  · exact F.parent_left hp
  · rename_i hAfter
    cases hOld : F.parent (C.source c) with
    | none => simp only [hOld, Option.map_none] at hp; contradiction
    | some q =>
        simp only [hOld, Option.map_some] at hp
        have he := Option.some.inj hp
        rw [← he]
        exact C.parentCopy_lt_column (by have := C.root_lt_last; omega) (F.parent_left hOld)

def forest (C : Context) (F : ParentForest) : ParentForest where
  parent := parent C F
  parent_left := parent_left C F

theorem parent_original (C : Context) (F : ParentForest) {c : Nat} (hc : c ≤ C.x) :
    parent C F c = F.parent c := by simp only [parent, if_pos hc]

theorem parent_encode (C : Context) (F : ParentForest) {s : Nat}
    (hs : C.y < s) (hx : s ≤ C.x) (b : Nat) :
    parent C F (C.encode s b) = (F.parent s).map (C.parentCopy b) := by
  cases b with
  | zero =>
      simp only [Context.encode, Nat.zero_mul, Nat.add_zero, parent_original C F hx]
      have he : C.parentCopy 0 = id := funext C.parentCopy_zero
      rw [he, Option.map_id]
      rfl
  | succ b =>
      have hAfter : C.x < C.encode s (b+1) := by
        have he := C.root_add_length
        unfold Context.encode
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [parent, if_neg (Nat.not_le.mpr hAfter), C.source_encode hs hx, C.block_encode hs hx]

theorem parent_nonroot (C : Context) (F : ParentForest) {s : Nat}
    (hs : s ≤ C.x) (hNot : s ≠ C.y) (b : Nat) :
    parent C F (C.parentCopy b s) = (F.parent s).map (C.parentCopy b) := by
  by_cases hGood : s < C.y
  · rw [C.parentCopy_good b hGood, parent_original C F hs]
    cases hp : F.parent s with
    | none => rfl
    | some p =>
        have hpg : p < C.y := by have := F.parent_left hp; omega
        rw [Option.map_some, C.parentCopy_good b hpg]
  · rw [C.parentCopy_bad b (by omega)]
    exact parent_encode C F (by omega) hs b

theorem prefix_ancestor (C : Context) (F : ParentForest) {a c : Nat}
    (ha : F.Ancestor a c) (hc : c ≤ C.x) : (forest C F).Ancestor a c := by
  induction ha with
  | direct hp => exact .direct (by change parent C F _ = _; rw [parent_original C F hc, hp])
  | step ha hp ih =>
      exact .step (ih (by have := F.parent_left hp; omega))
        (by change parent C F _ = _; rw [parent_original C F hc, hp])

theorem ancestor_same_block (C : Context) (F : ParentForest) {a c : Nat}
    (ha : F.Ancestor a c) (hy : C.y ≤ a) (hc : c ≤ C.x) (b : Nat) :
    (forest C F).Ancestor (a+b*C.length) (c+b*C.length) := by
  induction ha with
  | direct hp =>
      have hLeft := F.parent_left hp
      apply ParentForest.Ancestor.direct
      change parent C F (C.encode _ b) = _
      rw [parent_encode C F (by omega) hc b, hp, Option.map_some, C.parentCopy_bad b hy]
  | @step p c ha hp ih =>
      have hAP := ha.lt
      have hPC := F.parent_left hp
      apply ParentForest.Ancestor.step (ih (by omega))
      change parent C F (C.encode c b) = _
      rw [parent_encode C F (by omega) hc b, hp, Option.map_some, C.parentCopy_bad b (by omega)]

theorem root_copy_succ_eq (C : Context) (b : Nat) : C.y+(b+1)*C.length = C.x+b*C.length := by
  have he := C.root_add_length
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem root_good_ancestor (C : Context) (F : ParentForest) (hRoot : F.Ancestor C.y C.x)
    {a : Nat} (ha : F.Ancestor a C.y) (b : Nat) :
    (forest C F).Ancestor a (C.y+b*C.length) := by
  induction b with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero] using prefix_ancestor C F ha (Nat.le_of_lt C.root_lt_last)
  | succ b ih =>
      rw [root_copy_succ_eq]
      exact ih.trans (ancestor_same_block C F hRoot (Nat.le_refl _) (Nat.le_refl _) b)

theorem ancestor_copy (C : Context) (F : ParentForest) (hRoot : F.Ancestor C.y C.x)
    {a c : Nat} (ha : F.Ancestor a c) (hc : c ≤ C.x) (b : Nat) :
    (forest C F).Ancestor (C.parentCopy b a) (C.parentCopy b c) := by
  induction ha with
  | @direct c hp =>
      have hLeft := F.parent_left hp
      by_cases hGood : c < C.y
      · rw [C.parentCopy_good b hGood, C.parentCopy_good b (by omega)]
        exact prefix_ancestor C F (.direct hp) hc
      · by_cases hEq : c = C.y
        · subst c
          rw [C.parentCopy_bad b (Nat.le_refl _), C.parentCopy_good b hLeft]
          exact root_good_ancestor C F hRoot (.direct hp) b
        · exact .direct (by change parent C F _ = _; rw [parent_nonroot C F hc hEq b, hp, Option.map_some])
  | @step p c ha hp ih =>
      have hFirst := ih (by have := F.parent_left hp; omega)
      have hLast : (forest C F).Ancestor (C.parentCopy b p) (C.parentCopy b c) := by
        have hLeft := F.parent_left hp
        by_cases hGood : c < C.y
        · rw [C.parentCopy_good b hGood, C.parentCopy_good b (by omega)]
          exact prefix_ancestor C F (.direct hp) hc
        · by_cases hEq : c = C.y
          · subst c
            rw [C.parentCopy_bad b (Nat.le_refl _), C.parentCopy_good b hLeft]
            exact root_good_ancestor C F hRoot (.direct hp) b
          · exact .direct (by change parent C F _ = _; rw [parent_nonroot C F hc hEq b, hp, Option.map_some])
      exact hFirst.trans hLast

#print axioms parent_left
#print axioms ancestor_copy

end OneY.FrameCopy
