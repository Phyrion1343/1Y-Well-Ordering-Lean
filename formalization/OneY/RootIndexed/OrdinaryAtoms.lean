import OneY.RootIndexed.LowerAtoms
import OneY.OrdinaryCopyRoots
import OneY.TerminalCopyRoots

/-! # Source edges for ordinary copies and active copies outside low seams -/

namespace OneY.RootIndexed

theorem ordinary_rowAtom_source (C : OrdinaryCopy.Context) (k b r c : Nat)
    (hy : C.coordinates.y ≤ c) (hx : c < C.coordinates.x)
    (hr : r < C.toRowMountain.height (C.coordinates.encode c b)) :
    r < C.mountain.height c ∧
      CopiedFrom C.coordinates b (rowAtom k C.mountain r c)
        (rowAtom k C.toRowMountain r (C.coordinates.encode c b)) := by
  have hcoord : C.coordinates.encode c b = C.coordinates.parentCopy b c :=
    (C.coordinates.parentCopy_bad b hy).symm
  rw [hcoord] at hr
  change r < C.height (C.coordinates.parentCopy b c) at hr
  rw [C.height_parentCopy hx b] at hr
  obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hr
  refine ⟨hr, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
    k b r r c p hy hp ?_ (Or.inl ?_)⟩
  · rw [hcoord]
    change C.parent r (C.coordinates.parentCopy b c) = some _
    rw [C.parent_parentCopy hx b r, hp, Option.map_some]
  · rw [hcoord]
    exact C.rootAt_parentCopy hx b r

theorem terminal_rowAtom_source (C : TerminalCopy.Context) (k b r c : Nat)
    (hy : C.coordinates.y ≤ c) (hx : c < C.coordinates.x)
    (hAllowed : C.coordinates.y < c ∨ C.level ≤ r)
    (hr : r < C.toRowMountain.height (C.coordinates.encode c b)) :
    r < C.mountain.height c ∧
      CopiedFrom C.coordinates b (rowAtom k C.mountain r c)
        (rowAtom k C.toRowMountain r (C.coordinates.encode c b)) := by
  have hcoord : C.coordinates.encode c b = C.coordinates.parentCopy b c :=
    (C.coordinates.parentCopy_bad b hy).symm
  rw [hcoord] at hr
  change r < C.height (C.coordinates.parentCopy b c) at hr
  rw [C.height_parentCopy hx b] at hr
  obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hr
  refine ⟨hr, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
    k b r r c p hy hp ?_ (Or.inl ?_)⟩
  · change C.parent r (C.coordinates.encode c b) = some _
    by_cases hRoot : c = C.coordinates.y
    · subst c
      have hrLevel : C.level ≤ r := by rcases hAllowed with h | h <;> omega
      have hpgood := (C.mountain.row r).parent_left hp
      change C.parent r (C.coordinates.y+b*C.coordinates.length) = some _
      rw [C.parent_root_copy_high hrLevel b, hp, C.coordinates.parentCopy_good b hpgood]
    · have hafter : C.coordinates.y < c := by omega
      rw [C.parent_encode hafter (Nat.le_of_lt hx) b r,
        if_neg (by intro h; omega), hp, Option.map_some]
  · rw [hcoord]
    exact C.rootAt_parentCopy hx b r

end OneY.RootIndexed

#print axioms OneY.RootIndexed.ordinary_rowAtom_source
#print axioms OneY.RootIndexed.terminal_rowAtom_source
