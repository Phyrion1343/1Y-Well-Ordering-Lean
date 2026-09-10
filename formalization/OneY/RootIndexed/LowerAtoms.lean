import OneY.RootIndexed.CopyDiagram
import OneY.LowerCopyRoots

/-! # Every actual lower copied edge has a source edge with a weakly moved root -/

namespace OneY.RootIndexed

open RootGeometry

def CopiedFrom (C : CopyCoordinates.Context) (b : Nat) (old new : Atom) : Prop :=
  new.layer = old.layer ∧ new.parent = C.parentCopy b old.parent ∧
    new.child = C.parentCopy b old.child ∧
    (new.root = C.parentCopy b old.root ∨
      (new.root < blockCut C b ∧ C.y ≤ old.root))

theorem copiedFrom_rowAtoms (C : CopyCoordinates.Context) (M N : RowMountain)
    (k b r u c p : Nat) (hc : C.y ≤ c)
    (hp : (M.row u).parent c = some p)
    (hp' : (N.row r).parent (C.encode c b) = some (C.parentCopy b p))
    (hroot : N.rootAt r (C.encode c b) = C.parentCopy b (M.rootAt u c) ∨
      (N.rootAt r (C.encode c b) < blockCut C b ∧ C.y ≤ M.rootAt u c)) :
    CopiedFrom C b (rowAtom k M u c) (rowAtom k N r (C.encode c b)) := by
  refine ⟨rfl, ?_, ?_, hroot⟩
  · simp only [rowAtom, hp, hp', Option.getD_some]
  · change C.encode c b = C.parentCopy b c
    rw [C.parentCopy_bad b hc]
    rfl

theorem lower_rowAtom_source (C : LowerCopy.Context) (k b r c : Nat)
    (hc : C.coordinates.y < c) (hx : c ≤ C.coordinates.x)
    (hr : r < C.toRowMountain.height (C.coordinates.encode c b)) :
    ∃ u, u < C.mountain.height c ∧
      CopiedFrom C.coordinates b (rowAtom k C.mountain u c)
        (rowAtom k C.toRowMountain r (C.coordinates.encode c b)) := by
  have hheight := C.height_encode hc hx b
  change r < C.height (C.coordinates.encode c b) at hr
  rw [hheight] at hr
  by_cases hCone : C.InCone c
  · rw [if_pos hCone] at hr
    by_cases hLow : r < C.floor
    · have hu : r < C.mountain.height c := by have := hCone.1; omega
      obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hu
      refine ⟨r, hu, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
        k b r r c p (Nat.le_of_lt hc) hp ?_ (Or.inl (C.rootAt_low hc hx hLow b))⟩
      change C.parent r (C.coordinates.encode c b) = some _
      rw [C.parent_encode_low hc hx hLow b, hp, Option.map_some]
    · have hfloor : C.floor ≤ r := by omega
      by_cases hFill : r < C.floor+b*C.rise
      · have hu : C.floor < C.mountain.height c := C.height_lt_of_inCone hCone hc
        obtain ⟨p, hp⟩ := C.mountain.parent_exists C.floor c hu
        have hpgood := C.root_le_of_inCone (C.high_parent_inCone hCone (Nat.le_refl _) hp)
        refine ⟨C.floor, hu, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
          k b r C.floor c p (Nat.le_of_lt hc) hp ?_ (Or.inr ?_)⟩
        · change C.parent r (C.coordinates.encode c b) = some _
          rw [C.parent_encode_reference hc hx hCone b hfloor (Nat.le_of_lt hFill),
            hp, Option.map_some, C.coordinates.parentCopy_bad b hpgood]
        · exact ⟨C.rootAt_fill_lt_rootCopy hc hx hCone b hFill,
            by rw [hCone.2]; exact Nat.le_refl _⟩
      · have hHigh : C.floor+b*C.rise ≤ r := by omega
        have hu : r-b*C.rise < C.mountain.height c := by omega
        have huFloor : C.floor ≤ r-b*C.rise := by omega
        have hrow : r-b*C.rise+b*C.rise = r := by omega
        obtain ⟨p, hp⟩ := C.mountain.parent_exists (r-b*C.rise) c hu
        have hpbad := C.root_le_of_inCone (C.high_parent_inCone hCone huFloor hp)
        refine ⟨r-b*C.rise, hu, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
          k b r (r-b*C.rise) c p (Nat.le_of_lt hc) hp ?_
            (Or.inl (C.rootAt_high hc hx hCone b hHigh))⟩
        change C.parent r (C.coordinates.encode c b) = some _
        have ht := C.parent_encode_lifted hc hx hCone huFloor b
        rw [hrow, hp, Option.map_some, ← C.coordinates.parentCopy_bad b hpbad] at ht
        exact ht
  · rw [if_neg hCone] at hr
    obtain ⟨p, hp⟩ := C.mountain.parent_exists r c hr
    refine ⟨r, hr, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
      k b r r c p (Nat.le_of_lt hc) hp ?_ (Or.inl (C.rootAt_outside hc hx hCone b))⟩
    change C.parent r (C.coordinates.encode c b) = some _
    rw [C.parent_encode hc hx b r, if_neg (by intro h; exact hCone h.1),
      hp, Option.map_some]

theorem copiedFrom_copyCase (C : CopyCoordinates.Context) (b : Nat)
    (facts : List Atom) {old new : Atom} (hold : old ∈ facts)
    (h : CopiedFrom C (b+1) old new) :
    CopyCase (C.width b) (blockCut C b) (facts.map (copyAtom C b)) new := by
  refine ⟨copyAtom C b old, List.mem_map.mpr ⟨old, hold, rfl⟩, h.1, ?_, ?_, ?_⟩
  · exact h.2.1.trans (moveColumn_parentCopy C b old.parent).symm
  · exact h.2.2.1.trans (moveColumn_parentCopy C b old.child).symm
  · rcases h.2.2.2 with hroot | ⟨hlt, hbad⟩
    · exact Or.inl (hroot.trans (moveColumn_parentCopy C b old.root).symm)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [blockCut_succ] at hlt
        exact hlt
      · change blockCut C b ≤ C.parentCopy b old.root
        rw [C.parentCopy_bad b hbad]
        unfold blockCut
        omega

end OneY.RootIndexed

#print axioms OneY.RootIndexed.lower_rowAtom_source
#print axioms OneY.RootIndexed.copiedFrom_copyCase
