import OneY.OrdinaryCopyReconstruction
import OneY.NumericRoots
import ZeroY.Forest.Blocker

/-! # Nearest-smaller parent selection commutes with ordinary copying -/

namespace OneY.OrdinaryCopy.Context

theorem parentCopy_le_iff (C : Context) (b p q : Nat) :
    C.coordinates.parentCopy b p ≤ C.coordinates.parentCopy b q ↔ p ≤ q := by
  unfold CopyCoordinates.Context.parentCopy
  split <;> split <;> omega

theorem ancestor_parentCopy_iff (C : Context) {r a c : Nat}
    (hc : c < C.coordinates.x) (b : Nat) :
    (C.row r).Ancestor a (C.coordinates.parentCopy b c) ↔
      ∃ q, (C.mountain.row r).Ancestor q c ∧ a = C.coordinates.parentCopy b q := by
  constructor
  · intro ha
    induction c using Nat.strongRecOn generalizing a with
    | ind c ih =>
        cases hp : (C.mountain.row r).parent c with
        | none =>
            have hn : (C.row r).parent (C.coordinates.parentCopy b c) = none := by
              change C.parent r _ = _
              rw [C.parent_parentCopy hc b r, hp, Option.map_none]
            cases ha with
            | direct h => rw [hn] at h; contradiction
            | step _ h => rw [hn] at h; contradiction
        | some p =>
            have hleft := (C.mountain.row r).parent_left hp
            have hn : (C.row r).parent (C.coordinates.parentCopy b c) =
                some (C.coordinates.parentCopy b p) := by
              change C.parent r _ = _
              rw [C.parent_parentCopy hc b r, hp, Option.map_some]
            rcases ZeroY.Forest.ancestor_eq_or_below_parent hn
              (ParentForest.ancestor_to_zeroY ha) with heq | hpath
            · exact ⟨p, ParentForest.Ancestor.direct hp, heq⟩
            · obtain ⟨q, hq, heq⟩ := ih p hleft (by omega)
                (ParentForest.ancestor_of_zeroY hpath)
              exact ⟨q, ParentForest.Ancestor.step hq hp, heq⟩
  · rintro ⟨q, hq, rfl⟩
    exact C.ancestor_copy hq hc b

theorem restrictedParent_parentCopy (C : Context) (v : Nat → Nat)
    {c : Nat} (hc : c < C.coordinates.x) (b r : Nat) :
    Numeric.restrictedParent (C.row r) (C.copyValue v) (C.coordinates.parentCopy b c) =
      (Numeric.restrictedParent (C.mountain.row r) v c).map (C.coordinates.parentCopy b) := by
  cases hp : Numeric.restrictedParent (C.mountain.row r) v c with
  | none =>
      simp only [Option.map_none]
      apply (Numeric.restrictedParent_none_iff (C.row r) (C.copyValue v) _).mpr
      intro a ha hpos
      obtain ⟨q, hq, heq⟩ := (C.ancestor_parentCopy_iff hc b).mp ha
      have hleft := hq.lt
      have hqbound : q < C.coordinates.x := by omega
      rw [heq, C.copyValue_parentCopy v hqbound b] at hpos
      rw [heq, C.copyValue_parentCopy v hc b, C.copyValue_parentCopy v hqbound b]
      exact (Numeric.restrictedParent_none_iff (C.mountain.row r) v c).mp hp q hq hpos
  | some p =>
      simp only [Option.map_some]
      obtain ⟨hap, hpPos, hpVal, hpMax⟩ :=
        (Numeric.restrictedParent_some_iff (C.mountain.row r) v c p).mp hp
      have hpa := ParentForest.ancestor_of_zeroY hap
      have hleft := hpa.lt
      have hpbound : p < C.coordinates.x := by omega
      apply (Numeric.restrictedParent_some_iff (C.row r) (C.copyValue v)
        (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b p)).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (C.ancestor_copy hpa hc b), ?_, ?_, ?_⟩
      · rw [C.copyValue_parentCopy v hpbound b]
        exact hpPos
      · rw [C.copyValue_parentCopy v hpbound b, C.copyValue_parentCopy v hc b]
        exact hpVal
      · intro a ha haPos haVal
        obtain ⟨q, hq, heq⟩ := (C.ancestor_parentCopy_iff hc b).mp
          (ParentForest.ancestor_of_zeroY ha)
        have hqlt := hq.lt
        have hqbound : q < C.coordinates.x := by omega
        rw [heq, C.copyValue_parentCopy v hqbound b] at haPos
        rw [heq, C.copyValue_parentCopy v hqbound b, C.copyValue_parentCopy v hc b] at haVal
        rw [heq, C.parentCopy_le_iff]
        exact hpMax q (ParentForest.ancestor_to_zeroY hq) haPos haVal

theorem restrictedParent_formula (C : Context) (v : Nat → Nat) (r c : Nat) :
    Numeric.restrictedParent (C.row r) (C.copyValue v) c =
      (Numeric.restrictedParent (C.mountain.row r) v (C.source0 c)).map
        (C.coordinates.parentCopy (C.block0 c)) := by
  have h := C.restrictedParent_parentCopy v (C.source0_bounds c) (C.block0 c) r
  rw [C.parentCopy_coordinates c] at h
  exact h

end OneY.OrdinaryCopy.Context

namespace OneY.Numeric

theorem ordinaryCopy_restrictedParent_reconstruction (base : Row)
    (hpos : ∀ c, 0 < base.value c) (coordinates : CopyCoordinates.Context) (r c : Nat) :
    restrictedParent ((ordinaryCopyContext base hpos coordinates).row r)
      (Reconstruction.value (ordinaryCopyContext base hpos coordinates).toRowMountain
        ((ordinaryCopyContext base hpos coordinates).copyValue (topValue base)) (r+1)) c =
      (ordinaryCopyContext base hpos coordinates).parent (r+1) c := by
  let C := ordinaryCopyContext base hpos coordinates
  have hv : Reconstruction.value C.toRowMountain (C.copyValue (topValue base)) (r+1) =
      C.copyValue (rows base (r+1)).value := by
    funext q
    exact ordinaryCopy_value base hpos coordinates (r+1) q
  rw [hv, C.restrictedParent_formula]
  rfl

end OneY.Numeric

#print axioms OneY.OrdinaryCopy.Context.ancestor_parentCopy_iff
#print axioms OneY.OrdinaryCopy.Context.restrictedParent_formula
#print axioms OneY.Numeric.ordinaryCopy_restrictedParent_reconstruction
