import OneY.OrdinaryCopySelection

/-! # Ordinary-copy selection for any explicitly transported candidate forest -/

namespace OneY.OrdinaryCopy.Context

def CopiesForest (C : Context) (old copied : ParentForest) : Prop :=
  ∀ c, copied.parent c = (old.parent (C.source0 c)).map
    (C.coordinates.parentCopy (C.block0 c))

theorem forest_parent_parentCopy (C : Context) {old copied : ParentForest}
    (hcopy : C.CopiesForest old copied) {c : Nat} (hc : c < C.coordinates.x) (b : Nat) :
    copied.parent (C.coordinates.parentCopy b c) =
      (old.parent c).map (C.coordinates.parentCopy b) := by
  rw [hcopy, C.source0_parentCopy hc b]
  by_cases hgood : c < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hgood, C.block0_good hgood]
    cases hp : old.parent c with
    | none => rfl
    | some p =>
        have hleft := old.parent_left hp
        simp only [Option.map_some, C.coordinates.parentCopy_zero,
          C.coordinates.parentCopy_good b (by omega : p < C.coordinates.y)]
  · rw [C.coordinates.parentCopy_bad b (by omega)]
    change (old.parent c).map (C.coordinates.parentCopy (C.block0 (C.coordinates.encode c b))) = _
    rw [C.block0_encode (by omega) hc b]

theorem forest_ancestor_copy (C : Context) {old copied : ParentForest}
    (hcopy : C.CopiesForest old copied) {a c : Nat}
    (ha : old.Ancestor a c) (hc : c < C.coordinates.x) (b : Nat) :
    copied.Ancestor (C.coordinates.parentCopy b a) (C.coordinates.parentCopy b c) := by
  induction ha with
  | direct hp =>
      exact ParentForest.Ancestor.direct
        (by rw [C.forest_parent_parentCopy hcopy hc b, hp, Option.map_some])
  | @step p c ha hp ih =>
      have hleft := old.parent_left hp
      exact ParentForest.Ancestor.step (ih (by omega))
        (by rw [C.forest_parent_parentCopy hcopy hc b, hp, Option.map_some])

theorem forest_ancestor_parentCopy_iff (C : Context) {old copied : ParentForest}
    (hcopy : C.CopiesForest old copied) {a c : Nat} (hc : c < C.coordinates.x) (b : Nat) :
    copied.Ancestor a (C.coordinates.parentCopy b c) ↔
      ∃ q, old.Ancestor q c ∧ a = C.coordinates.parentCopy b q := by
  constructor
  · intro ha
    induction c using Nat.strongRecOn generalizing a with
    | ind c ih =>
        cases hp : old.parent c with
        | none =>
            have hn : copied.parent (C.coordinates.parentCopy b c) = none := by
              rw [C.forest_parent_parentCopy hcopy hc b, hp, Option.map_none]
            cases ha with
            | direct h => rw [hn] at h; contradiction
            | step _ h => rw [hn] at h; contradiction
        | some p =>
            have hleft := old.parent_left hp
            have hn : copied.parent (C.coordinates.parentCopy b c) =
                some (C.coordinates.parentCopy b p) := by
              rw [C.forest_parent_parentCopy hcopy hc b, hp, Option.map_some]
            rcases ZeroY.Forest.ancestor_eq_or_below_parent hn
              (ParentForest.ancestor_to_zeroY ha) with heq | hpath
            · exact ⟨p, ParentForest.Ancestor.direct hp, heq⟩
            · obtain ⟨q, hq, heq⟩ := ih p hleft (by omega)
                (ParentForest.ancestor_of_zeroY hpath)
              exact ⟨q, ParentForest.Ancestor.step hq hp, heq⟩
  · rintro ⟨q, hq, rfl⟩
    exact C.forest_ancestor_copy hcopy hq hc b

theorem restrictedParent_parentCopy_of_forest_copy (C : Context)
    {old copied : ParentForest} (hcopy : C.CopiesForest old copied) (v : Nat → Nat)
    {c : Nat} (hc : c < C.coordinates.x) (b : Nat) :
    Numeric.restrictedParent copied (C.copyValue v) (C.coordinates.parentCopy b c) =
      (Numeric.restrictedParent old v c).map (C.coordinates.parentCopy b) := by
  cases hp : Numeric.restrictedParent old v c with
  | none =>
      simp only [Option.map_none]
      apply (Numeric.restrictedParent_none_iff copied (C.copyValue v) _).mpr
      intro a ha hpos
      obtain ⟨q, hq, heq⟩ := (C.forest_ancestor_parentCopy_iff hcopy hc b).mp ha
      have hleft := hq.lt
      have hqbound : q < C.coordinates.x := by omega
      rw [heq, C.copyValue_parentCopy v hqbound b] at hpos
      rw [heq, C.copyValue_parentCopy v hc b, C.copyValue_parentCopy v hqbound b]
      exact (Numeric.restrictedParent_none_iff old v c).mp hp q hq hpos
  | some p =>
      simp only [Option.map_some]
      obtain ⟨hap, hpPos, hpVal, hpMax⟩ :=
        (Numeric.restrictedParent_some_iff old v c p).mp hp
      have hpa := ParentForest.ancestor_of_zeroY hap
      have hleft := hpa.lt
      have hpbound : p < C.coordinates.x := by omega
      apply (Numeric.restrictedParent_some_iff copied (C.copyValue v)
        (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b p)).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (C.forest_ancestor_copy hcopy hpa hc b), ?_, ?_, ?_⟩
      · rw [C.copyValue_parentCopy v hpbound b]
        exact hpPos
      · rw [C.copyValue_parentCopy v hpbound b, C.copyValue_parentCopy v hc b]
        exact hpVal
      · intro a ha haPos haVal
        obtain ⟨q, hq, heq⟩ := (C.forest_ancestor_parentCopy_iff hcopy hc b).mp
          (ParentForest.ancestor_of_zeroY ha)
        have hqlt := hq.lt
        have hqbound : q < C.coordinates.x := by omega
        rw [heq, C.copyValue_parentCopy v hqbound b] at haPos
        rw [heq, C.copyValue_parentCopy v hqbound b, C.copyValue_parentCopy v hc b] at haVal
        rw [heq, C.parentCopy_le_iff]
        exact hpMax q (ParentForest.ancestor_to_zeroY hq) haPos haVal

theorem restrictedParent_of_forest_copy (C : Context) {old copied : ParentForest}
    (hcopy : C.CopiesForest old copied) (v : Nat → Nat) (c : Nat) :
    Numeric.restrictedParent copied (C.copyValue v) c =
      (Numeric.restrictedParent old v (C.source0 c)).map
        (C.coordinates.parentCopy (C.block0 c)) := by
  have h := C.restrictedParent_parentCopy_of_forest_copy hcopy v (C.source0_bounds c) (C.block0 c)
  rw [C.parentCopy_coordinates c] at h
  exact h

end OneY.OrdinaryCopy.Context

#print axioms OneY.OrdinaryCopy.Context.forest_ancestor_parentCopy_iff
#print axioms OneY.OrdinaryCopy.Context.restrictedParent_of_forest_copy
