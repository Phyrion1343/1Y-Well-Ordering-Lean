import OneY.RootIndexed.LowerAtoms

/-! # Actual seam demands come from old-last-column templates -/

namespace OneY.RootIndexed

open RootGeometry Numeric

def atomTemplate (e : Atom) : TopAtom := ⟨e.layer, e.root, e.parent⟩

theorem copiedFrom_virtualCase (C : CopyCoordinates.Context) (b : Nat)
    (templates : List TopAtom) {old new : Atom}
    (hold : atomTemplate old ∈ templates) (h : CopiedFrom C b old new) :
    VirtualCase (blockCut C b) (templates.map (copyTopAtom C b)) (atomTemplate new) := by
  refine ⟨copyTopAtom C b (atomTemplate old), List.mem_map.mpr ⟨_, hold, rfl⟩,
    h.1, h.2.1, ?_⟩
  rcases h.2.2.2 with he | ⟨hlt, hbad⟩
  · exact Or.inl he
  · refine Or.inr ⟨hlt, ?_⟩
    change blockCut C b ≤ C.parentCopy b old.root
    rw [C.parentCopy_bad b hbad]
    unfold blockCut
    omega

theorem terminal_low_rowAtom_source (C : TerminalCopy.Context) (k b r : Nat)
    (hr : r < C.level) :
    r < C.mountain.height C.coordinates.x ∧
      CopiedFrom C.coordinates b (rowAtom k C.mountain r C.coordinates.x)
        (rowAtom k C.toRowMountain r (C.coordinates.encode C.coordinates.x b)) := by
  have hlive := C.mountain.parent_source C.last_parent
  have hrow : r < C.mountain.height C.coordinates.x := by omega
  obtain ⟨p, hp⟩ := C.mountain.parent_exists r C.coordinates.x hrow
  refine ⟨hrow, copiedFrom_rowAtoms C.coordinates C.mountain C.toRowMountain
    k b r r C.coordinates.x p (Nat.le_of_lt C.coordinates.root_lt_last) hp ?_ (Or.inl ?_)⟩
  · change C.parent r (C.coordinates.encode C.coordinates.x b) = some _
    rw [C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hr b,
      hp, Option.map_some]
  · have h := C.rootAt_low_parentCopy hr (Nat.le_refl _) b
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt C.coordinates.root_lt_last)] at h
    exact h

theorem copyNeeds_virtual (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) {e : TopAtom} (he : e ∈ copyNeeds a hbad bound b) :
    VirtualCase (blockCut (badCoordinates a hbad) b) (copyTemplates a hbad bound b) e := by
  obtain ⟨k, hkBound, r, hr, rfl⟩ := (mem_copyNeeds_iff a hbad bound b e).mp he
  have hLive := Nat.lt_of_lt_of_le hr (needHeight_le a hbad k b)
  by_cases hk : k < K
  · let C := badAtLowerContext a hbad hk
    have hM : expandedMountain a hbad k = C.toRowMountain := by
      simp only [expandedMountain, hk, ↓reduceDIte, C]
    rw [hM] at hLive ⊢
    obtain ⟨u, hu, hSource⟩ := lower_rowAtom_source C k b r x
      C.coordinates.root_lt_last (Nat.le_refl _) hLive
    have hOld : rowTemplate k (originalMountain a k) u x ∈ originalTemplates a bound x :=
      (mem_originalTemplates_iff a bound x _).mpr ⟨k, hkBound, u, hu, rfl⟩
    exact copiedFrom_virtualCase C.coordinates b (originalTemplates a bound x)
      (old := rowAtom k C.mountain u x)
      (new := rowAtom k C.toRowMountain r (C.coordinates.encode x b)) hOld hSource
  · have hkEq : k = K := by
      by_cases hh : k = K
      · exact hh
      · have hn : needHeight a hbad k b = 0 := by simp [needHeight, hk, hh]
        rw [hn] at hr
        omega
    subst k
    have hrd : r < d := by
      simp only [needHeight, Nat.lt_irrefl, ↓reduceIte] at hr
      omega
    let C := badAtTerminalContext a hbad
    have hM : expandedMountain a hbad K = C.toRowMountain := by
      simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      rfl
    rw [hM]
    obtain ⟨hu, hSource⟩ := terminal_low_rowAtom_source C K b r hrd
    have hOld : rowTemplate K (originalMountain a K) r x ∈ originalTemplates a bound x :=
      (mem_originalTemplates_iff a bound x _).mpr ⟨K, hkBound, r, hu, rfl⟩
    exact copiedFrom_virtualCase C.coordinates b (originalTemplates a bound x)
      (old := rowAtom K C.mountain r x)
      (new := rowAtom K C.toRowMountain r (C.coordinates.encode x b)) hOld hSource

end OneY.RootIndexed

#print axioms OneY.RootIndexed.copyNeeds_virtual
