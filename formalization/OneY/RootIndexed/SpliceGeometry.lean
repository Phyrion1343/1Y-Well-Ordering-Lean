import OneY.RootIndexed.VirtualNeeds
import OneY.RootIndexed.OrdinaryAtoms

/-! # Classification of every edge in an actual one-block extension -/

namespace OneY.RootIndexed

open Numeric

theorem new_nonseam_coordinates (C : CopyCoordinates.Context) (b c : Nat)
    (hc : C.width b < c) (hNext : c < C.width (b+1)) :
    ∃ s, C.y < s ∧ s < C.x ∧ C.encode s (b+1) = c := by
  have hcut := blockCut_succ C b
  have hsize := width_succ C b
  have hxy := C.root_add_length
  unfold blockCut at hcut
  refine ⟨C.y+(c-C.width b), by omega, ?_, ?_⟩
  · unfold CopyCoordinates.Context.width at hc hNext
    rw [Nat.add_mul, Nat.one_mul] at hNext
    unfold CopyCoordinates.Context.width
    omega
  · unfold CopyCoordinates.Context.encode
    omega

theorem expanded_nonroot_source (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k b r s : Nat) (hy : y < s) (hx : s < x)
    (hr : r < (expandedMountain a hbad k).height ((badCoordinates a hbad).encode s b)) :
    ∃ u, u < (originalMountain a k).height s ∧
      CopiedFrom (badCoordinates a hbad) b (rowAtom k (originalMountain a k) u s)
        (rowAtom k (expandedMountain a hbad k) r ((badCoordinates a hbad).encode s b)) := by
  by_cases hk : k < K
  · let C := badAtLowerContext a hbad hk
    have hm : expandedMountain a hbad k = C.toRowMountain := by
      simp only [expandedMountain, hk, ↓reduceDIte, C]
    rw [hm] at hr ⊢
    exact lower_rowAtom_source C k b r s hy (Nat.le_of_lt hx) hr
  · by_cases he : k = K
    · subst k
      let C := badAtTerminalContext a hbad
      have hm : expandedMountain a hbad K = C.toRowMountain := by
        simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
        rfl
      rw [hm] at hr ⊢
      obtain ⟨hu, ht⟩ := terminal_rowAtom_source C K b r s (Nat.le_of_lt hy) hx (Or.inl hy) hr
      exact ⟨r, hu, ht⟩
    · let C : OrdinaryCopy.Context := ⟨originalMountain a k, badCoordinates a hbad⟩
      have hm : expandedMountain a hbad k = C.toRowMountain := by
        simp only [expandedMountain, hk, ↓reduceDIte, he, ↓reduceIte]
        rfl
      rw [hm] at hr ⊢
      obtain ⟨hu, ht⟩ := ordinary_rowAtom_source C k b r s (Nat.le_of_lt hy) hx hr
      exact ⟨r, hu, ht⟩

theorem expanded_root_source (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k b r : Nat) (hk : K ≤ k) (hrK : k = K → d ≤ r)
    (hr : r < (expandedMountain a hbad k).height ((badCoordinates a hbad).encode y b)) :
    r < (originalMountain a k).height y ∧
      CopiedFrom (badCoordinates a hbad) b (rowAtom k (originalMountain a k) r y)
        (rowAtom k (expandedMountain a hbad k) r ((badCoordinates a hbad).encode y b)) := by
  have hNot : ¬k < K := by omega
  by_cases he : k = K
  · subst k
    let C := badAtTerminalContext a hbad
    have hm : expandedMountain a hbad K = C.toRowMountain := by
      simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      rfl
    rw [hm] at hr ⊢
    exact terminal_rowAtom_source C K b r y (Nat.le_refl _) C.coordinates.root_lt_last
      (Or.inr (hrK rfl)) hr
  · let C : OrdinaryCopy.Context := ⟨originalMountain a k, badCoordinates a hbad⟩
    have hm : expandedMountain a hbad k = C.toRowMountain := by
      simp only [expandedMountain, hNot, ↓reduceDIte, he, ↓reduceIte]
      rfl
    rw [hm] at hr ⊢
    exact ordinary_rowAtom_source C k b r y (Nat.le_refl _) C.coordinates.root_lt_last hr

theorem actual_splice_geometry (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (bound b : Nat) :
    SpliceGeometry (copyDiagram a hbad bound b) (copyDiagram a hbad bound (b+1))
      (blockCut (badCoordinates a hbad) b) (copyFacts a hbad bound b) (copyNeeds a hbad bound b) := by
  let C := badCoordinates a hbad
  refine ⟨width_succ C b, ?_⟩
  intro e he
  obtain ⟨k, hk, c, hc, r, hr, rfl⟩ :=
    (mem_towerAtoms_iff bound (C.width (b+1)) (expandedMountain a hbad) e).mp he
  by_cases hOld : c < C.width b
  · exact Or.inl ((mem_towerAtoms_iff bound (C.width b) _ _).mpr ⟨k, hk, c, hOld, r, hr, rfl⟩)
  · by_cases hSeam : c = C.width b
    · subst c
      by_cases hNeed : k < K ∨ (k = K ∧ r < d)
      · apply Or.inr ∘ Or.inr
        refine ⟨rowTemplate k (expandedMountain a hbad k) r (C.width b), ?_, rfl, rfl, rfl, rfl⟩
        apply (mem_copyNeeds_iff a hbad bound b _).mpr
        refine ⟨k, hk, r, ?_, rfl⟩
        rcases hNeed with hLow | ⟨hSame, hRow⟩
        · simpa only [needHeight, hLow, ↓reduceIte] using hr
        · subst k
          simp only [needHeight, Nat.lt_irrefl, ↓reduceIte]
          change r < min d ((expandedMountain a hbad K).height (C.width b))
          omega
      · have hLayer : K ≤ k := by
          by_cases h : k < K
          · exact False.elim (hNeed (Or.inl h))
          · omega
        have hRow : k = K → d ≤ r := by
          intro heq
          by_cases h : r < d
          · exact False.elim (hNeed (Or.inr ⟨heq, h⟩))
          · omega
        have hcoord : C.encode y (b+1) = C.width b := blockCut_succ C b
        rw [← hcoord] at hr ⊢
        obtain ⟨hu, ht⟩ := expanded_root_source a hbad k (b+1) r hLayer hRow hr
        have hSource : rowAtom k (originalMountain a k) r y ∈ towerAtoms bound x (originalMountain a) :=
          (mem_towerAtoms_iff bound x _ _).mpr
            ⟨k, hk, y, C.root_lt_last, r, hu, rfl⟩
        exact Or.inr (Or.inl (copiedFrom_copyCase C b _ hSource ht))
    · have hAfter : C.width b < c := by omega
      obtain ⟨s, hy, hx, hcoord⟩ := new_nonseam_coordinates C b c hAfter hc
      rw [← hcoord] at hr ⊢
      obtain ⟨u, hu, ht⟩ := expanded_nonroot_source a hbad k (b+1) r s hy hx hr
      have hSource : rowAtom k (originalMountain a k) u s ∈ towerAtoms bound x (originalMountain a) :=
        (mem_towerAtoms_iff bound x _ _).mpr ⟨k, hk, s, hx, u, hu, rfl⟩
      exact Or.inr (Or.inl (copiedFrom_copyCase C b _ hSource ht))

end OneY.RootIndexed

#print axioms OneY.RootIndexed.actual_splice_geometry
