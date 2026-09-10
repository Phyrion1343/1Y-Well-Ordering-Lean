import OneY.LowerCopyPseudo
import OneY.LowerCopyTopForest
import OneY.ReconstructionTop
import OneY.ExtractionGeometry

/-! # The lower pseudo-top bound from the restored upper layer

The two selection equations are obtained by running the upper recovery
theorem with its two valid old candidate frames, Q and the strict-height
top forest. No lower canonical equation or numerical domination is assumed.
-/

namespace OneY.LowerCopy.Context

theorem contractedSelectionGood_of_upper_transport (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (newTop : Nat → Nat)
    (hTransport : ∀ s, C.coordinates.y < s → s < C.coordinates.x → ∀ b,
      Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop
        (C.coordinates.parentCopy b s) =
      (Numeric.restrictedParent (Pseudo.forest C.mountain) (Numeric.topValue base) s).map
        (C.coordinates.parentCopy b)) : C.ContractedSelectionGood newTop := by
  intro s hs hx hHeight hQ b p hp
  have hxStrict : s < C.coordinates.x := by
    by_cases he : s = C.coordinates.x
    · subst s
      have := C.last_higher
      change C.floor < C.mountain.height C.coordinates.x at this
      omega
    · omega
  have hTop : Numeric.topValue base s ≤ Numeric.topValue base C.coordinates.y := by
    have hPath : (Pseudo.forest (Numeric.mountain base hBase)).Ancestor C.coordinates.y s := by
      rw [hMountain] at hQ
      exact ParentForest.Ancestor.direct hQ
    apply Numeric.topValue_le_of_same_height_pseudo_ancestor base hBase hPath
    have hHeq : C.mountain.height C.coordinates.y = C.mountain.height s := hHeight.symm
    rw [hMountain] at hHeq
    exact hHeq
  have hOldGood : ∀ q, Numeric.restrictedParent (Pseudo.forest C.mountain) (Numeric.topValue base) s = some q →
      q < C.coordinates.y := by
    intro q hq
    have hspec := Numeric.restrictedParent_spec (Pseudo.forest C.mountain) (Numeric.topValue base) hq
    rcases ZeroY.Forest.ancestor_eq_or_below_parent hQ hspec.1 with he | ha
    · subst q
      have := hspec.2.2
      omega
    · exact ZeroY.Forest.ancestor_lt (Pseudo.forest C.mountain).parent_left ha
  rw [hTransport s hs hxStrict b] at hp
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp hp
  have hGood := hOldGood q hq
  rw [C.coordinates.parentCopy_good b hGood] at he
  omega

theorem extractedHeightDecrease_of_upper_selections (C : Context) (hRegular : C.DepthRegular)
    (hRoot : (Pseudo.forest C.mountain).Ancestor C.coordinates.y C.coordinates.x)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hGood : C.ContractedSelectionGood newTop)
    (hSame : ∀ c,
      Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop c =
      Numeric.restrictedParent (FrameCopy.forest C.coordinates C.mountain.topForest) newTop c) :
    Reconstruction.ExtractedHeightDecrease C.toRowMountain newTop := by
  intro c p hp
  rw [C.pseudo_select_eq_frameCopy hRegular hRoot newTop hPositive hGood c, hSame c,
    ← C.topForest_eq_frameCopy] at hp
  have ha : C.toRowMountain.topForest.Ancestor p c :=
    Numeric.select_refines C.toRowMountain.topForest newTop hp
  have hd := ha.depth_lt
  rw [C.toRowMountain.topForest_depth, C.toRowMountain.topForest_depth] at hd
  exact hd

theorem pseudoTopBound_of_upper_selections (C : Context) (base : Numeric.Row)
    (hBase : ∀ c, 0 < base.value c) (hMountain : C.mountain = Numeric.mountain base hBase)
    (hRoot : (Pseudo.forest C.mountain).Ancestor C.coordinates.y C.coordinates.x)
    (newTop : Nat → Nat) (hPositive : ∀ c, 0 < newTop c)
    (hTransport : ∀ s, C.coordinates.y < s → s < C.coordinates.x → ∀ b,
      Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop
        (C.coordinates.parentCopy b s) =
      (Numeric.restrictedParent (Pseudo.forest C.mountain) (Numeric.topValue base) s).map
        (C.coordinates.parentCopy b))
    (hSame : ∀ c,
      Numeric.restrictedParent (FrameCopy.forest C.coordinates (Pseudo.forest C.mountain)) newTop c =
      Numeric.restrictedParent (FrameCopy.forest C.coordinates C.mountain.topForest) newTop c) :
    Reconstruction.PseudoTopBound C.toRowMountain newTop :=
  Reconstruction.pseudoTopBound_of_extractedHeightDecrease C.toRowMountain newTop hPositive
    (C.extractedHeightDecrease_of_upper_selections (C.depthRegular_numeric base hBase hMountain) hRoot newTop hPositive
      (C.contractedSelectionGood_of_upper_transport base hBase hMountain newTop hTransport) hSame)

#print axioms contractedSelectionGood_of_upper_transport
#print axioms extractedHeightDecrease_of_upper_selections
#print axioms pseudoTopBound_of_upper_selections

end OneY.LowerCopy.Context
