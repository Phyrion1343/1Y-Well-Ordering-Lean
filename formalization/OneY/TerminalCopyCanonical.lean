import OneY.TerminalCopyReconstruction
import OneY.OrdinaryCopyExtraction

/-!
# Established canonical regions of the active finite copy

This module checks nearest-smaller reconstruction above the active row
and inside the unchanged prefix. It does not assert the yet-unproved
nearest-smaller statement below the active row in later copied blocks.
-/

namespace OneY.Numeric

theorem restrictedParent_prefix_congr (F G : ParentForest) (v w : Nat → Nat)
    {n c : Nat} (hc : c < n)
    (hparent : ∀ q, q < n → F.parent q = G.parent q)
    (hvalue : ∀ q, q < n → v q = w q) :
    restrictedParent F v c = restrictedParent G w c := by
  have transferFG : ∀ q, F.Ancestor q c → G.Ancestor q c := by
    intro q hq
    exact ParentForest.ancestor_of_zeroY (ZeroY.Forest.ancestor_transfer_prefix
      F.parent_left hc hparent (ParentForest.ancestor_to_zeroY hq))
  have transferGF : ∀ q, G.Ancestor q c → F.Ancestor q c := by
    intro q hq
    exact ParentForest.ancestor_of_zeroY (ZeroY.Forest.ancestor_transfer_prefix
      G.parent_left hc (fun q h => (hparent q h).symm) (ParentForest.ancestor_to_zeroY hq))
  cases hp : restrictedParent F v c with
  | none =>
      symm
      apply (restrictedParent_none_iff G w c).mpr
      intro q hq hpos
      have hqlt := hq.lt
      have hqbound : q < n := by omega
      rw [← hvalue q hqbound] at hpos
      rw [← hvalue c hc, ← hvalue q hqbound]
      exact (restrictedParent_none_iff F v c).mp hp q (transferGF q hq) hpos
  | some p =>
      symm
      obtain ⟨ha, hpos, hval, hmax⟩ := (restrictedParent_some_iff F v c p).mp hp
      have hpa := ParentForest.ancestor_of_zeroY ha
      have hplt := hpa.lt
      have hpbound : p < n := by omega
      apply (restrictedParent_some_iff G w c p).mpr
      refine ⟨ParentForest.ancestor_to_zeroY (transferFG p hpa), ?_, ?_, ?_⟩
      · rw [← hvalue p hpbound]
        exact hpos
      · rw [← hvalue p hpbound, ← hvalue c hc]
        exact hval
      · intro q hq hqpos hqval
        have hqa := ParentForest.ancestor_of_zeroY hq
        have hqlt := hqa.lt
        have hqbound : q < n := by omega
        rw [← hvalue q hqbound] at hqpos
        rw [← hvalue q hqbound, ← hvalue c hc] at hqval
        exact hmax q (ParentForest.ancestor_to_zeroY (transferGF q hqa)) hqpos hqval

theorem badAtTerminal_restrictedParent_above (a : RootedRow) {K d x y r : Nat}
    (hbad : BadAt a K d x y) (hr : d ≤ r) (c : Nat) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) c = (badAtTerminalContext a hbad).parent (r+1) c := by
  let C := badAtTerminalContext a hbad
  have hr' : C.level ≤ r := hr
  have hnext : C.level ≤ r+1 := by omega
  have hf : C.row r = C.ordinaryContext.row r := by
    apply ParentForest.ext_parent
    funext q
    exact C.parent_eq_ordinary_above hr' q
  have hv : Reconstruction.value C.toRowMountain
      (C.ordinaryContext.copyValue (topValue (layers a K).row)) (r+1) =
        Reconstruction.value C.ordinaryContext.toRowMountain
          (C.ordinaryContext.copyValue (topValue (layers a K).row)) (r+1) := by
    funext q
    exact C.value_eq_ordinary_above _ hnext q
  change restrictedParent (C.row r) _ c = C.parent (r+1) c
  rw [hf, hv, C.parent_eq_ordinary_above hnext c]
  exact ordinaryCopy_restrictedParent_reconstruction (layers a K).row
    (layers a K).positive C.coordinates r c

theorem badAtTerminal_restrictedParent_prefix (a : RootedRow) {K d x y c : Nat}
    (hbad : BadAt a K d x y) (hc : c < x) (r : Nat) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) c = (badAtTerminalContext a hbad).parent (r+1) c := by
  let C := badAtTerminalContext a hbad
  have h := restrictedParent_prefix_congr (C.row r) (C.mountain.row r)
    (Reconstruction.value C.toRowMountain (C.ordinaryContext.copyValue (topValue (layers a K).row)) (r+1))
    (Reconstruction.value C.mountain (topValue (layers a K).row) (r+1)) hc
    (fun q hq => C.parent_original hq r)
    (fun q hq => C.value_original _ hq (r+1))
  change restrictedParent (C.row r) _ c = C.parent (r+1) c
  rw [h, C.parent_original hc (r+1)]
  exact Reconstruction.restrictedParent_numeric_reconstruction
    (layers a K).row (layers a K).positive r c

end OneY.Numeric

#print axioms OneY.Numeric.restrictedParent_prefix_congr
#print axioms OneY.Numeric.badAtTerminal_restrictedParent_above
#print axioms OneY.Numeric.badAtTerminal_restrictedParent_prefix
