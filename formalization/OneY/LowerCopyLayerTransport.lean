import OneY.LowerCopyRebuild
import OneY.ActiveGeometry

/-! # B/C propagation between the actual adjacent extracted layers -/

namespace OneY.Numeric

theorem badAtLowerCopiedBase_upperFixed (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k+1 < K) (newTop : Nat → Nat)
    (hPositive : ∀ c, 0 < newTop c)
    (hPrefix : ∀ s, s < x → topValue (layers a (k+1)).row s = newTop s)
    (hFixed : (badAtLowerContext a hbad hk).UpperFixed (topValue (layers a (k+1)).row) newTop) :
    (badAtLowerContext a hbad (by omega : k < K)).UpperFixed
      (topValue (layers a k).row) ((badAtLowerContext a hbad hk).copiedBase newTop hPositive).value := by
  intro s hs hx hGood b
  exact ((badAtLowerContext a hbad hk).value_copy_of_good_base_parent (layers a (k+1)).row
    (layers a (k+1)).positive (layers a (k+1)).rootsOne rfl newTop hPrefix hFixed hs hx hGood b).symm

theorem badAtLowerCopiedBase_upperOrder (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k+1 < K) (newTop : Nat → Nat)
    (hPositive : ∀ c, 0 < newTop c)
    (hPrefix : ∀ s, s < x → topValue (layers a (k+1)).row s = newTop s)
    (hFixed : (badAtLowerContext a hbad hk).UpperFixed (topValue (layers a (k+1)).row) newTop)
    (hUpper : (badAtLowerContext a hbad hk).UpperOrder (topValue (layers a (k+1)).row) newTop)
    (hBound : Reconstruction.PseudoTopBound (badAtLowerContext a hbad hk).toRowMountain newTop) :
    (badAtLowerContext a hbad (by omega : k < K)).UpperOrder
      (topValue (layers a k).row) ((badAtLowerContext a hbad hk).copiedBase newTop hPositive).value := by
  intro z c hz hzc hcx hFrame hLe b
  exact (badAtLowerContext a hbad hk).value_copy_le_of_common_frame (layers a (k+1)).row
    (layers a (k+1)).positive (layers a (k+1)).rootsOne rfl
    (Pseudo.forest (mountain (layers a k).row (layers a k).positive)) (fun _ => rfl)
    newTop hPositive hPrefix hFixed hUpper hBound hz hzc hcx hFrame hLe b

#print axioms badAtLowerCopiedBase_upperFixed
#print axioms badAtLowerCopiedBase_upperOrder

end OneY.Numeric
