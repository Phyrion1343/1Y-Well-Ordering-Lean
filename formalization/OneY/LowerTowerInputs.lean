import OneY.LowerCopyLayerTopBound
import OneY.TerminalCopyUpperOrder
import OneY.TerminalTowerRebuild

/-! # Finite downward assembly and its proved layer inputs -/

namespace OneY.Numeric

def lowerTowerValues (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (k : Nat) : Nat → Nat :=
  TowerReconstruction.assemble ((List.range' k (K-k)).map (expandedMountain a hbad))
    (badAtTerminalBase a hbad).value

theorem lowerTowerValues_positive (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k c : Nat) : 0 < lowerTowerValues a hbad k c :=
  TowerReconstruction.assemble_positive _ _ (badAtTerminalBase_positive a hbad) c

theorem lowerTowerValues_active (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : lowerTowerValues a hbad K = (badAtTerminalBase a hbad).value := by
  simp only [lowerTowerValues, Nat.sub_self, List.range'_zero, List.map_nil, TowerReconstruction.assemble]

theorem lowerTowerValues_succ (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) :
    lowerTowerValues a hbad k =
      Reconstruction.value (badAtLowerContext a hbad hk).toRowMountain (lowerTowerValues a hbad (k+1)) 0 := by
  have he : K-k = (K-(k+1))+1 := by omega
  unfold lowerTowerValues
  rw [he, List.range'_succ, List.map_cons, TowerReconstruction.assemble]
  simp only [expandedMountain, dif_pos hk]

def lowerTowerBase (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (k : Nat) : Row :=
  if hk : k < K then (badAtLowerContext a hbad hk).copiedBase
    (lowerTowerValues a hbad (k+1)) (lowerTowerValues_positive a hbad (k+1))
  else badAtTerminalBase a hbad

theorem lowerTowerBase_lower (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) :
    lowerTowerBase a hbad k = (badAtLowerContext a hbad hk).copiedBase
      (lowerTowerValues a hbad (k+1)) (lowerTowerValues_positive a hbad (k+1)) := by
  rw [lowerTowerBase, dif_pos hk]

theorem lowerTowerBase_active (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : lowerTowerBase a hbad K = badAtTerminalBase a hbad := by
  rw [lowerTowerBase, dif_neg (Nat.lt_irrefl _)]

theorem lowerTowerBase_positive (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k c : Nat) : 0 < (lowerTowerBase a hbad k).value c := by
  unfold lowerTowerBase
  split
  · exact LowerCopy.Context.copiedBase_positive _ _ _ c
  · exact badAtTerminalBase_positive a hbad c

theorem lowerTowerBase_value (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k ≤ K) :
    (lowerTowerBase a hbad k).value = lowerTowerValues a hbad k := by
  by_cases hlt : k < K
  · rw [lowerTowerBase_lower a hbad hlt, lowerTowerValues_succ a hbad hlt]
    rfl
  · have he : k = K := by omega
    subst k
    rw [lowerTowerBase_active, lowerTowerValues_active]

/-- These are precisely the four hypotheses already required by the local
lower recovery theorem. Their actual supply is proved below. -/
structure LowerTowerInputs (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (k : Nat) (hk : k < K) : Prop where
  prefixTop : ∀ s, s < x → topValue (layers a k).row s = lowerTowerValues a hbad (k+1) s
  fixed : (badAtLowerContext a hbad hk).UpperFixed (topValue (layers a k).row) (lowerTowerValues a hbad (k+1))
  order : (badAtLowerContext a hbad hk).UpperOrder (topValue (layers a k).row) (lowerTowerValues a hbad (k+1))
  bound : Reconstruction.PseudoTopBound (badAtLowerContext a hbad hk).toRowMountain (lowerTowerValues a hbad (k+1))

theorem lowerTower_prefix_and_inputs (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : ∀ k, k ≤ K →
    (∀ s, s < x → lowerTowerValues a hbad k s = (layers a k).row.value s) ∧
      ∀ hk : k < K, LowerTowerInputs a hbad k hk := by
  have main : ∀ gap k, k+gap = K →
      (∀ s, s < x → lowerTowerValues a hbad k s = (layers a k).row.value s) ∧
        ∀ hk : k < K, LowerTowerInputs a hbad k hk := by
    intro gap
    induction gap with
    | zero =>
        intro k he
        have hEq : k = K := by omega
        subst k
        constructor
        · intro s hs
          rw [lowerTowerValues_active]
          let T := badAtTerminalContext a hbad
          change Reconstruction.value T.toRowMountain
            (T.ordinaryContext.copyValue (topValue (layers a K).row)) 0 s = _
          rw [T.value_original (topValue (layers a K).row) hs 0]
          exact Reconstruction.value_numeric_base (layers a K).row (layers a K).positive s
        · intro hk
          omega
    | succ gap ih =>
        intro k he
        have hk : k < K := by omega
        have hNext := ih (k+1) (by omega)
        have hPrefix : ∀ s, s < x → topValue (layers a k).row s = lowerTowerValues a hbad (k+1) s :=
          fun s hs => (hNext.1 s hs).symm
        have hInputs : LowerTowerInputs a hbad k hk := by
          refine ⟨hPrefix, ?_, ?_, ?_⟩
          all_goals
            by_cases hNextLower : k+1 < K
            · have hi := hNext.2 hNextLower
              have hValue : ((badAtLowerContext a hbad hNextLower).copiedBase
                  (lowerTowerValues a hbad (k+1+1)) (lowerTowerValues_positive a hbad (k+1+1))).value =
                    lowerTowerValues a hbad (k+1) := (lowerTowerValues_succ a hbad hNextLower).symm
              first
              | simpa only [hValue] using badAtLowerCopiedBase_upperFixed a hbad hNextLower
                  (lowerTowerValues a hbad (k+1+1)) (lowerTowerValues_positive a hbad (k+1+1)) hi.prefixTop hi.fixed
              | simpa only [hValue] using badAtLowerCopiedBase_upperOrder a hbad hNextLower
                  (lowerTowerValues a hbad (k+1+1)) (lowerTowerValues_positive a hbad (k+1+1)) hi.prefixTop hi.fixed hi.order hi.bound
              | simpa only [hValue] using badAtLowerCopiedBase_lowerTopBound a hbad hNextLower
                  (lowerTowerValues a hbad (k+1+1)) (lowerTowerValues_positive a hbad (k+1+1)) hi.prefixTop hi.fixed hi.order hi.bound
            · have hEq : K = k+1 := by omega
              clear he
              subst K
              rw [lowerTowerValues_active]
              first
              | exact badAtTerminalBase_upperFixed a hbad
              | exact badAtTerminalBase_upperOrder a hbad
              | exact badAtTerminalBase_lowerTopBound a hbad
        constructor
        · intro s hs
          rw [lowerTowerValues_succ a hbad hk,
            ← (badAtLowerContext a hbad hk).value_original_prefix_eq (topValue (layers a k).row)
              (lowerTowerValues a hbad (k+1)) hInputs.prefixTop hs 0]
          exact Reconstruction.value_numeric_base (layers a k).row (layers a k).positive s
        · intro _
          exact hInputs
  intro k hk
  exact main (K-k) k (by omega)

theorem lowerTower_inputs (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) : LowerTowerInputs a hbad k hk :=
  (lowerTower_prefix_and_inputs a hbad k (Nat.le_of_lt hk)).2 hk

#print axioms lowerTower_prefix_and_inputs
#print axioms lowerTower_inputs

end OneY.Numeric
