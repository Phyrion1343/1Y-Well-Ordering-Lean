import OneY.LowerTowerInputs

/-! # Complete finite downward reconstruction of the copied extraction tower

All lower-layer comparison and pseudo-top hypotheses have been discharged
by `lowerTower_inputs`. The row family here is the actual finite assembly.
-/

namespace OneY.Numeric

theorem mountain_eq_of_row_eq {a b : Row} (ha : ∀ c, 0 < a.value c)
    (hb : ∀ c, 0 < b.value c) (h : a = b) : mountain a ha = mountain b hb := by
  cases h
  rfl

theorem lowerTowerBase_rootsOne (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k ≤ K) : (lowerTowerBase a hbad k).RootsOne := by
  by_cases hLower : k < K
  · have hi := lowerTower_inputs a hbad hLower
    rw [lowerTowerBase_lower a hbad hLower]
    exact (badAtLowerContext a hbad hLower).copiedBase_rootsOne (layers a k).row (layers a k).positive
      (layers a k).rootsOne rfl _ _ hi.prefixTop hi.fixed
  · have he : k = K := by omega
    subst k
    rw [lowerTowerBase_active]
    exact fun c hp => badAtTerminalBase_none_eq_one a hbad hp

theorem lowerTowerBase_mountain (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k ≤ K) :
    mountain (lowerTowerBase a hbad k) (lowerTowerBase_positive a hbad k) = expandedMountain a hbad k := by
  by_cases hLower : k < K
  · have hi := lowerTower_inputs a hbad hLower
    rw [mountain_eq_of_row_eq _ ((badAtLowerContext a hbad hLower).copiedBase_positive
      (lowerTowerValues a hbad (k+1)) (lowerTowerValues_positive a hbad (k+1)))
      (lowerTowerBase_lower a hbad hLower)]
    simp only [expandedMountain, dif_pos hLower]
    exact (badAtLowerContext a hbad hLower).copiedBase_mountain (layers a k).row (layers a k).positive
      rfl _ (lowerTowerValues_positive a hbad (k+1)) hi.prefixTop hi.fixed hi.order hi.bound
  · have he : k = K := by omega
    subst k
    rw [mountain_eq_of_row_eq _ (badAtTerminalBase_positive a hbad) (lowerTowerBase_active a hbad), expandedMountain_active]
    exact badAtTerminalBase_mountain a hbad

theorem lowerTowerBase_select_external (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k ≤ K) (F : ParentForest)
    (hSelected : ∀ c, restrictedParent F (layers a k).row.value c = (layers a k).row.forest.parent c) :
    select (FrameCopy.forest (badAtTerminalContext a hbad).coordinates F) (lowerTowerBase a hbad k).value =
      lowerTowerBase a hbad k := by
  by_cases hLower : k < K
  · have hi := lowerTower_inputs a hbad hLower
    rw [lowerTowerBase_lower a hbad hLower]
    apply Row.ext_values_parents
    · rfl
    · funext c
      exact (badAtLowerContext a hbad hLower).restrictedParent_bottom_numeric (layers a k).row
        (layers a k).positive (layers a k).rootsOne rfl F hSelected _ (lowerTowerValues_positive a hbad (k+1))
        hi.prefixTop hi.fixed hi.order hi.bound c
  · have he : k = K := by omega
    subst k
    rw [lowerTowerBase_active]
    exact badAtTerminalBase_select_external a hbad F hSelected

theorem lowerTowerBase_rawExtract_next (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) :
    rawExtract (lowerTowerBase a hbad k) (lowerTowerBase_positive a hbad k) = lowerTowerBase a hbad (k+1) := by
  have hi := lowerTower_inputs a hbad hk
  rw [rawExtract_eq_of_row_eq _ ((badAtLowerContext a hbad hk).copiedBase_positive
      (lowerTowerValues a hbad (k+1)) (lowerTowerValues_positive a hbad (k+1)))
      (lowerTowerBase_lower a hbad hk),
    (badAtLowerContext a hbad hk).copiedBase_rawExtract (layers a k).row (layers a k).positive
      rfl _ (lowerTowerValues_positive a hbad (k+1)) hi.prefixTop hi.fixed hi.order hi.bound,
    ← lowerTowerBase_value a hbad (by omega : k+1 ≤ K)]
  exact lowerTowerBase_select_external a hbad (by omega : k+1 ≤ K)
    (mountain (layers a k).row (layers a k).positive).topForest
    (fun c => (rawExtract_parent_eq_topForest (layers a k).row (layers a k).positive c).symm)

def lowerTowerRooted (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) : RootedRow where
  row := lowerTowerBase a hbad 0
  positive := lowerTowerBase_positive a hbad 0
  rootsOne := lowerTowerBase_rootsOne a hbad (Nat.zero_le _)

theorem lowerTowerRooted_layers_below (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k ≤ K) :
    (layers (lowerTowerRooted a hbad) k).row = lowerTowerBase a hbad k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change rawExtract (layers (lowerTowerRooted a hbad) k).row _ = _
      rw [rawExtract_eq_of_row_eq _ (lowerTowerBase_positive a hbad k) (ih (by omega))]
      exact lowerTowerBase_rawExtract_next a hbad (by omega)

theorem rootedRow_eq_of_row_eq {a b : RootedRow} (h : a.row = b.row) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem layers_add (a : RootedRow) (k j : Nat) : layers (layers a k) j = layers a (k+j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change (layers (layers a k) j).extract = _
      rw [ih]
      rfl

theorem lowerTowerRooted_at_active (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) : layers (lowerTowerRooted a hbad) K = badAtTerminalRooted a hbad := by
  apply rootedRow_eq_of_row_eq
  rw [lowerTowerRooted_layers_below a hbad (Nat.le_refl _), lowerTowerBase_active]
  rfl

theorem lowerTowerRooted_layers_mountain (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k : Nat) :
    mountain (layers (lowerTowerRooted a hbad) k).row
      (layers (lowerTowerRooted a hbad) k).positive = expandedMountain a hbad k := by
  by_cases hk : k ≤ K
  · have he := lowerTowerRooted_layers_below a hbad hk
    have hm : mountain (layers (lowerTowerRooted a hbad) k).row
        (layers (lowerTowerRooted a hbad) k).positive =
      mountain (lowerTowerBase a hbad k) (lowerTowerBase_positive a hbad k) := by congr 1
    rw [hm]
    exact lowerTowerBase_mountain a hbad hk
  · have he : K+(k-K) = k := by omega
    have hAt := badAtTerminalRooted_layers_mountain a hbad (k-K)
    rw [← lowerTowerRooted_at_active a hbad, layers_add, he] at hAt
    exact hAt

theorem lowerTowerRooted_select_linear (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) :
    select linearForest (lowerTowerRooted (rootedSequence s hs) hbad).row.value =
      (lowerTowerRooted (rootedSequence s hs) hbad).row := by
  have ht := lowerTowerBase_select_external (rootedSequence s hs) hbad (Nat.zero_le K) linearForest (fun _ => rfl)
  rwa [FrameCopy.linear_forest] at ht

theorem assemble_expanded_sequence_from_lower (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y k : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) (hk : k ≤ K) :
    TowerReconstruction.assemble
      ((List.range' k (sequenceBound s-k)).map (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) =
        lowerTowerValues (rootedSequence s hs) hbad k := by
  have hK : K < sequenceBound s := by
    have hLayer := badAt_layer_bound hbad
    have hValue := sequence_value_le_bound s x
    change K+2 ≤ (ofSequence s).value x at hLayer
    omega
  have main : ∀ gap k, k+gap = K →
      TowerReconstruction.assemble
        ((List.range' k (sequenceBound s-k)).map (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) =
          lowerTowerValues (rootedSequence s hs) hbad k := by
    intro gap
    induction gap with
    | zero =>
        intro k he
        have hEq : k = K := by omega
        subst k
        rw [lowerTowerValues_active]
        exact assemble_expanded_sequence_active s hs hbad hK
    | succ gap ih =>
        intro k he
        have hk : k < K := by omega
        have hCount : sequenceBound s-k = (sequenceBound s-(k+1))+1 := by omega
        rw [hCount, List.range'_succ, List.map_cons, TowerReconstruction.assemble,
          ih (k+1) (by omega), lowerTowerValues_succ _ hbad hk]
        simp only [expandedMountain, dif_pos hk]
  exact main (K-k) k (by omega)

theorem assemble_expanded_sequence_lower (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) :
    TowerReconstruction.assemble (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) (fun _ => 1) =
      (lowerTowerRooted (rootedSequence s hs) hbad).row.value := by
  change _ = (lowerTowerBase (rootedSequence s hs) hbad 0).value
  rw [lowerTowerBase_value _ hbad (Nat.zero_le _)]
  simpa only [expandedGraphs, List.range_eq_range', Nat.sub_zero] using
    assemble_expanded_sequence_from_lower s hs hbad (Nat.zero_le K)

#print axioms lowerTowerBase_rawExtract_next
#print axioms lowerTowerRooted_layers_mountain
#print axioms lowerTowerRooted_select_linear
#print axioms assemble_expanded_sequence_lower

end OneY.Numeric
