import OneY.ExpansionCanonical
import ZeroY.SequenceOrder

/-! # Actual expansion preserves nested prefixes and strictly lowers lexicographic order -/

namespace OneY.Reconstruction

theorem value_succ_of_last_top (M N : RootGeometry.RowMountain) (topM topN : Nat → Nat)
    (x : Nat) (hH : ∀ c, c ≤ x → M.height c = N.height c)
    (hP : ∀ r c, c ≤ x → (M.row r).parent c = (N.row r).parent c)
    (hTop : ∀ c, c < x → topM c = topN c) (hLast : topM x+1 = topN x)
    (r : Nat) (hr : r ≤ N.height x) : value M topM r x+1 = value N topN r x := by
  have hParent : ∀ u, parentValue M topM u x = parentValue N topN u x := by
    intro u
    unfold parentValue
    rw [hP u x (Nat.le_refl _)]
    cases hp : (N.row u).parent x with
    | none => rfl
    | some p =>
        exact value_prefix_congr M N topM topN x
          (fun c hc => hH c (Nat.le_of_lt hc))
          (fun v c hc => hP v c (Nat.le_of_lt hc)) hTop p
          ((N.row u).parent_left hp) u
  rw [value_eq M topM, value_eq N topN, hH x (Nat.le_refl _)]
  simp only [hr, ↓reduceIte]
  have hSum := congrArg List.sum (List.map_congr_left (l := List.range' r (N.height x-r))
    (fun u _ => hParent u))
  omega

end OneY.Reconstruction

namespace OneY.Numeric

theorem lowerTowerValues_first_seam_succ (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) :
    ∀ k, k ≤ K → lowerTowerValues a hbad k x+1 = (layers a k).row.value x := by
  have aux : ∀ gap k, k+gap = K →
      lowerTowerValues a hbad k x+1 = (layers a k).row.value x := by
    intro gap
    induction gap with
    | zero =>
        intro k he
        have hk : k = K := by omega
        subst k
        rw [lowerTowerValues_active]
        exact badAtTerminal_first_seam_succ a hbad (Nat.zero_le d)
    | succ gap ih =>
        intro k he
        have hk : k < K := by omega
        have hi := lowerTower_inputs a hbad hk
        let C := badAtLowerContext a hbad hk
        rw [lowerTowerValues_succ a hbad hk]
        have hLast : lowerTowerValues a hbad (k+1) x+1 = topValue (layers a k).row x :=
          ih (k+1) (by omega)
        have h := Reconstruction.value_succ_of_last_top C.toRowMountain C.mountain
          (lowerTowerValues a hbad (k+1)) (topValue (layers a k).row) x
          (fun c hc => C.height_original hc)
          (fun r c hc => C.parent_original hc)
          (fun c hc => (hi.prefixTop c hc).symm) hLast 0 (Nat.zero_le _)
        exact h.trans (Reconstruction.value_numeric_base (layers a k).row (layers a k).positive x)
  intro k hk
  exact aux (K-k) k (by omega)

theorem assemble_expandedGraphs_first_seam_succ (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) :
    TowerReconstruction.assemble (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
      (fun _ => 1) x+1 = (ofSequence s).value x := by
  rw [assemble_expanded_sequence_lower]
  exact (congrFun (lowerTowerBase_value (rootedSequence s hs) hbad (Nat.zero_le K)) x) ▸
    lowerTowerValues_first_seam_succ (rootedSequence s hs) hbad 0 (Nat.zero_le K)

theorem expandValues_nested_take (s : List Nat) (hs : ZeroY.Legal s) {i j : Nat} (hij : i ≤ j) :
    (expandValues s hs j).take (expandValues s hs i).length = expandValues s hs i := by
  unfold expandValues
  dsimp only
  split
  · exact List.take_length
  · rename_i z hz
    have hle : s.length-1+i*(s.length-1-z.column) ≤ s.length-1+j*(s.length-1-z.column) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _
    simp only [reconstructedValues, List.length_map, List.length_range, ← List.map_take,
      List.take_range, Nat.min_eq_left hle]

theorem expandValues_first_seam_succ (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z)
    (hN : 0 < N) :
    (expandValues s hs N)[s.length-1]?.getD 1+1 = s[s.length-1]?.getD 1 := by
  have hbad := (findBadRoot_sound s hs _ hz).2
  have hy : z.column < s.length-1 := (rows (layers (rootedSequence s hs) z.layer).row z.row).forest.parent_left hbad.1
  have hL : 0 < s.length-1-z.column := by omega
  have hWidth : s.length-1 < s.length-1+N*(s.length-1-z.column) :=
    Nat.lt_add_of_pos_right (Nat.mul_pos hN hL)
  rw [expandValues_of_badRoot s hs N hz]
  simp only [reconstructedValues, List.getElem?_map, List.getElem?_range hWidth,
    Option.map_some, Option.getD_some]
  exact assemble_expandedGraphs_first_seam_succ s hs hbad

end OneY.Numeric

namespace ZeroY.SeqLt

theorem take_lt {s : List Nat} {n : Nat} (hn : n < s.length) : SeqLt (s.take n) s := by
  induction s generalizing n with
  | nil => simp at hn
  | cons a s ih =>
      cases n with
      | zero => exact .nil _ _
      | succ n => exact .tail a (ih (by simpa using hn))

theorem of_first_difference {s t : List Nat} {c : Nat}
    (hs : c < s.length) (ht : c < t.length)
    (hp : ∀ i, i < c → s[i]? = t[i]?) (hl : s[c] < t[c]) : SeqLt s t := by
  induction c generalizing s t with
  | zero =>
      cases s with
      | nil => simp at hs
      | cons a s =>
          cases t with
          | nil => simp at ht
          | cons b t => exact .head hl
  | succ c ih =>
      cases s with
      | nil => simp at hs
      | cons a s =>
          cases t with
          | nil => simp at ht
          | cons b t =>
              have hab : a = b := by simpa using hp 0 (by omega)
              subst b
              exact .tail a (ih (by simpa using hs) (by simpa using ht)
                (fun i hi => by simpa using hp (i+1) (by omega)) hl)

end ZeroY.SeqLt

namespace OneY.Numeric

theorem expandValues_lt (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    (hNonempty : s ≠ []) : ZeroY.SeqLt (expandValues s hs N) s := by
  have hsPos : 0 < s.length := List.length_pos_iff.mpr hNonempty
  have hx : s.length-1 < s.length := by omega
  by_cases hN : N = 0
  · rw [hN, expandValues_zero]
    exact ZeroY.SeqLt.take_lt hx
  · cases hz : findBadRoot s hs (s.length-1) with
    | none =>
        rw [expandValues_of_no_parent s hs N ((findBadRoot_none_iff _ _ _).mp hz)]
        exact ZeroY.SeqLt.take_lt hx
    | some z =>
        have hbad := (findBadRoot_sound s hs _ hz).2
        have hy : z.column < s.length-1 :=
          (rows (layers (rootedSequence s hs) z.layer).row z.row).forest.parent_left hbad.1
        have hWidth : s.length-1 < (expandValues s hs N).length := by
          rw [expandValues_of_badRoot s hs N hz, reconstructedValues_length]
          exact Nat.lt_add_of_pos_right (Nat.mul_pos (by omega) (by omega))
        apply ZeroY.SeqLt.of_first_difference hWidth hx (fun _ hi => expandValues_prefix s hs N hi)
        have h := expandValues_first_seam_succ s hs N hz (by omega)
        simp only [List.getElem?_eq_getElem hWidth, List.getElem?_eq_getElem hx, Option.getD_some] at h
        omega

theorem expand_lt (s : ZeroY.Expr) (N : Nat) (hNonempty : s.values ≠ []) :
    ZeroY.ExprLt (expand s N) s := expandValues_lt s.values s.legal N hNonempty

end OneY.Numeric

#print axioms OneY.Numeric.lowerTowerValues_first_seam_succ
#print axioms OneY.Numeric.expandValues_nested_take
#print axioms OneY.Numeric.expandValues_first_seam_succ
#print axioms OneY.Numeric.expandValues_lt
