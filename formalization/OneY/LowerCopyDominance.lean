import OneY.LowerCopyNesting
import OneY.Reconstruction
import OneY.ReconstructionNumeric
import OneY.Pseudo

/-! # Numerical domination from the actual lower copy graph

The sole numerical transport input compares copied top values to their source
tops. The reconstruction itself is the computed value function.
-/

namespace OneY.LowerCopy.Context

open Reconstruction

def rowCopy (C : Context) (b s r : Nat) : Nat :=
  if C.InCone s ∧ C.floor ≤ r then r+b*C.rise else r

theorem not_inCone_of_good (C : Context) {s : Nat} (hs : s < C.coordinates.y) :
    ¬ C.InCone s := by
  intro h
  have := C.root_le_of_inCone h
  omega

theorem rowCopy_low (C : Context) {r : Nat} (hr : r < C.floor) (b s : Nat) :
    C.rowCopy b s r = r := by
  rw [rowCopy, if_neg (by intro h; omega)]

theorem rowCopy_outside (C : Context) {s : Nat} (hs : ¬ C.InCone s) (b r : Nat) :
    C.rowCopy b s r = r := by
  rw [rowCopy, if_neg (by intro h; exact hs h.1)]

theorem rowCopy_live (C : Context) {s r : Nat} (hs : s ≤ C.coordinates.x)
    (hr : r ≤ C.mountain.height s) (b : Nat) :
    C.rowCopy b s r ≤ C.height (C.coordinates.parentCopy b s) := by
  rw [C.height_parentCopy hs b]
  unfold rowCopy
  by_cases hCone : C.InCone s
  · rw [if_pos hCone]
    split <;> omega
  · rw [if_neg hCone, if_neg (by intro h; exact hCone h.1)]
    exact hr

theorem rowCopy_top (C : Context) {s : Nat} (hs : s ≤ C.coordinates.x) (b : Nat) :
    C.rowCopy b s (C.mountain.height s) = C.height (C.coordinates.parentCopy b s) := by
  rw [C.height_parentCopy hs b]
  unfold rowCopy
  by_cases hCone : C.InCone s
  · rw [if_pos hCone, if_pos ⟨hCone, hCone.1⟩]
  · rw [if_neg hCone, if_neg (by intro h; exact hCone h.1)]

theorem rowCopy_succ_le (C : Context) (b s r : Nat) :
    C.rowCopy b s r+1 ≤ C.rowCopy b s (r+1) := by
  unfold rowCopy
  split
  · rename_i h
    rw [if_pos ⟨h.1, by omega⟩]
    omega
  · split <;> omega

theorem rowCopy_parent (C : Context) {s p r : Nat}
    (hp : (C.mountain.row r).parent s = some p) (b : Nat) :
    C.rowCopy b p r = C.rowCopy b s r := by
  by_cases hLow : r < C.floor
  · rw [C.rowCopy_low hLow, C.rowCopy_low hLow]
  · have hr : C.floor ≤ r := by omega
    by_cases hCone : C.InCone s
    · rw [rowCopy, rowCopy, if_pos ⟨C.high_parent_inCone hCone hr hp, hr⟩,
        if_pos ⟨hCone, hr⟩]
    · rw [C.rowCopy_outside (C.high_parent_outside hr hCone hp), C.rowCopy_outside hCone]

/-- Away from the root seam, old parent edges transport exactly at their
appropriate physical row. -/
theorem parent_rowCopy (C : Context) {s p r : Nat}
    (hs : s ≤ C.coordinates.x) (hNotRoot : s ≠ C.coordinates.y)
    (hp : (C.mountain.row r).parent s = some p) (b : Nat) :
    C.parent (C.rowCopy b s r) (C.coordinates.parentCopy b s) =
      some (C.coordinates.parentCopy b p) := by
  have hLeft := (C.mountain.row r).parent_left hp
  by_cases hGood : s < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hGood,
      C.coordinates.parentCopy_good b (by omega),
      C.rowCopy_outside (C.not_inCone_of_good hGood), C.parent_original hs]
    exact hp
  · have hAfter : C.coordinates.y < s := by omega
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hAfter)]
    by_cases hMove : C.InCone s ∧ C.floor ≤ r
    · rw [rowCopy, if_pos hMove]
      change C.parent (r+b*C.rise) (C.coordinates.encode s b) = _
      rw [C.parent_encode_lifted hAfter hs hMove.1 hMove.2 b, hp, Option.map_some,
        C.coordinates.parentCopy_bad b (C.root_le_of_inCone (C.high_parent_inCone hMove.1 hMove.2 hp))]
    · rw [rowCopy, if_neg hMove]
      change C.parent r (C.coordinates.encode s b) = _
      rw [C.parent_encode hAfter hs b r, if_neg hMove, hp, Option.map_some]

theorem value_row_antitone (M : RootGeometry.RowMountain) (top : Nat → Nat)
    {c r t : Nat} (hrt : r ≤ t) (ht : t ≤ M.height c) :
    value M top t c ≤ value M top r c := by
  induction hrt with
  | refl => exact Nat.le_refl _
  | @step t hrt ih =>
      have hPrev := ih (by omega)
      have he := value_eq_succ_parentValue M top (by omega : t < M.height c)
      change value M top (t+1) c ≤ value M top r c
      omega

theorem value_ancestor_le (M : RootGeometry.RowMountain) (top : Nat → Nat)
    {r a c : Nat} (ha : (M.row r).Ancestor a c) : value M top r a ≤ value M top r c := by
  induction ha with
  | direct hp => rw [value_recurrence M top hp]; omega
  | step _ hp ih => rw [value_recurrence M top hp]; omega

theorem ancestor_parent_or_eq (F : ParentForest) {a c p : Nat}
    (ha : F.Ancestor a c) (hp : F.parent c = some p) : F.Ancestor a p ∨ a = p := by
  cases ha with
  | direct h => exact Or.inr (Option.some.inj (h.symm.trans hp))
  | step ha h =>
      have he := Option.some.inj (h.symm.trans hp)
      subst p
      exact Or.inl ha

theorem parent_rowCopy_nonseam (C : Context) {s p r b : Nat}
    (hs : s ≤ C.coordinates.x) (hSeam : s ≠ C.coordinates.y ∨ b = 0)
    (hp : (C.mountain.row r).parent s = some p) :
    C.parent (C.rowCopy b s r) (C.coordinates.parentCopy b s) =
      some (C.coordinates.parentCopy b p) := by
  rcases hSeam with hNot | hb
  · exact C.parent_rowCopy hs hNot hp b
  · subst b
    have hr : C.rowCopy 0 s r = r := by simp [rowCopy]
    rw [hr, C.coordinates.parentCopy_zero, C.coordinates.parentCopy_zero, C.parent_original hs]
    exact hp

/-- Positive values are not required for weak domination: all parent sums are
nonnegative. Copied roots compare to the old root `y`, not to the old last `x`.
The hypothesis is purely about top values and does not assume canonicality. -/
theorem value_copy_dominance (C : Context) (oldTop newTop : Nat → Nat)
    (hTop : ∀ s, s < C.coordinates.x → ∀ b,
      oldTop s ≤ newTop (C.coordinates.parentCopy b s))
    {s r : Nat} (hs : s < C.coordinates.x) (hr : r ≤ C.mountain.height s) (b : Nat) :
    value C.mountain oldTop r s ≤
      value C.toRowMountain newTop (C.rowCopy b s r) (C.coordinates.parentCopy b s) := by
  have all : ∀ c s b, s < C.coordinates.x → C.coordinates.parentCopy b s = c →
      ∀ r, r ≤ C.mountain.height s →
        value C.mountain oldTop r s ≤ value C.toRowMountain newTop (C.rowCopy b s r) c := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
        intro s b hs he r hr
        by_cases hSpecial : s = C.coordinates.y ∧ 0 < b
        · obtain ⟨hsy, hb⟩ := hSpecial
          subst s
          by_cases hLow : r < C.floor
          · have hOldHeight : r < C.mountain.height C.coordinates.x := by
              have := C.last_higher
              change C.floor < C.mountain.height C.coordinates.x at this
              omega
            obtain ⟨p, hp⟩ := C.mountain.parent_exists r C.coordinates.x hOldHeight
            have hpLt := (C.mountain.row r).parent_left hp
            have hYP := ancestor_parent_or_eq (C.mountain.row r) (C.root_ancestor_last_low hLow) hp
            have hOldLe : value C.mountain oldTop r C.coordinates.y ≤ value C.mountain oldTop r p := by
              rcases hYP with ha | heq
              · exact value_ancestor_le C.mountain oldTop ha
              · rw [heq]; exact Nat.le_refl _
            have hRootEq : C.coordinates.parentCopy b C.coordinates.y =
                C.coordinates.encode C.coordinates.x (b-1) := by
              rw [C.coordinates.parentCopy_bad b (Nat.le_refl _)]
              have ht := C.root_copy_succ_eq (b-1)
              rw [Nat.sub_add_cancel hb] at ht
              exact ht
            have hParent : C.parent r c = some (C.coordinates.parentCopy (b-1) p) := by
              rw [← he, hRootEq, C.parent_encode_low C.coordinates.root_lt_last (Nat.le_refl _) hLow,
                hp, Option.map_some]
            have hDom := ih _ (C.parent_left hParent) p (b-1) hpLt rfl r (C.mountain.parent_endpoint hp)
            rw [C.rowCopy_low hLow] at hDom
            have hRec := value_recurrence C.toRowMountain newTop hParent
            rw [C.rowCopy_low hLow]
            omega
          · have hAtTop : r = C.mountain.height C.coordinates.y := by
              change r ≤ C.floor at hr
              change r = C.floor
              omega
            rw [hAtTop, value_top, C.rowCopy_top (Nat.le_of_lt C.coordinates.root_lt_last) b, he]
            change oldTop C.coordinates.y ≤ value C.toRowMountain newTop (C.toRowMountain.height c) c
            rw [value_top]
            simpa only [he] using hTop C.coordinates.y C.coordinates.root_lt_last b
        · have hSeam : s ≠ C.coordinates.y ∨ b = 0 := by
            by_cases hsy : s = C.coordinates.y
            · exact Or.inr (by by_cases hb : b = 0; exact hb; exact False.elim (hSpecial ⟨hsy, by omega⟩))
            · exact Or.inl hsy
          have below : ∀ gap r, r+gap = C.mountain.height s →
              value C.mountain oldTop r s ≤ value C.toRowMountain newTop (C.rowCopy b s r) c := by
            intro gap
            induction gap with
            | zero =>
                intro r hr
                have hAtTop : r = C.mountain.height s := by omega
                rw [hAtTop, value_top, C.rowCopy_top (Nat.le_of_lt hs) b, he]
                change oldTop s ≤ value C.toRowMountain newTop (C.toRowMountain.height c) c
                rw [value_top]
                simpa only [he] using hTop s hs b
            | succ gap ihRow =>
                intro r hr
                have hOldLive : r < C.mountain.height s := by omega
                obtain ⟨p, hp⟩ := C.mountain.parent_exists r s hOldLive
                have hParent := C.parent_rowCopy_nonseam (Nat.le_of_lt hs) hSeam hp
                rw [he] at hParent
                have hpLt := (C.mountain.row r).parent_left hp
                have hDom := ih _ (C.parent_left hParent) p b (by omega) rfl r (C.mountain.parent_endpoint hp)
                rw [C.rowCopy_parent hp b] at hDom
                have hUpper := ihRow (r+1) (by omega)
                have hNewLive := C.rowCopy_live (Nat.le_of_lt hs) (by omega : r+1 ≤ C.mountain.height s) b
                rw [he] at hNewLive
                have hVertical := value_row_antitone C.toRowMountain newTop
                  (C.rowCopy_succ_le b s r) hNewLive
                have hOldRec := value_recurrence C.mountain oldTop hp
                have hNewRec := value_recurrence C.toRowMountain newTop hParent
                omega
          exact below (C.mountain.height s-r) r (by omega)
  exact all _ s b hs rfl r hr

/-- At an unchanged physical row, extra inserted rows only add further
nonnegative contributions, so domination holds there as well. -/
theorem value_copy_dominance_unshifted (C : Context) (oldTop newTop : Nat → Nat)
    (hTop : ∀ s, s < C.coordinates.x → ∀ b,
      oldTop s ≤ newTop (C.coordinates.parentCopy b s))
    {s r : Nat} (hs : s < C.coordinates.x) (hr : r ≤ C.mountain.height s) (b : Nat) :
    value C.mountain oldTop r s ≤
      value C.toRowMountain newTop r (C.coordinates.parentCopy b s) := by
  have hDom := C.value_copy_dominance oldTop newTop hTop hs hr b
  have hRow : r ≤ C.rowCopy b s r := by unfold rowCopy; split <;> omega
  have hVertical := value_row_antitone C.toRowMountain newTop hRow
    (C.rowCopy_live (Nat.le_of_lt hs) hr b)
  omega

/-- Numerical-mountain specialization: the left side is the actual original
row value, by the proved reconstruction round trip. -/
theorem value_copy_dominance_numeric (C : Context) (base : Numeric.Row)
    (hPositive : ∀ c, 0 < base.value c)
    (hMountain : C.mountain = Numeric.mountain base hPositive)
    (newTop : Nat → Nat)
    (hTop : ∀ s, s < C.coordinates.x → ∀ b,
      Numeric.topValue base s ≤ newTop (C.coordinates.parentCopy b s))
    {s r : Nat} (hs : s < C.coordinates.x) (hr : r ≤ C.mountain.height s) (b : Nat) :
    (Numeric.rows base r).value s ≤
      value C.toRowMountain newTop (C.rowCopy b s r) (C.coordinates.parentCopy b s) := by
  have hDom := C.value_copy_dominance (Numeric.topValue base) newTop hTop hs hr b
  rw [hMountain, value_numeric_mountain] at hDom
  exact hDom

/-- If good-part tops are fixed, their reconstructed values are exactly fixed.
This equality uses only prefix dependence, independently of canonicality. -/
theorem value_good_eq (C : Context) (oldTop newTop : Nat → Nat)
    (hTop : ∀ s, s < C.coordinates.y → oldTop s = newTop s)
    {s : Nat} (hs : s < C.coordinates.y) (r : Nat) :
    value C.mountain oldTop r s = value C.toRowMountain newTop r s := by
  apply value_prefix_congr C.mountain C.toRowMountain oldTop newTop C.coordinates.y
    (fun c hc => (C.height_original (by have := C.coordinates.root_lt_last; omega)).symm)
    (fun u c hc => (C.parent_original (r := u) (by have := C.coordinates.root_lt_last; omega)).symm)
    hTop s hs r

theorem higher_parent_good (C : Context) {s p q r u : Nat}
    (hp : (C.mountain.row r).parent s = some p) (hGood : p < C.coordinates.y)
    (hru : r ≤ u) (hq : (C.mountain.row u).parent s = some q) : q < C.coordinates.y := by
  have ha := (C.mountain.refines_le hru) hq
  rcases ancestor_parent_or_eq (C.mountain.row r) ha hp with ha | he
  · have := ha.lt; omega
  · omega

theorem not_inCone_of_good_parent (C : Context) {s p r : Nat}
    (hs : C.coordinates.y < s) (hp : (C.mountain.row r).parent s = some p)
    (hGood : p < C.coordinates.y) : ¬ C.InCone s := by
  intro hCone
  by_cases hr : C.floor ≤ r
  · have := C.root_le_of_inCone (C.high_parent_inCone hCone hr hp)
    omega
  · obtain ⟨q, hq⟩ := C.mountain.parent_exists C.floor s (C.height_lt_of_inCone hCone hs)
    have hqGood := C.higher_parent_good hp hGood (by omega) hq
    have := C.root_le_of_inCone (C.high_parent_inCone hCone (Nat.le_refl _) hq)
    omega

/-- A genuine good finite parent also puts the old pseudo-parent in the good
part. The proof uses the last *nonempty* finite row, not the empty top row. -/
theorem pseudo_parent_good_of_row_parent_good (C : Context) {s p q r : Nat}
    (hp : (C.mountain.row r).parent s = some p) (hGood : p < C.coordinates.y)
    (hq : Pseudo.parent C.mountain s = some q) : q < C.coordinates.y := by
  have hHeight := C.mountain.parent_source hp
  have ha := ParentForest.Refines.ancestor (C.mountain.refines_le
    (by omega : r ≤ C.mountain.height s-1)) (Pseudo.parent_ancestor C.mountain hq)
  rcases ancestor_parent_or_eq (C.mountain.row r) ha hp with ha | he
  · have := ha.lt; omega
  · omega

theorem pseudo_ancestor_good_of_row_parent_good (C : Context) {s p q r : Nat}
    (hp : (C.mountain.row r).parent s = some p) (hGood : p < C.coordinates.y)
    (ha : (Pseudo.forest C.mountain).Ancestor q s) : q < C.coordinates.y := by
  cases hPseudo : Pseudo.parent C.mountain s with
  | none =>
      have hHeight := (Pseudo.parent_none_iff C.mountain s).mp hPseudo
      have := C.mountain.parent_source hp
      omega
  | some a =>
      have hAGood := C.pseudo_parent_good_of_row_parent_good hp hGood hPseudo
      rcases ancestor_parent_or_eq (Pseudo.forest C.mountain) ha hPseudo with ha | he
      · have := ha.lt; omega
      · omega

/-- Exact input for the upper-layer fixed-value induction: every actual
extracted parent is good, if the lower finite row has a genuine good parent. -/
theorem extracted_parent_good_of_row_parent_good (C : Context) (top : Nat → Nat)
    {s p q r : Nat} (hp : (C.mountain.row r).parent s = some p)
    (hGood : p < C.coordinates.y)
    (hq : Numeric.restrictedParent (Pseudo.forest C.mountain) top s = some q) :
    q < C.coordinates.y :=
  C.pseudo_ancestor_good_of_row_parent_good hp hGood
    (ParentForest.ancestor_of_zeroY (Numeric.restrictedParent_spec _ _ hq).1)

/-- Correct finite-tail preservation: a genuine good-part parent forces the
whole higher tail outside the lifted cone. Given fixed good-part and source
tops, every reconstructed value in that tail is fixed as well. -/
theorem value_tail_eq_of_good_parent (C : Context) (oldTop newTop : Nat → Nat)
    (hGoodTop : ∀ q, q < C.coordinates.y → oldTop q = newTop q)
    {s p r : Nat} (hs : C.coordinates.y < s) (hx : s < C.coordinates.x)
    (hp : (C.mountain.row r).parent s = some p) (hGood : p < C.coordinates.y)
    (b : Nat) (hTop : oldTop s = newTop (C.coordinates.parentCopy b s)) :
    ∀ u, r ≤ u → value C.mountain oldTop u s =
      value C.toRowMountain newTop u (C.coordinates.parentCopy b s) := by
  have hOut := C.not_inCone_of_good_parent hs hp hGood
  have hHeight : C.height (C.coordinates.parentCopy b s) = C.mountain.height s := by
    rw [C.height_parentCopy (Nat.le_of_lt hx) b, if_neg hOut]
  have below : ∀ gap u, u+gap = C.mountain.height s → r ≤ u →
      value C.mountain oldTop u s = value C.toRowMountain newTop u (C.coordinates.parentCopy b s) := by
    intro gap
    induction gap with
    | zero =>
        intro u hu _
        have he : u = C.mountain.height s := by omega
        rw [he, value_top, ← hHeight]
        change oldTop s = value C.toRowMountain newTop
          (C.toRowMountain.height (C.coordinates.parentCopy b s)) _
        rw [value_top]
        exact hTop
    | succ gap ih =>
        intro u hu hru
        obtain ⟨q, hq⟩ := C.mountain.parent_exists u s (by omega)
        have hqGood := C.higher_parent_good hp hGood hru hq
        have hNew := C.parent_rowCopy (Nat.le_of_lt hx) (by omega) hq b
        rw [C.rowCopy_outside hOut, C.coordinates.parentCopy_good b hqGood] at hNew
        rw [value_recurrence C.mountain oldTop hq, value_recurrence C.toRowMountain newTop hNew,
          ih (u+1) (by omega) (by omega), C.value_good_eq oldTop newTop hGoodTop hqGood u]
  intro u hru
  by_cases hu : u ≤ C.mountain.height s
  · exact below (C.mountain.height s-u) u (by omega) hru
  · rw [value_absent C.mountain oldTop (by omega),
      value_absent C.toRowMountain newTop (by change C.height _ < u; omega)]

/-- An empty parent at an old top is *not* sufficient for unshifted tail
preservation inside the lifted cone: its copied value is strictly larger.
This isolates the necessary exception to that informal preservation claim. -/
theorem old_top_strictly_increases_in_cone (C : Context) (oldTop newTop : Nat → Nat)
    (hPositive : ∀ c, 0 < newTop c) {s : Nat}
    (hs : s ≤ C.coordinates.x) (hCone : C.InCone s) (b : Nat) (hb : 0 < b)
    (hTop : oldTop s ≤ newTop (C.coordinates.parentCopy b s)) :
    value C.mountain oldTop (C.mountain.height s) s <
      value C.toRowMountain newTop (C.mountain.height s) (C.coordinates.parentCopy b s) := by
  have hRise := C.rise_pos
  have hMul : 0 < b*C.rise := Nat.mul_pos hb hRise
  have hHeight := C.height_parentCopy hs b
  rw [if_pos hCone] at hHeight
  have hLive : C.mountain.height s < C.toRowMountain.height (C.coordinates.parentCopy b s) := by
    change C.mountain.height s < C.height _
    omega
  have hStep := next_row_value_lt C.toRowMountain newTop hPositive hLive
  have hTopLe := top_le_value C.toRowMountain newTop (by omega :
    C.mountain.height s+1 ≤ C.toRowMountain.height (C.coordinates.parentCopy b s))
  rw [value_top]
  omega

/-- A tail starting at an empty old parent requires an explicit top equality.
It is fixed at synchronized heights, with zero values above both tops. -/
theorem value_top_tail_eq (C : Context) (oldTop newTop : Nat → Nat)
    {s : Nat} (hs : s ≤ C.coordinates.x) (b : Nat)
    (hTop : oldTop s = newTop (C.coordinates.parentCopy b s)) :
    ∀ u, C.mountain.height s ≤ u → value C.mountain oldTop u s =
      value C.toRowMountain newTop (C.rowCopy b s u) (C.coordinates.parentCopy b s) := by
  intro u hu
  by_cases he : u = C.mountain.height s
  · rw [he, value_top, C.rowCopy_top hs b]
    change oldTop s = value C.toRowMountain newTop
      (C.toRowMountain.height (C.coordinates.parentCopy b s)) _
    rw [value_top]
    exact hTop
  · have hOld : C.mountain.height s < u := by omega
    have hNew : C.toRowMountain.height (C.coordinates.parentCopy b s) < C.rowCopy b s u := by
      change C.height _ < C.rowCopy b s u
      rw [C.height_parentCopy hs b]
      by_cases hCone : C.InCone s
      · rw [if_pos hCone, rowCopy, if_pos ⟨hCone, by have := hCone.1; omega⟩]
        omega
      · rw [if_neg hCone, C.rowCopy_outside hCone]
        exact hOld
    rw [value_absent C.mountain oldTop hOld, value_absent C.toRowMountain newTop hNew]

theorem value_tail_eq_of_no_parent_outside (C : Context) (oldTop newTop : Nat → Nat)
    {s r : Nat} (hs : s ≤ C.coordinates.x) (hOut : ¬ C.InCone s)
    (hn : (C.mountain.row r).parent s = none) (b : Nat)
    (hTop : oldTop s = newTop (C.coordinates.parentCopy b s)) :
    ∀ u, r ≤ u → value C.mountain oldTop u s =
      value C.toRowMountain newTop u (C.coordinates.parentCopy b s) := by
  intro u hu
  have hHeight := (C.mountain.parent_none_iff r s).mp hn
  have ht := C.value_top_tail_eq oldTop newTop hs b hTop u (by omega)
  rw [C.rowCopy_outside hOut] at ht
  exact ht

/-- Every copied root still reaches the original root in low rows, possibly
through several earlier seams. Block zero is the reflexive case. -/
theorem root_path_copy_low (C : Context) {r : Nat} (hr : r < C.floor) (b : Nat) :
    (C.row r).Ancestor C.coordinates.y (C.coordinates.y+b*C.coordinates.length) ∨
      C.coordinates.y = C.coordinates.y+b*C.coordinates.length := by
  induction b with
  | zero => exact Or.inr (by simp)
  | succ b ih =>
      rw [C.root_copy_succ_eq]
      have ht := C.low_ancestor_same_block hr (C.root_ancestor_last_low hr)
        (Nat.le_refl _) (Nat.le_refl _) b
      rcases ih with ha | he
      · exact Or.inl (ha.trans ht)
      · rw [← he] at ht
        exact Or.inl ht

/-- The special blocker `z=y` must remain at the original root. This theorem
supplies its new path from the transported candidate; it does not pretend
that the outgoing edge of the copied root equals the old root edge. -/
theorem zero_root_path_copy_low (C : Context) {r q : Nat}
    (hr : r < C.floor) (hq : q ≤ C.coordinates.x) (b : Nat)
    (hPath : C.coordinates.y = q ∨ (C.mountain.row r).Ancestor C.coordinates.y q) :
    C.coordinates.y = C.coordinates.parentCopy b q ∨
      (C.row r).Ancestor C.coordinates.y (C.coordinates.parentCopy b q) := by
  rcases hPath with he | ha
  · rw [← he, C.coordinates.parentCopy_bad b (Nat.le_refl _)]
    exact (C.root_path_copy_low hr b).symm
  · have hLeft := ha.lt
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hLeft)]
    have ht := C.low_ancestor_same_block hr ha (Nat.le_refl _) hq b
    rcases C.root_path_copy_low hr b with hRoot | he
    · exact Or.inr (hRoot.trans ht)
    · rw [← he] at ht
      exact Or.inr ht

#print axioms parent_rowCopy
#print axioms value_row_antitone
#print axioms value_copy_dominance
#print axioms value_copy_dominance_numeric
#print axioms value_good_eq
#print axioms value_tail_eq_of_good_parent
#print axioms old_top_strictly_increases_in_cone
#print axioms value_top_tail_eq
#print axioms value_tail_eq_of_no_parent_outside
#print axioms extracted_parent_good_of_row_parent_good
#print axioms zero_root_path_copy_low

end OneY.LowerCopy.Context
