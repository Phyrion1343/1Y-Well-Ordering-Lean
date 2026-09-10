import OneY.TerminalFrame
import OneY.TerminalCopyReconstruction

/-!
# Actual BM4 expanded parents equal the specified terminal copy graph

The equality covers every finite row and every retained copied block.
It is a graph theorem; the copied top values are not decoded in this module.
-/

namespace OneY.TerminalCopy.Context

theorem parent_parentCopy_nonroot (C : Context) {s : Nat}
    (hs : s < C.coordinates.x) (hny : s ≠ C.coordinates.y) (b r : Nat) :
    C.parent r (C.coordinates.parentCopy b s) =
      ((C.mountain.row r).parent s).map (C.coordinates.parentCopy b) := by
  by_cases hg : s < C.coordinates.y
  · rw [C.coordinates.parentCopy_good b hg, C.parent_original hs r]
    cases hp : (C.mountain.row r).parent s with
    | none => rfl
    | some p =>
        have hps := (C.mountain.row r).parent_left hp
        simp only [Option.map_some, C.coordinates.parentCopy_good b (by omega : p < C.coordinates.y)]
  · have hy : C.coordinates.y < s := by omega
    rw [C.coordinates.parentCopy_bad b (Nat.le_of_lt hy)]
    change C.parent r (C.coordinates.encode s b) = _
    rw [C.parent_encode hy (Nat.le_of_lt hs) b r, if_neg (by intro h; omega)]

end OneY.TerminalCopy.Context

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS

theorem badAt_copyColumn_eq (a : RootedRow) {K d x y cap : Nat}
    (hbad : BadAt a K d x y) (hcap : (layers a K).row.value x ≤ cap) (b c : Nat) :
    BMS.copyColumn (badAtContext a hbad hcap) b c =
      (badAtTerminalContext a hbad).coordinates.parentCopy b c := rfl

theorem expanded_parent_parentCopy (a : RootedRow) {K d x y cap index b s : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ c, c < x+1 → (layers a K).row.value c ≤ cap)
    (hb : b ≤ index) (hs : s < x) (r : Nat) :
    parent ((x+1)+1+r) ((matrix (layers a K).row (x+1) cap).expand index).raw
      ((badAtTerminalContext a hbad).coordinates.parentCopy b s) =
        (badAtTerminalContext a hbad).parent r
          ((badAtTerminalContext a hbad).coordinates.parentCopy b s) := by
  let C := badAtTerminalContext a hbad
  let E := badAtContext a hbad (hcap x (Nat.lt_succ_self x))
  have hcopy (j q : Nat) : BMS.copyColumn E j q = C.coordinates.parentCopy j q := rfl
  have hold (u q : Nat) (hq : q < x+1) :
      parent ((x+1)+1+u) (matrix (layers a K).row (x+1) cap).raw q =
        (C.mountain.row u).parent q :=
    matrix_numeric_parent_all (layers a K).row (hcap q hq) hq u
  change parent ((x+1)+1+r) ((matrix (layers a K).row (x+1) cap).expand index).raw
    (C.coordinates.parentCopy b s) = C.parent r (C.coordinates.parentCopy b s)
  by_cases hny : s ≠ y
  · rw [C.parent_parentCopy_nonroot hs hny b r, ← hcopy]
    rw [BMS.parent_copyColumn_nonroot E hb hs hny ((x+1)+1+r), hold r s (by omega)]
    rfl
  · have he : s = y := by omega
    subst s
    rw [C.coordinates.parentCopy_bad b (by change y ≤ y; omega : C.coordinates.y ≤ y)]
    have hpos : E.copyPosition b 0 = y+b*(x-y) := by
      simp [ExpansionContext.copyPosition, ExpansionContext.copyStart, ExpansionContext.blockLength,
        E, badAtContext, terminalContext]
    change parent ((x+1)+1+r) ((matrix (layers a K).row (x+1) cap).expand index).raw
      (y+b*(x-y)) = C.parent r (y+b*(x-y))
    rw [← hpos]
    by_cases hr : d ≤ r
    · rw [BMS.parent_copied_root_high_of_le E hb
        (by change (x+1)+1+d ≤ (x+1)+1+r; omega), hpos]
      change parent ((x+1)+1+r) (matrix (layers a K).row (x+1) cap).raw y =
        C.parent r (C.coordinates.y+b*C.coordinates.length)
      rw [C.parent_root_copy_high hr b]
      exact hold r y (by have := C.coordinates.root_lt_last; change y < x at this; omega)
    · cases b with
      | zero =>
          simp only [Nat.zero_mul, Nat.add_zero] at hpos ⊢
          rw [hpos, BMS.parent_expand_prefix E index ((x+1)+1+r) (show y < E.lastIndex from hs),
            C.parent_original (show y < C.coordinates.x from hs) r]
          exact hold r y (by have := C.coordinates.root_lt_last; change y < x at this; omega)
      | succ b =>
          rw [BMS.parent_copied_root_low_of_le E hb (by omega)
            (by change (x+1)+1+r < (x+1)+1+d; omega)]
          change (parent ((x+1)+1+r) (matrix (layers a K).row (x+1) cap).raw x).map
            (BMS.copyColumn E (b+1-1)) = C.parent r (E.copyPosition (b+1) 0)
          rw [hold r x (Nat.lt_succ_self x), hpos]
          simp only [Nat.add_sub_cancel]
          have heq := C.root_copy_succ_eq b
          change y+(b+1)*(x-y) = x+b*(x-y) at heq
          rw [heq]
          exact (badAtTerminal_seam_parent_below a hbad (by omega : r < d) b).symm

theorem expanded_parent (a : RootedRow) {K d x y cap index c : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hc : c < ((matrix (layers a K).row (x+1) cap).expand index).raw.length) (r : Nat) :
    parent ((x+1)+1+r) ((matrix (layers a K).row (x+1) cap).expand index).raw c =
      (badAtTerminalContext a hbad).parent r c := by
  let C := badAtTerminalContext a hbad
  let E := badAtContext a hbad (hcap x (Nat.lt_succ_self x))
  by_cases hgood : c < y
  · have hcx : c < x := by have := C.coordinates.root_lt_last; change y < x at this; omega
    rw [BMS.parent_expand_prefix E index ((x+1)+1+r) hcx,
      matrix_numeric_parent_all (layers a K).row (hcap c (by omega)) (by omega) r]
    exact (C.parent_original hcx r).symm
  · obtain ⟨b, q, hb, hq, he⟩ := E.exists_copyPosition_of_not_good hc (by change y ≤ c; omega)
    have hsource : y+q < x := by
      change q < x-y at hq
      have := C.coordinates.root_lt_last
      change y < x at this
      omega
    have hcoord : C.coordinates.parentCopy b (y+q) = c := by
      rw [C.coordinates.parentCopy_bad b (by change y ≤ y+q; omega)]
      change y+q+b*(x-y) = c
      change c = y+b*(x-y)+q at he
      omega
    have h := expanded_parent_parentCopy a hbad hcap hb hsource r
    rw [hcoord] at h
    exact h

end OneY.NumericFrame

#print axioms OneY.NumericFrame.expanded_parent_parentCopy
#print axioms OneY.NumericFrame.expanded_parent
