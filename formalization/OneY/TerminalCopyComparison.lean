import OneY.TerminalFrameDepths
import OneY.DecoratedColumn
import OneY.LowerCopyComparison

/-! # Full depth-suffix and top-value comparison in actual terminal copies -/

namespace OneY.DecoratedColumn

open ZeroY YesMetaZFC.BMS LowerCopy.Context

theorem keyLEFrom_iff_columns (M : RootGeometry.RowMountain) (top : Nat → Nat)
    (array : Matrix) (offset start c z : Nat)
    (hc : ∀ r, matrixEntry array c (offset+r) = (M.row r).depth c)
    (hz : ∀ r, matrixEntry array z (offset+r) = (M.row r).depth z) :
    KeyLEFrom M top start c z ↔
      LE (columnSuffix array c (offset+start)) (top c)
        (columnSuffix array z (offset+start)) (top z) := by
  have hent (i : Nat) :
      columnEntry (columnSuffix array c (offset+start)) i = (M.row (start+i)).depth c ∧
      columnEntry (columnSuffix array z (offset+start)) i = (M.row (start+i)).depth z := by
    simp only [columnEntry_suffix]
    have he : offset+start+i = offset+(start+i) := by omega
    rw [he, hc, hz]
    exact ⟨rfl, rfl⟩
  have heq : DepthsEqualFrom M start c z ↔
      ColumnEq (columnSuffix array c (offset+start)) (columnSuffix array z (offset+start)) := by
    constructor
    · intro h i
      rw [(hent i).1, (hent i).2]
      exact h _ (by omega)
    · intro h r hr
      have ht := h (r-start)
      rw [(hent _).1, (hent _).2] at ht
      have he : start+(r-start) = r := by omega
      rwa [he] at ht
  have hlt : DepthsLTFrom M start c z ↔
      ColumnLt (columnSuffix array c (offset+start)) (columnSuffix array z (offset+start)) := by
    constructor
    · rintro ⟨r, hr, hbefore, hdiff⟩
      refine ⟨r-start, ?_, ?_⟩
      · intro i hi
        rw [(hent i).1, (hent i).2]
        exact hbefore _ (by omega) (by omega)
      · rw [(hent _).1, (hent _).2]
        have he : start+(r-start) = r := by omega
        rwa [he]
    · rintro ⟨i, hbefore, hdiff⟩
      refine ⟨start+i, by omega, ?_, ?_⟩
      · intro r hr hri
        have ht := hbefore (r-start) (by omega)
        rw [(hent _).1, (hent _).2] at ht
        have he : start+(r-start) = r := by omega
        rwa [he] at ht
      · rwa [(hent _).1, (hent _).2] at hdiff
  simp only [KeyLEFrom, LE, heq, hlt]

end OneY.DecoratedColumn

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS LowerCopy.Context

theorem copied_keyLE (a : RootedRow) {K d x y cap c z u : Nat}
    (hbad : BadAt a K d x y)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hc : y < c) (hcx : c < x) (hz : y < z) (hzx : z < x)
    (hparent : (rows (layers a K).row u).forest.parent c =
      (rows (layers a K).row u).forest.parent z)
    (hkey : KeyLEFrom (badAtTerminalContext a hbad).mountain (topValue (layers a K).row) (u+1) c z)
    (b : Nat) :
    KeyLEFrom (badAtTerminalContext a hbad).toRowMountain
      ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row)) (u+1)
      ((badAtTerminalContext a hbad).coordinates.parentCopy b c)
      ((badAtTerminalContext a hbad).coordinates.parentCopy b z) := by
  let C := badAtTerminalContext a hbad
  let E := badAtContext a hbad (hcap x (Nat.lt_succ_self x))
  let A := matrix (layers a K).row (x+1) cap
  have hcopy (q : Nat) : BMS.copyColumn E b q = C.coordinates.parentCopy b q := rfl
  have hbound (q : Nat) (hyq : y < q) (hqx : q < x) :
      C.coordinates.parentCopy b q < (A.expand b).raw.length := by
    rw [← hcopy q, BMS.copyColumn_bad E b (by change y ≤ q; omega)]
    exact E.copyPosition_lt_length (Nat.le_refl b)
      (by change q-y < x-y; omega)
  have hnewc := hbound c hc hcx
  have hnewz := hbound z hz hzx
  apply (DecoratedColumn.keyLEFrom_iff_columns C.toRowMountain
    (C.ordinaryContext.copyValue (topValue (layers a K).row)) (A.expand b).raw
    ((x+1)+1) (u+1) (C.coordinates.parentCopy b c) (C.coordinates.parentCopy b z)
    (fun r => expanded_entry a hbad hcap hnewc r)
    (fun r => expanded_entry a hbad hcap hnewz r)).mpr
  have htcopy (q : Nat) (hq : q < x) :
      C.ordinaryContext.copyValue (topValue (layers a K).row) (C.coordinates.parentCopy b q) =
        topValue (layers a K).row q :=
    C.ordinaryContext.copyValue_parentCopy _ hq b
  rw [htcopy c hcx, htcopy z hzx, ← hcopy c, ← hcopy z]
  apply DecoratedColumn.copied_le E (matrix_depthRegular _ _ _)
    (Nat.le_refl b) hcx hzx hc hz
  · have he : (x+1)+1+(u+1) = ((x+1)+1+u)+1 := by omega
    rw [he]
    change parent ((x+1)+1+u) A.raw c = parent ((x+1)+1+u) A.raw z
    rw [matrix_numeric_parent_all (layers a K).row (hcap c (by omega)) (by omega) u,
      matrix_numeric_parent_all (layers a K).row (hcap z (by omega)) (by omega) u]
    exact hparent
  · apply (DecoratedColumn.keyLEFrom_iff_columns C.mountain (topValue (layers a K).row)
      A.raw ((x+1)+1) (u+1) c z
      (fun r => original_entry a hbad hcap (by omega) r)
      (fun r => original_entry a hbad hcap (by omega) r)).mp
    exact hkey

end OneY.NumericFrame

#print axioms OneY.DecoratedColumn.keyLEFrom_iff_columns
#print axioms OneY.NumericFrame.copied_keyLE
