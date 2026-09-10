import OneY.NumericDecoratedFrame
import OneY.TerminalCopyCanonical

/-! # Recovering every nonempty parent in the active copied mountain

The only numerical induction inputs are the already recovered higher rows
and strict left prefix of the current row.  The specified parent being
nonempty is an explicit case distinction, not a canonicality assumption.
-/

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS LowerCopy.Context

theorem badAtTerminal_restrictedParent_some_bounded (a : RootedRow)
    {K d x y cap index r c p : Nat} (hbad : BadAt a K d x y)
    (hcap : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap)
    (hc : c < ((matrix (layers a K).row (x+1) cap).expand index).raw.length)
    (hHigher : ∀ u, r+1 ≤ u → ∀ q,
      restrictedParent ((badAtTerminalContext a hbad).row u)
        (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
          ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
          (u+1)) q = (badAtTerminalContext a hbad).parent (u+1) q)
    (hPrefix : ∀ q, q < c →
      restrictedParent ((badAtTerminalContext a hbad).row r)
        (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
          ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
          (r+1)) q = (badAtTerminalContext a hbad).parent (r+1) q)
    (hP : (badAtTerminalContext a hbad).parent (r+1) c = some p) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) c = some p := by
  let C := badAtTerminalContext a hbad
  let M := C.toRowMountain
  let top := C.ordinaryContext.copyValue (topValue (layers a K).row)
  let A := ((matrix (layers a K).row (x+1) cap).expand index).raw
  have hcA : c < A.length := hc
  have hTop : ∀ q, 0 < top q := fun q => topValue_pos (layers a K).row
    ((layers a K).positive (C.ordinaryContext.source0 q))
  have hAnc : (C.row r).Ancestor p c := M.nested_succ r hP
  obtain ⟨q, hQ⟩ := M.parent_exists r c (by have := M.parent_source hP; omega)
  by_cases hDirect : p = q
  · subst q
    exact restrictedParent_eq_of_direct_parent
      (Reconstruction.numericRow M top hTop (r+1)) (C.row r) hP hQ
  by_cases hHigh : d ≤ r
  · exact (badAtTerminal_restrictedParent_above a hbad hHigh c).trans hP
  have hS := badAt_expanded_decorated_rowS (index := index) a hbad hcap
    (by omega : r+1 ≤ d)
  have hQmat : previousParent A ((x+1)+1+(r+1)) c = some q := by
    change parent ((x+1)+1+(r+1)-1) A c = some q
    have he : (x+1)+1+(r+1)-1 = (x+1)+1+r := by omega
    rw [he, expanded_parent a hbad hcap hc r]
    exact hQ
  have hPmat : parent ((x+1)+1+(r+1)) A c = some p := by
    rw [expanded_parent a hbad hcap hc (r+1)]
    exact hP
  obtain ⟨z, hZ, hZP, hKey⟩ := hS c q p hc hQmat hPmat hDirect
  have hqlt : q < c := (C.row r).parent_left hQ
  have hzq : z ≤ q := by
    rcases hZ with he | ha
    · omega
    · have haz := (Forest.ancestorChain_contains_iff (fun h => parent_some_lt h)).mp ha
      have := Forest.ancestor_lt (fun h => parent_some_lt h) haz
      omega
  have hz : z < A.length := by omega
  have hZactual : z = q ∨ (C.row (r+1)).Ancestor z q := by
    rcases hZ with he | ha
    · exact Or.inl he
    · apply Or.inr
      apply ParentForest.ancestor_of_zeroY
      exact Forest.ancestor_transfer_prefix (fun h => parent_some_lt h)
        (by omega : q < A.length)
        (fun i hi => expanded_parent a hbad hcap hi (r+1))
        ((Forest.ancestorChain_contains_iff (fun h => parent_some_lt h)).mp ha)
  have hZParent : (C.row (r+1)).parent z = some p := by
    rw [expanded_parent a hbad hcap hz (r+1)] at hZP
    exact hZP
  have hGeom : KeyLEFrom M top (r+2) c z := by
    have he : (x+1)+1+(r+1)+1 = (x+1)+1+(r+2) := by omega
    rw [he] at hKey
    apply (DecoratedColumn.keyLEFrom_iff_columns M top A ((x+1)+1) (r+2) c z
      (fun u => expanded_entry a hbad hcap hc u)
      (fun u => expanded_entry a hbad hcap hz u)).mpr
    exact hKey
  have hNext : Reconstruction.value M top (r+2) c ≤ Reconstruction.value M top (r+2) z :=
    (Reconstruction.keyLEFrom_iff_value_le M top hTop (r+1) hHigher
      (M.parent_source hP) (M.parent_source hZParent) (hP.trans hZParent.symm)).mp hGeom
  have hUpper : Reconstruction.value M top (r+1) c ≤ Reconstruction.value M top (r+1) z := by
    rw [Reconstruction.value_recurrence M top hP,
      Reconstruction.value_recurrence M top hZParent]
    simpa only [Nat.add_assoc] using Nat.add_le_add_right hNext (Reconstruction.value M top (r+1) p)
  exact restrictedParent_eq_of_blocker (Reconstruction.numericRow M top hTop (r+1))
    (C.row r) hQ hP hAnc hPrefix hZactual hZParent hUpper

theorem badAtTerminal_restrictedParent_some (a : RootedRow)
    {K d x y r c p : Nat} (hbad : BadAt a K d x y)
    (hHigher : ∀ u, r+1 ≤ u → ∀ q,
      restrictedParent ((badAtTerminalContext a hbad).row u)
        (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
          ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
          (u+1)) q = (badAtTerminalContext a hbad).parent (u+1) q)
    (hPrefix : ∀ q, q < c →
      restrictedParent ((badAtTerminalContext a hbad).row r)
        (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
          ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
          (r+1)) q = (badAtTerminalContext a hbad).parent (r+1) q)
    (hP : (badAtTerminalContext a hbad).parent (r+1) c = some p) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) c = some p := by
  obtain ⟨cap, hcap⟩ := exists_value_cap (layers a K).row.value x
  have hcap' : ∀ q, q < x+1 → (layers a K).row.value q ≤ cap := fun q hq => hcap q (by omega)
  let E := badAtContext a hbad (hcap x (Nat.le_refl _))
  have hc : c < ((matrix (layers a K).row (x+1) cap).expand (c+1)).raw.length := by
    rw [E.length_expand]
    change c < y+(c+1+1)*(x-y)
    have hxy : y < x := (badAtTerminalContext a hbad).coordinates.root_lt_last
    have hm := Nat.mul_le_mul_left (c+1+1) (by omega : 1 ≤ x-y)
    simp only [Nat.mul_one] at hm
    omega
  exact badAtTerminal_restrictedParent_some_bounded a hbad hcap' hc hHigher hPrefix hP

end OneY.NumericFrame

#print axioms OneY.NumericFrame.badAtTerminal_restrictedParent_some_bounded
#print axioms OneY.NumericFrame.badAtTerminal_restrictedParent_some
