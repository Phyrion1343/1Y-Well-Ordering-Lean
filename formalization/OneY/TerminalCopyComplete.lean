import OneY.TerminalDecoratedRecovery
import OneY.TerminalCopyTopBound

/-! # Unconditional canonical reconstruction of the active finite layer

Downward induction on the row and left-to-right induction on the column
remove every local comparison hypothesis. The only input is the actual
numerical bad root of the original iterated extraction layer.
-/

namespace OneY.Numeric

theorem badAtTerminal_restrictedParent (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (r c : Nat) :
    restrictedParent ((badAtTerminalContext a hbad).row r)
      (Reconstruction.value (badAtTerminalContext a hbad).toRowMountain
        ((badAtTerminalContext a hbad).ordinaryContext.copyValue (topValue (layers a K).row))
        (r+1)) c = (badAtTerminalContext a hbad).parent (r+1) c := by
  let C := badAtTerminalContext a hbad
  let M := C.toRowMountain
  let top := C.ordinaryContext.copyValue (topValue (layers a K).row)
  have hTop : ∀ q, 0 < top q := fun q => topValue_pos (layers a K).row
    ((layers a K).positive (C.ordinaryContext.source0 q))
  have hBound : Reconstruction.PseudoTopBound M top := badAtTerminal_pseudoTopBound a hbad
  have main : ∀ n u, d ≤ u+n → ∀ q,
      restrictedParent (C.row u) (Reconstruction.value M top (u+1)) q = C.parent (u+1) q := by
    intro n
    induction n with
    | zero =>
        intro u hu q
        exact badAtTerminal_restrictedParent_above a hbad (by omega) q
    | succ n ih =>
        intro u hu
        by_cases hHigh : d ≤ u
        · exact fun q => badAtTerminal_restrictedParent_above a hbad hHigh q
        have hHigher : ∀ v, u+1 ≤ v → ∀ q,
            restrictedParent (C.row v) (Reconstruction.value M top (v+1)) q = C.parent (v+1) q := by
          intro v hv q
          exact ih v (by omega) q
        intro q
        induction q using Nat.strongRecOn with
        | ind q hPrefix =>
            cases hp : C.parent (u+1) q with
            | some p =>
                exact NumericFrame.badAtTerminal_restrictedParent_some a hbad hHigher hPrefix hp
            | none =>
                have hh : M.height q ≤ u+1 := (M.parent_none_iff (u+1) q).mp hp
                by_cases hTopCell : M.height q = u+1
                · exact Reconstruction.restrictedParent_top_none M top hTop hBound hTopCell hPrefix
                · have hZero : Reconstruction.value M top (u+1) q = 0 :=
                    Reconstruction.value_absent M top (by omega)
                  apply (restrictedParent_none_iff (C.row u) (Reconstruction.value M top (u+1)) q).mpr
                  intro p _ _
                  rw [hZero]
                  exact Nat.zero_le _
  exact main d r (by omega) c

end OneY.Numeric

#print axioms OneY.Numeric.badAtTerminal_restrictedParent
