import OneY.NumericFrameBlocker
import OneY.TerminalCopyNumeric
import ZeroY.Expansion.Context

/-!
# The actual active site in the framed sparse-depth matrix

The matrix's maximal-parent-row search selects the finite active row with
the framing offset. Its bad root and final column are the numerical ones.
Consequently the existing BM4 expansion theorems apply to this concrete
matrix, not to an existential or assumed encoding.
-/

namespace OneY.NumericFrame

open Numeric ZeroY YesMetaZFC.BMS

theorem maximalParentRow_eq (base : Row) (hpos : ∀ c, 0 < base.value c)
    {d x y cap : Nat} (hp : (rows base d).forest.parent x = some y)
    (hx : height base x = d+1) (hcap : base.value x ≤ cap) :
    maximalParentRow (matrix base (x+1) cap).raw = some ((x+1)+1+d) := by
  have hparent : parent ((x+1)+1+d) (matrix base (x+1) cap).raw x = some y := by
    rw [matrix_numeric_parent_all base hcap (Nat.lt_succ_self x) d]
    exact hp
  unfold maximalParentRow
  rw [matrix_length]
  apply greatestBelow?_eq_some_iff.mpr
  refine ⟨parent_some_row_lt_column_height hparent, ?_, ?_⟩
  · rw [hparent]
    rfl
  · intro r hr hsome
    by_cases hle : r ≤ (x+1)+1+d
    · exact hle
    · have hrlarge : (x+1)+1+d < r := by omega
      have he : (x+1)+1+(r-((x+1)+1)) = r := by omega
      have hhigh : height base x ≤ r-((x+1)+1) := by omega
      have hn : (rows base (r-((x+1)+1))).forest.parent x = none := by
        cases hpp : (rows base (r-((x+1)+1))).forest.parent x with
        | none => rfl
        | some p =>
            have hh := (parent_exists_iff_lt_height base (hpos x) _).mp ⟨p, hpp⟩
            omega
      have hout := matrix_numeric_parent_all base hcap (Nat.lt_succ_self x) (r-((x+1)+1))
      rw [he, hn] at hout
      rw [hout] at hsome
      cases hsome

def terminalContext (base : Row) (hpos : ∀ c, 0 < base.value c)
    {d x y cap : Nat} (hp : (rows base d).forest.parent x = some y)
    (hx : height base x = d+1) (hcap : base.value x ≤ cap) :
    ExpansionContext (matrix base (x+1) cap) where
  lastIndex := x
  maximalRow := (x+1)+1+d
  parentColumn := y
  array_length := matrix_length _ _ _
  maximal_row_eq := maximalParentRow_eq base hpos hp hx hcap
  parent_eq := (matrix_numeric_parent_all base hcap (Nat.lt_succ_self x) d).trans hp

def badAtContext (a : RootedRow) {K d x y cap : Nat} (hbad : BadAt a K d x y)
    (hcap : (layers a K).row.value x ≤ cap) :
    ExpansionContext (matrix (layers a K).row (x+1) cap) :=
  terminalContext (layers a K).row (layers a K).positive hbad.1
    (badAt_height_and_top hbad).1 hcap

theorem expanded_relative_structure (base : Row) (width cap index : Nat)
    (hcap : ∀ c, c < width → base.value c ≤ cap) :
    DepthRegular ((matrix base width cap).expand index).raw ∧
      RelativeBlocker.AboveS ((matrix base width cap).expand index).raw (width+1) :=
  RelativeBlocker.relative_structural_expand (width+1) index
    ⟨matrix_depthRegular base width cap, matrix_aboveS base width cap hcap⟩

end OneY.NumericFrame

#print axioms OneY.NumericFrame.maximalParentRow_eq
#print axioms OneY.NumericFrame.badAtContext
#print axioms OneY.NumericFrame.expanded_relative_structure
