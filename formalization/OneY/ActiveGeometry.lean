import OneY.TopForestGeometry
import OneY.BadRoot
import OneY.LowerCopy

/-!
# Every layer below an active parent edge supplies a lower-copy context

Finite-row parent edges refine their layer's base forest, and actual
extraction refines the preceding base forest. Consequently an active
ancestor remains an ancestor in every intervening extracted layer. The
proved extraction geometry then supplies both the strict height rise and
the computed component-root equation required by the copy construction.
-/

namespace OneY.RootGeometry.RowMountain

theorem topForest_refines_row_zero (M : RowMountain) :
    M.topForest.Refines (M.row 0) := by
  intro c p hp
  have hroot := M.topForest_parent_root hp
  have hpath := (M.rootAt_eq_iff_path (r := M.height p) (q := p) (c := c) rfl).mp hroot
  rcases hpath with ha | heq
  · exact ParentForest.Refines.ancestor (M.refines_le (Nat.zero_le _)) ha
  · have hh := M.topForest_parent_height hp
    rw [heq] at hh
    omega

end OneY.RootGeometry.RowMountain

namespace OneY.Numeric

theorem rawExtract_refines_base (base : Row) (hpos : ∀ c, 0 < base.value c) :
    (rawExtract base hpos).forest.Refines base.forest := by
  intro c p hp
  exact ParentForest.Refines.trans (rawExtract_refines_topForest base hpos)
    (mountain base hpos).topForest_refines_row_zero hp

theorem rows_refines_base (base : Row) (hpos : ∀ c, 0 < base.value c) (r : Nat) :
    (rows base r).forest.Refines base.forest := by
  intro c p hp
  exact (mountain base hpos).refines_le (Nat.zero_le r) hp

theorem layers_succ_refines (a : RootedRow) (k : Nat) :
    (layers a (k+1)).row.forest.Refines (layers a k).row.forest := by
  intro c p hp
  exact rawExtract_refines_base (layers a k).row (layers a k).positive hp

theorem layers_refines (a : RootedRow) {k K : Nat} (hk : k ≤ K) :
    (layers a K).row.forest.Refines (layers a k).row.forest := by
  induction hk with
  | refl => exact ParentForest.refines_refl _
  | @step K _ ih =>
      intro c p hp
      exact ParentForest.Refines.trans (layers_succ_refines a K) ih hp

theorem active_parent_layer_ancestor (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k ≤ K) :
    (layers a k).row.forest.Ancestor y x := by
  have ha := rows_refines_base (layers a K).row (layers a K).positive d hp
  exact ParentForest.Refines.ancestor (layers_refines a hk) ha

theorem active_parent_lower_root (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k < K) :
    height (layers a k).row y < height (layers a k).row x ∧
      (rows (layers a k).row (height (layers a k).row y)).forest.root x = y := by
  have ha := active_parent_layer_ancestor a hp (by omega : k+1 ≤ K)
  exact rawExtract_ancestor_rootAt (layers a k).row (layers a k).positive ha

theorem active_parent_lower_vertex (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k < K) :
    Geometry.Reach (geometry (layers a k).row (layers a k).positive) y
      (height (layers a k).row x) x := by
  have ha := active_parent_layer_ancestor a hp (by omega : k+1 ≤ K)
  exact rawExtract_ancestor_vertex (layers a k).row (layers a k).positive ha

/-- This context is built from a concrete active parent edge; its root
and height conditions are proved, rather than supplied as assumptions. -/
def activeLowerContext (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k < K) :
    LowerCopy.Context where
  mountain := mountain (layers a k).row (layers a k).positive
  coordinates := ⟨y, x, (rows (layers a K).row d).forest.parent_left hp⟩
  last_root := (active_parent_lower_root a hp hk).2
  last_higher := (active_parent_lower_root a hp hk).1

def badAtLowerContext (a : RootedRow) {K d x y k : Nat}
    (hbad : BadAt a K d x y) (hk : k < K) : LowerCopy.Context :=
  activeLowerContext a hbad.1 hk

theorem activeLowerContext_floor (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k < K) :
    (activeLowerContext a hp hk).floor = height (layers a k).row y := rfl

theorem activeLowerContext_rise (a : RootedRow) {K d x y k : Nat}
    (hp : (rows (layers a K).row d).forest.parent x = some y) (hk : k < K) :
    (activeLowerContext a hp hk).rise =
      height (layers a k).row x - height (layers a k).row y := rfl

end OneY.Numeric

#print axioms OneY.Numeric.rawExtract_refines_base
#print axioms OneY.Numeric.active_parent_lower_root
#print axioms OneY.Numeric.activeLowerContext
#print axioms OneY.Numeric.badAtLowerContext
