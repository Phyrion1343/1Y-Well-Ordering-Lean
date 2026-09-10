import OneY.OrdinaryCopyForest
import OneY.OrdinaryCopyPseudo
import OneY.Extraction

/-!
# Actual extraction commutes with ordinary copies

The numerical rebuilding theorem identifies the copied mountain, its
computed pseudo-parent map copies the original map, and nearest-smaller
selection respects that transported candidate forest. Consequently the
base forest of the next extraction layer is obtained by ordinary copying.
-/

namespace OneY.ParentForest

theorem ext_parent {F G : ParentForest} (hp : F.parent = G.parent) : F = G := by
  cases F
  cases G
  cases hp
  rfl

end OneY.ParentForest

namespace OneY.RootGeometry.RowMountain

theorem ext_height_parents {M N : RowMountain} (hh : M.height = N.height)
    (hp : ∀ r, (M.row r).parent = (N.row r).parent) : M = N := by
  have hrows : M.row = N.row := by
    funext r
    exact ParentForest.ext_parent (hp r)
  cases M
  cases N
  dsimp only at hh hrows
  cases hh
  cases hrows
  rfl

end OneY.RootGeometry.RowMountain

namespace OneY.Numeric

theorem ordinaryCopy_mountain (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) :
    mountain (ordinaryCopiedBase base hpos coordinates)
      (ordinaryCopiedBase_positive base hpos coordinates) =
        (ordinaryCopyContext base hpos coordinates).toRowMountain := by
  apply RootGeometry.RowMountain.ext_height_parents
  · funext c
    exact ordinaryCopy_height base hpos coordinates c
  · intro r
    funext c
    exact ordinaryCopy_rows_parent base hpos coordinates r c

theorem ordinaryCopy_rawExtract_parent (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (c : Nat) :
    (rawExtract (ordinaryCopiedBase base hpos coordinates)
      (ordinaryCopiedBase_positive base hpos coordinates)).forest.parent c =
        (ordinaryCopiedBase (rawExtract base hpos) (rawExtract_positive base hpos)
          coordinates).forest.parent c := by
  let C := ordinaryCopyContext base hpos coordinates
  have hm := ordinaryCopy_mountain base hpos coordinates
  have ht : topValue (ordinaryCopiedBase base hpos coordinates) = C.copyValue (topValue base) := by
    funext q
    exact ordinaryCopy_topValue base hpos coordinates q
  have hq : C.CopiesForest (Pseudo.forest C.mountain) (Pseudo.forest C.toRowMountain) := by
    intro q
    exact C.pseudo_parent_formula q
  change restrictedParent
    (Pseudo.forest (mountain (ordinaryCopiedBase base hpos coordinates)
      (ordinaryCopiedBase_positive base hpos coordinates)))
    (topValue (ordinaryCopiedBase base hpos coordinates)) c = _
  rw [hm, ht, C.restrictedParent_of_forest_copy hq]
  rfl

theorem ordinaryCopy_rawExtract (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) :
    rawExtract (ordinaryCopiedBase base hpos coordinates)
      (ordinaryCopiedBase_positive base hpos coordinates) =
        ordinaryCopiedBase (rawExtract base hpos) (rawExtract_positive base hpos)
          coordinates := by
  apply Row.ext_values_parents
  · funext c
    exact ordinaryCopy_topValue base hpos coordinates c
  · funext c
    exact ordinaryCopy_rawExtract_parent base hpos coordinates c

theorem ordinaryCopy_extract (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) :
    extract (ordinaryCopiedBase base hpos coordinates)
      (ordinaryCopiedBase_positive base hpos coordinates) =
        ordinaryCopiedBase (extract base hpos) (extract_positive base hpos)
          coordinates :=
  ordinaryCopy_rawExtract base hpos coordinates

end OneY.Numeric

#print axioms OneY.Numeric.ordinaryCopy_mountain
#print axioms OneY.Numeric.ordinaryCopy_rawExtract
#print axioms OneY.Numeric.ordinaryCopy_extract
