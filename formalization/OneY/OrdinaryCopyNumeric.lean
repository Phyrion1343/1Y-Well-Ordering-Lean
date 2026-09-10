import OneY.OrdinaryCopySelection

/-!
# Rebuilding ordinary copies by the actual numerical row algorithm

Both the differences and the nearest-smaller searches commute with copying.
The copied base therefore rebuilds exactly the specified ordinary-copy
mountain, including its computed heights and its top values.
-/

namespace OneY.Numeric

theorem Row.ext_values_parents {a b : Row} (hv : a.value = b.value)
    (hp : a.forest.parent = b.forest.parent) : a = b := by
  cases a with
  | mk va fa ha =>
      cases b with
      | mk vb fb hb =>
          cases fa with
          | mk pa hpa =>
              cases fb with
              | mk pb hpb =>
                  dsimp only at hv hp
                  cases hv
                  cases hp
                  rfl

def ordinaryCopyRow (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r : Nat) : Row where
  value := (ordinaryCopyContext base hpos coordinates).copyValue (rows base r).value
  forest := (ordinaryCopyContext base hpos coordinates).row r
  parent_values := by
    intro c p hp
    let C := ordinaryCopyContext base hpos coordinates
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
    have hleft := (C.mountain.row r).parent_left hq
    change q < C.source0 c at hleft
    have hs := C.source0_bounds c
    rw [← heq, C.copyValue_parentCopy (rows base r).value (by omega : q < C.coordinates.x)]
    exact (rows base r).parent_values hq

theorem ordinaryCopyRow_difference (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r c : Nat) :
    (ordinaryCopyRow base hpos coordinates r).difference c =
      (ordinaryCopyContext base hpos coordinates).copyValue (rows base r).difference c := by
  let C := ordinaryCopyContext base hpos coordinates
  change (match C.parent r c with
    | none => 0
    | some p => C.copyValue (rows base r).value c-C.copyValue (rows base r).value p) =
      (rows base r).difference (C.source0 c)
  unfold OrdinaryCopy.Context.parent
  cases hp : (C.mountain.row r).parent (C.source0 c) with
  | none =>
      change (rows base r).forest.parent (C.source0 c) = none at hp
      simp only [Option.map_none, Row.difference, hp]
  | some q =>
      have hleft := (C.mountain.row r).parent_left hp
      have hs := C.source0_bounds c
      simp only [Option.map_some]
      rw [C.copyValue_parentCopy (rows base r).value (by omega : q < C.coordinates.x)]
      change (rows base r).forest.parent (C.source0 c) = some q at hp
      rw [Row.difference, hp]
      rfl

theorem ordinaryCopyRow_next (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r : Nat) :
    (ordinaryCopyRow base hpos coordinates r).next =
      ordinaryCopyRow base hpos coordinates (r+1) := by
  apply Row.ext_values_parents
  · funext c
    exact ordinaryCopyRow_difference base hpos coordinates r c
  · funext c
    let C := ordinaryCopyContext base hpos coordinates
    change restrictedParent (C.row r) (ordinaryCopyRow base hpos coordinates r).difference c =
      C.parent (r+1) c
    have hv : (ordinaryCopyRow base hpos coordinates r).difference =
        C.copyValue (rows base r).difference := by
      funext q
      exact ordinaryCopyRow_difference base hpos coordinates r q
    rw [hv, C.restrictedParent_formula]
    rfl

def ordinaryCopiedBase (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) : Row := ordinaryCopyRow base hpos coordinates 0

theorem ordinaryCopy_rows (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r : Nat) :
    rows (ordinaryCopiedBase base hpos coordinates) r =
      ordinaryCopyRow base hpos coordinates r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (rows (ordinaryCopiedBase base hpos coordinates) r).next = _
      rw [ih, ordinaryCopyRow_next]

theorem ordinaryCopy_rows_value (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r c : Nat) :
    (rows (ordinaryCopiedBase base hpos coordinates) r).value c =
      (rows base r).value ((ordinaryCopyContext base hpos coordinates).source0 c) := by
  rw [ordinaryCopy_rows]
  rfl

theorem ordinaryCopy_rows_parent (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r c : Nat) :
    (rows (ordinaryCopiedBase base hpos coordinates) r).forest.parent c =
      (ordinaryCopyContext base hpos coordinates).parent r c := by
  rw [ordinaryCopy_rows]
  rfl

theorem ordinaryCopiedBase_positive (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (c : Nat) :
    0 < (ordinaryCopiedBase base hpos coordinates).value c := hpos _

theorem ordinaryCopy_height (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (c : Nat) :
    height (ordinaryCopiedBase base hpos coordinates) c =
      (ordinaryCopyContext base hpos coordinates).height c := by
  let newBase := ordinaryCopiedBase base hpos coordinates
  let C := ordinaryCopyContext base hpos coordinates
  have hp := ordinaryCopiedBase_positive base hpos coordinates c
  have hlive : ∀ r, 0 < (rows newBase r).value c ↔ r ≤ height base (C.source0 c) := by
    intro r
    rw [ordinaryCopy_rows_value]
    exact live_iff_le_height base (hpos _) r
  apply Nat.le_antisymm
  · exact (hlive (height newBase c)).mp (height_live newBase hp)
  · exact (live_iff_le_height newBase hp _).mp
      ((hlive _).mpr (Nat.le_refl _))

theorem ordinaryCopy_topValue (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (c : Nat) :
    topValue (ordinaryCopiedBase base hpos coordinates) c =
      (ordinaryCopyContext base hpos coordinates).copyValue (topValue base) c := by
  unfold topValue
  rw [ordinaryCopy_height, ordinaryCopy_rows_value]
  rfl

end OneY.Numeric

#print axioms OneY.Numeric.ordinaryCopy_rows
#print axioms OneY.Numeric.ordinaryCopy_height
#print axioms OneY.Numeric.ordinaryCopy_topValue
