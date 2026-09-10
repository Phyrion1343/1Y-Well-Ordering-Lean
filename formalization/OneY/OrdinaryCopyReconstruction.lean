import OneY.OrdinaryCopyRoots
import OneY.ReconstructionNumeric

/-!
# Ordinary copy commutes with the computed numerical reconstruction

The copied values satisfy the reconstruction equations because copied
parents have exactly the original source column. Uniqueness then identifies
them with the actual well-founded reconstruction computation.
-/

namespace OneY.OrdinaryCopy.Context

theorem copied_values_reconstruct (C : Context) (oldTop : Nat → Nat) :
    Reconstruction.Reconstructs C.toRowMountain (C.copyValue oldTop)
      (fun r c => Reconstruction.value C.mountain oldTop r (C.source0 c)) := by
  constructor
  · intro r c hr
    exact Reconstruction.value_absent C.mountain oldTop hr
  · intro c
    exact Reconstruction.value_top C.mountain oldTop (C.source0 c)
  · intro r c p hp
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hp
    have hleft := (C.mountain.row r).parent_left hq
    have hsource := C.source0_bounds c
    have hqp : C.source0 p = q := by
      rw [← heq, C.source0_parentCopy (by omega : q < C.coordinates.x)]
    rw [hqp]
    exact Reconstruction.value_recurrence C.mountain oldTop hq

theorem value_eq_source (C : Context) (oldTop : Nat → Nat) (r c : Nat) :
    Reconstruction.value C.toRowMountain (C.copyValue oldTop) r c =
      Reconstruction.value C.mountain oldTop r (C.source0 c) := by
  have h := Reconstruction.reconstructs_eq_value C.toRowMountain (C.copyValue oldTop)
    (C.copied_values_reconstruct oldTop)
  exact (congrFun (congrFun h r) c).symm

theorem value_parentCopy (C : Context) (oldTop : Nat → Nat) {c : Nat}
    (hc : c < C.coordinates.x) (b r : Nat) :
    Reconstruction.value C.toRowMountain (C.copyValue oldTop) r
      (C.coordinates.parentCopy b c) = Reconstruction.value C.mountain oldTop r c := by
  rw [C.value_eq_source, C.source0_parentCopy hc b]

theorem value_original (C : Context) (oldTop : Nat → Nat) {c : Nat}
    (hc : c < C.coordinates.x) (r : Nat) :
    Reconstruction.value C.toRowMountain (C.copyValue oldTop) r c =
      Reconstruction.value C.mountain oldTop r c := by
  rw [C.value_eq_source, (C.original_coordinates hc).1]

end OneY.OrdinaryCopy.Context

namespace OneY.Numeric

def ordinaryCopyContext (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) : OrdinaryCopy.Context :=
  ⟨mountain base hpos, coordinates⟩

theorem ordinaryCopy_value (base : Row) (hpos : ∀ c, 0 < base.value c)
    (coordinates : CopyCoordinates.Context) (r c : Nat) :
    Reconstruction.value (ordinaryCopyContext base hpos coordinates).toRowMountain
      ((ordinaryCopyContext base hpos coordinates).copyValue (topValue base)) r c =
        (rows base r).value ((ordinaryCopyContext base hpos coordinates).source0 c) := by
  rw [OrdinaryCopy.Context.value_eq_source]
  exact Reconstruction.value_numeric_cell base hpos r _

end OneY.Numeric

#print axioms OneY.OrdinaryCopy.Context.value_eq_source
#print axioms OneY.OrdinaryCopy.Context.value_parentCopy
#print axioms OneY.Numeric.ordinaryCopy_value
