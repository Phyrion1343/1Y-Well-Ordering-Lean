import OneY.ExpansionRebuildPrefix
import OneY.LowerTowerRebuild

/-! # Canonical rebuilding of the actual finite 1-Y output

All layer inputs and all nearest-smaller equations have been discharged
by the concrete tower construction. The statements below have only an
actual old bad root as their hypothesis.
-/

namespace OneY.Numeric

theorem rootedSequence_eq_of_values_eq {s t : List Nat} (hs : ZeroY.Legal s)
    (ht : ZeroY.Legal t) (he : s = t) : rootedSequence s hs = rootedSequence t ht := by
  cases he
  rfl

theorem expandValues_rooted_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) :
    rootedSequence (expandValues s hs N) (expandValues_legal s hs N) =
      rootedSequence
        (reconstructedValues (expandedGraphs (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 (sequenceBound s))
          (s.length-1 + N*(s.length-1-z.column))) (reconstructedValues_legal _ _) :=
  rootedSequence_eq_of_values_eq _ _ (expandValues_of_badRoot s hs N hz)

theorem reconstructedValues_layers (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) (width k : Nat) :
    (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row.AgreesBelow
      (layers (lowerTowerRooted (rootedSequence s hs) hbad) k).row width :=
  reconstructedValues_layers_agreesBelow _ _ _ (assemble_expanded_sequence_lower s hs hbad)
    (lowerTowerRooted_select_linear s hs hbad) k

theorem reconstructedValues_height (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) (width k : Nat)
    {c : Nat} (hc : c < width) :
    height (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row c =
        (expandedMountain (rootedSequence s hs) hbad k).height c := by
  rw [(reconstructedValues_layers s hs hbad width k).height hc]
  have ht := congrArg (fun M : RootGeometry.RowMountain => M.height c)
    (lowerTowerRooted_layers_mountain (rootedSequence s hs) hbad k)
  simpa only [mountain] using ht

theorem reconstructedValues_parent (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y) (width k r : Nat)
    {c : Nat} (hc : c < width) :
    (rows (layers (rootedSequence
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s)) width)
      (reconstructedValues_legal _ _)) k).row r).forest.parent c =
        ((expandedMountain (rootedSequence s hs) hbad k).row r).parent c := by
  rw [((reconstructedValues_layers s hs hbad width k).rows r).2 c hc]
  have ht := congrArg (fun M : RootGeometry.RowMountain => (M.row r).parent c)
    (lowerTowerRooted_layers_mountain (rootedSequence s hs) hbad k)
  simpa only [mountain] using ht

theorem expandValues_layers_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) (k : Nat) :
    (layers (rootedSequence (expandValues s hs N) (expandValues_legal s hs N)) k).row.AgreesBelow
      (layers (lowerTowerRooted (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2) k).row
      (s.length-1+N*(s.length-1-z.column)) := by
  rw [expandValues_rooted_of_badRoot s hs N hz]
  exact reconstructedValues_layers s hs (findBadRoot_sound s hs _ hz).2 _ k

theorem expandValues_height_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) (k : Nat)
    {c : Nat} (hc : c < (expandValues s hs N).length) :
    height (layers (rootedSequence (expandValues s hs N) (expandValues_legal s hs N)) k).row c =
      (expandedMountain (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 k).height c := by
  rw [expandValues_of_badRoot s hs N hz] at hc
  rw [expandValues_rooted_of_badRoot s hs N hz]
  rw [reconstructedValues_length] at hc
  exact reconstructedValues_height s hs (findBadRoot_sound s hs _ hz).2 _ k hc

theorem expandValues_parent_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) (k r : Nat)
    {c : Nat} (hc : c < (expandValues s hs N).length) :
    (rows (layers (rootedSequence (expandValues s hs N) (expandValues_legal s hs N)) k).row r).forest.parent c =
      ((expandedMountain (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 k).row r).parent c := by
  rw [expandValues_of_badRoot s hs N hz] at hc
  rw [expandValues_rooted_of_badRoot s hs N hz]
  rw [reconstructedValues_length] at hc
  exact reconstructedValues_parent s hs (findBadRoot_sound s hs _ hz).2 _ k r hc

end OneY.Numeric

namespace OneY.RootIndexed

universe u

open Numeric

theorem sequenceDiagram_eq_of_values_eq {s t : List Nat} (hs : ZeroY.Legal s)
    (ht : ZeroY.Legal t) (he : s = t) (J : Nat) : sequenceDiagram s hs J = sequenceDiagram t ht J := by
  cases he
  rfl

theorem reconstructedValues_diagram (s : List Nat) (hs : ZeroY.Legal s)
    {K d x y : Nat} (hbad : BadAt (rootedSequence s hs) K d x y)
    (hK : K < sequenceBound s) (N J : Nat) :
    (sequenceDiagram
      (reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        ((badCoordinates (rootedSequence s hs) hbad).width N))
      (reconstructedValues_legal _ _) J).IsPrefix
      (copyDiagram (rootedSequence s hs) hbad (sequenceBound s) N) :=
  reconstructedValues_diagram_isPrefix_of_height_bound _ _ _
    (assemble_expanded_sequence_lower s hs hbad) (lowerTowerRooted_select_linear s hs hbad)
    (expandedMountain (rootedSequence s hs) hbad) (lowerTowerRooted_layers_mountain _ hbad) J _
    (fun _ hk c _ => expandedMountain_height_zero_above_bound s hs hbad hK hk c)

theorem expandValues_diagram_of_badRoot (s : List Nat) (hs : ZeroY.Legal s) (N J : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) :
    (sequenceDiagram (expandValues s hs N) (expandValues_legal s hs N) J).IsPrefix
      (copyDiagram (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 (sequenceBound s) N) := by
  rw [sequenceDiagram_eq_of_values_eq _ (reconstructedValues_legal _ _) (expandValues_of_badRoot s hs N hz) J]
  exact reconstructedValues_diagram s hs (findBadRoot_sound s hs _ hz).2 (findBadRoot_sound s hs _ hz).1 N J

theorem expandValues_representation_of_badRoot {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (s : List Nat) (hs : ZeroY.Legal s) (N J : Nat)
    {z : RootAddress} (hz : findBadRoot s hs (s.length-1) = some z) (f : Nat → α)
    (hF : Representation lt D R
      (copyDiagram (rootedSequence s hs) (findBadRoot_sound s hs _ hz).2 (sequenceBound s) N) f) :
    Representation lt D R (sequenceDiagram (expandValues s hs N) (expandValues_legal s hs N) J) f :=
  representation_prefix lt D R (expandValues_diagram_of_badRoot s hs N J hz) f hF

end OneY.RootIndexed

#print axioms OneY.Numeric.expandValues_layers_of_badRoot
#print axioms OneY.Numeric.expandValues_height_of_badRoot
#print axioms OneY.Numeric.expandValues_parent_of_badRoot
#print axioms OneY.RootIndexed.expandValues_diagram_of_badRoot
#print axioms OneY.RootIndexed.expandValues_representation_of_badRoot
