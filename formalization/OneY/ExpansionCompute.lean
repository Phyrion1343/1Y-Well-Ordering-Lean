import OneY.Expansion
import OneY.ReconstructionCompute

/-! # Executable reconstruction and expansion with a proved equality -/

namespace OneY.TowerReconstruction

def assembleCompute : List RootGeometry.RowMountain → (Nat → Nat) → Nat → Nat
  | [], top => top
  | M :: rest, top => fun c =>
      Reconstruction.valueFuel M (assembleCompute rest top) (c+1) 0 c

theorem assemble_eq_compute (graphs : List RootGeometry.RowMountain) (top : Nat → Nat) :
    assemble graphs top = assembleCompute graphs top := by
  induction graphs with
  | nil => rfl
  | cons M rest ih =>
      funext c
      change Reconstruction.value M (assemble rest top) 0 c =
        Reconstruction.valueFuel M (assembleCompute rest top) (c+1) 0 c
      rw [← ih]
      exact Reconstruction.value_eq_compute M _ 0 c

end OneY.TowerReconstruction

namespace OneY.Numeric

def reconstructedValuesCompute (graphs : List RootGeometry.RowMountain) (width : Nat) : List Nat :=
  (List.range width).map (TowerReconstruction.assembleCompute graphs (fun _ => 1))

theorem reconstructedValues_eq_compute (graphs : List RootGeometry.RowMountain) (width : Nat) :
    reconstructedValues graphs width = reconstructedValuesCompute graphs width := by
  unfold reconstructedValues reconstructedValuesCompute
  rw [TowerReconstruction.assemble_eq_compute]

def expandValuesCompute (s : List Nat) (hs : ZeroY.Legal s) (N : Nat) : List Nat :=
  let x := s.length-1
  match hz : findBadRoot s hs x with
  | none => s.take x
  | some z =>
      let hbad := (findBadRoot_sound s hs x hz).2
      reconstructedValuesCompute (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        (x+N*(x-z.column))

theorem expandValues_eq_compute (s : List Nat) (hs : ZeroY.Legal s) (N : Nat) :
    expandValues s hs N = expandValuesCompute s hs N := by
  unfold expandValues expandValuesCompute
  dsimp only
  split <;> split
  · rfl
  · simp_all
  · simp_all
  · rename_i z hz z' hz'
    have he : z = z' := Option.some.inj (hz.symm.trans hz')
    subst z'
    exact reconstructedValues_eq_compute _ _

end OneY.Numeric

#print axioms OneY.Numeric.expandValues_eq_compute
