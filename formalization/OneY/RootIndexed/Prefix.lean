import OneY.RootIndexed.Diagram
import OneY.Prefix

/-! # Prefix restriction of the computed root-indexed diagrams -/

namespace OneY.RootIndexed

universe u

open RootGeometry

theorem rowAtom_prefix_congr (k : Nat) (M N : RowMountain) (n : Nat)
    (hP : ∀ r c, c < n → (M.row r).parent c = (N.row r).parent c)
    (r : Nat) {c : Nat} (hc : c < n) : rowAtom k M r c = rowAtom k N r c := by
  have hroot := ParentForest.root_prefix_congr (M.row r) (N.row r) n (hP r) c hc
  change M.rootAt r c = N.rootAt r c at hroot
  simp only [rowAtom, hroot, hP r c hc]

theorem mountainDiagram_isPrefix {K J n m : Nat} (hK : K ≤ J) (hn : n ≤ m)
    (M N : Nat → RowMountain)
    (hH : ∀ k c, c < n → (M k).height c = (N k).height c)
    (hP : ∀ k r c, c < n → ((M k).row r).parent c = ((N k).row r).parent c) :
    (mountainDiagram K n M).IsPrefix (mountainDiagram J m N) := by
  refine ⟨hn, ?_⟩
  intro e he
  obtain ⟨k, hk, c, hc, r, hr, he⟩ := (mem_towerAtoms_iff K n M e).mp he
  refine (mem_towerAtoms_iff J m N e).mpr ⟨k, by omega, c, by omega, r, ?_, ?_⟩
  · rw [← hH k c hc]
    exact hr
  · rw [← rowAtom_prefix_congr k (M k) (N k) n (hP k) r hc]
    exact he

def sequenceDiagram (s : List Nat) (hs : ZeroY.Legal s) (K : Nat) : Diagram :=
  mountainDiagram K s.length fun k =>
    Numeric.mountain (Numeric.layers (Numeric.rootedSequence s hs) k).row
      (Numeric.layers (Numeric.rootedSequence s hs) k).positive

theorem sequenceDiagram_take_isPrefix (s : List Nat) (hs : ZeroY.Legal s)
    (n K J : Nat) (hK : K ≤ J) :
    (sequenceDiagram (s.take n) (ZeroY.legal_take hs n) K).IsPrefix
      (sequenceDiagram s hs J) := by
  apply mountainDiagram_isPrefix hK (by simp; omega)
  · intro k c hc
    have hcn : c < n := by simpa using (Nat.lt_of_lt_of_le hc (List.length_take_le n s))
    exact ((Numeric.sequence_take_layers_agree s hs n k).height hcn).symm
  · intro k r c hc
    have hcn : c < n := by simpa using (Nat.lt_of_lt_of_le hc (List.length_take_le n s))
    exact ((Numeric.sequence_take_layers_agree s hs n k).rows r).2 c hcn |>.symm

theorem sequence_representation_take {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (s : List Nat) (hs : ZeroY.Legal s) (n K J : Nat) (hK : K ≤ J)
    (f : Nat → α) (hF : Representation lt D R (sequenceDiagram s hs J) f) :
    Representation lt D R (sequenceDiagram (s.take n) (ZeroY.legal_take hs n) K) f :=
  representation_prefix lt D R (sequenceDiagram_take_isPrefix s hs n K J hK) f hF

end OneY.RootIndexed

#print axioms OneY.RootIndexed.sequenceDiagram_take_isPrefix
#print axioms OneY.RootIndexed.sequence_representation_take
