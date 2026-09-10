import OneY.RootIndexed.Representation
import OneY.RootGeometry

/-!
# The finite diagram actually extracted from mountain parent graphs

Each real parent edge is annotated with the computed root of its row.
There is no supplied root-index map and no supplied diagram-validity axiom.
-/

namespace OneY.RootIndexed

universe u

open RootGeometry

def rowAtom (k : Nat) (M : RowMountain) (r c : Nat) : Atom where
  layer := k
  root := M.rootAt r c
  parent := ((M.row r).parent c).getD c
  child := c

theorem rowAtom_valid (k : Nat) (M : RowMountain) {n r c : Nat}
    (hc : c < n) (hr : r < M.height c) : (rowAtom k M r c).Valid n := by
  obtain ⟨p, hp⟩ := M.parent_exists r c hr
  have hroot := M.rootAt_of_parent hp
  have hle := M.rootAt_le r p
  have hleft := (M.row r).parent_left hp
  change M.rootAt r c ≤ ((M.row r).parent c).getD c ∧
    ((M.row r).parent c).getD c < c ∧ c < n
  simp only [hp, Option.getD_some]
  exact ⟨hroot ▸ hle, hleft, hc⟩

def columnAtoms (k : Nat) (M : RowMountain) (c : Nat) : List Atom :=
  (List.range (M.height c)).map fun r => rowAtom k M r c

def mountainAtoms (k n : Nat) (M : RowMountain) : List Atom :=
  (List.range n).flatMap fun c => columnAtoms k M c

def towerAtoms (K n : Nat) (M : Nat → RowMountain) : List Atom :=
  (List.range K).flatMap fun k => mountainAtoms k n (M k)

theorem mem_columnAtoms_iff (k : Nat) (M : RowMountain) (c : Nat) (e : Atom) :
    e ∈ columnAtoms k M c ↔ ∃ r, r < M.height c ∧ rowAtom k M r c = e := by
  simp [columnAtoms]

theorem mem_mountainAtoms_iff (k n : Nat) (M : RowMountain) (e : Atom) :
    e ∈ mountainAtoms k n M ↔
      ∃ c, c < n ∧ ∃ r, r < M.height c ∧ rowAtom k M r c = e := by
  simp [mountainAtoms, mem_columnAtoms_iff]

theorem mem_towerAtoms_iff (K n : Nat) (M : Nat → RowMountain) (e : Atom) :
    e ∈ towerAtoms K n M ↔
      ∃ k, k < K ∧ ∃ c, c < n ∧ ∃ r, r < (M k).height c ∧
        rowAtom k (M k) r c = e := by
  simp [towerAtoms, mem_mountainAtoms_iff]

def mountainDiagram (K n : Nat) (M : Nat → RowMountain) : Diagram where
  size := n
  atoms := towerAtoms K n M
  valid := by
    intro e he
    obtain ⟨k, _, c, hc, r, hr, rfl⟩ := (mem_towerAtoms_iff K n M e).mp he
    exact rowAtom_valid k (M k) hc hr

theorem rowAtom_holds_iff {α : Type u} (R : Nat → α → α → α → Prop)
    (f : Nat → α) (k : Nat) (M : RowMountain) (r c p : Nat)
    (hp : (M.row r).parent c = some p) :
    (rowAtom k M r c).Holds R f ↔ R k (f (M.rootAt r c)) (f p) (f c) := by
  simp only [Atom.Holds, rowAtom, hp, Option.getD_some]

/-- The finite-diagram condition is exactly the condition on every actual
parent edge, with its computed component root as the stability index. -/
theorem diagram_relations_iff {α : Type u} (R : Nat → α → α → α → Prop)
    (f : Nat → α) (K n : Nat) (M : Nat → RowMountain) :
    (∀ e ∈ (mountainDiagram K n M).atoms, e.Holds R f) ↔
      ∀ k, k < K → ∀ c, c < n → ∀ r p,
        ((M k).row r).parent c = some p →
          R k (f ((M k).rootAt r c)) (f p) (f c) := by
  constructor
  · intro h k hk c hc r p hp
    have hr := (M k).parent_source hp
    have he : rowAtom k (M k) r c ∈ towerAtoms K n M :=
      (mem_towerAtoms_iff K n M _).mpr ⟨k, hk, c, hc, r, hr, rfl⟩
    exact (rowAtom_holds_iff R f k (M k) r c p hp).mp (h _ he)
  · intro h e he
    obtain ⟨k, hk, c, hc, r, hr, rfl⟩ := (mem_towerAtoms_iff K n M e).mp he
    obtain ⟨p, hp⟩ := (M k).parent_exists r c hr
    exact (rowAtom_holds_iff R f k (M k) r c p hp).mpr (h k hk c hc r p hp)

end OneY.RootIndexed

#print axioms OneY.RootIndexed.mountainDiagram
#print axioms OneY.RootIndexed.diagram_relations_iff
