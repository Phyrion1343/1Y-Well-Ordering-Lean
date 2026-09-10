import OneY.RootIndexed.CopyCoordinates
import OneY.RootIndexed.Prefix
import OneY.RootIndexed.TerminalRoots
import OneY.ExpansionProperties

/-!
# The concrete finite diagrams used for block reflection

The graphs and the transported source facts are computed from BadAt and the
actual copy maps. No edge-classification or semantic assumption is supplied
to these definitions. Classification into reflection cases is a separate
proof obligation.
-/

namespace OneY.RootIndexed

universe u

open RootGeometry Numeric

def originalMountain (a : RootedRow) (k : Nat) : RowMountain :=
  mountain (layers a k).row (layers a k).positive

def badCoordinates (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) :
    CopyCoordinates.Context :=
  ⟨y, x, (rows (layers a K).row d).forest.parent_left hbad.1⟩

def copyDiagram (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : Diagram :=
  mountainDiagram bound ((badCoordinates a hbad).width b) (expandedMountain a hbad)

def rowTemplate (k : Nat) (M : RowMountain) (r c : Nat) : TopAtom :=
  ⟨k, M.rootAt r c, ((M.row r).parent c).getD c⟩

def columnTemplates (k : Nat) (M : RowMountain) (c : Nat) : List TopAtom :=
  (List.range (M.height c)).map fun r => rowTemplate k M r c

def originalTemplates (a : RootedRow) (bound x : Nat) : List TopAtom :=
  (List.range bound).flatMap fun k => columnTemplates k (originalMountain a k) x

def copyFacts (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : List Atom :=
  (towerAtoms bound x (originalMountain a)).map (copyAtom (badCoordinates a hbad) b)

def copyTemplates (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : List TopAtom :=
  (originalTemplates a bound x).map (copyTopAtom (badCoordinates a hbad) b)

def copyControlRoot (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (b : Nat) : Nat :=
  (badCoordinates a hbad).parentCopy b ((originalMountain a K).rootAt d x)

def needHeight (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (k b : Nat) : Nat :=
  let H := (expandedMountain a hbad k).height ((badCoordinates a hbad).width b)
  if k < K then H else if k = K then min d H else 0

def copyNeeds (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : List TopAtom :=
  (List.range bound).flatMap fun k =>
    (List.range (needHeight a hbad k b)).map fun r =>
      rowTemplate k (expandedMountain a hbad k) r ((badCoordinates a hbad).width b)

theorem rowTemplate_valid (k : Nat) (M : RowMountain) {r c : Nat}
    (hr : r < M.height c) : (rowTemplate k M r c).Valid c := by
  have h := rowAtom_valid k M (Nat.lt_succ_self c) hr
  exact ⟨h.1, h.2.1⟩

theorem mem_originalTemplates_iff (a : RootedRow) (bound x : Nat) (e : TopAtom) :
    e ∈ originalTemplates a bound x ↔
      ∃ k, k < bound ∧ ∃ r, r < (originalMountain a k).height x ∧
        rowTemplate k (originalMountain a k) r x = e := by
  simp [originalTemplates, columnTemplates]

theorem copyFacts_valid (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) {e : Atom} (he : e ∈ copyFacts a hbad bound b) :
    e.Valid (copyDiagram a hbad bound b).size := by
  obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
  exact copyAtom_valid (badCoordinates a hbad) b
    ((mountainDiagram bound x (originalMountain a)).valid old hOld)

theorem copyTemplates_valid (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) {e : TopAtom} (he : e ∈ copyTemplates a hbad bound b) :
    e.Valid (copyDiagram a hbad bound b).size := by
  obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
  obtain ⟨k, _, r, hr, rfl⟩ := (mem_originalTemplates_iff a bound x old).mp hOld
  exact copyTopAtom_valid (badCoordinates a hbad) b (rowTemplate_valid k _ hr)

theorem copyControlRoot_le (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (b : Nat) : copyControlRoot a hbad b ≤ blockCut (badCoordinates a hbad) b := by
  apply parentCopy_le_cut
  have hroot := (originalMountain a K).rootAt_of_parent hbad.1
  rw [hroot]
  exact (originalMountain a K).rootAt_le d y

theorem copyFacts_succ (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : copyFacts a hbad bound (b+1) =
      (copyFacts a hbad bound b).map
        (moveAtom (copyDiagram a hbad bound b).size (blockCut (badCoordinates a hbad) b)) := by
  simp only [copyFacts, List.map_map]
  apply List.map_congr_left
  intro e he
  exact (moveAtom_copyAtom (badCoordinates a hbad) b e).symm

theorem copyTemplates_succ (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : copyTemplates a hbad bound (b+1) =
      (copyTemplates a hbad bound b).map
        (moveTopAtom (copyDiagram a hbad bound b).size (blockCut (badCoordinates a hbad) b)) := by
  simp only [copyTemplates, List.map_map]
  apply List.map_congr_left
  intro e he
  exact (moveTopAtom_copyTopAtom (badCoordinates a hbad) b e).symm

theorem copyControlRoot_succ (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) : copyControlRoot a hbad (b+1) =
      moveColumn (copyDiagram a hbad bound b).size (blockCut (badCoordinates a hbad) b)
        (copyControlRoot a hbad b) :=
  (moveColumn_parentCopy (badCoordinates a hbad) b _).symm

theorem copyDiagram_zero_isPrefix (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (bound : Nat) :
    (copyDiagram a hbad bound 0).IsPrefix
      (mountainDiagram bound (x+1) (originalMountain a)) := by
  apply mountainDiagram_isPrefix (Nat.le_refl _)
    (show (badCoordinates a hbad).width 0 ≤ x+1 by
      simp [CopyCoordinates.Context.width, badCoordinates])
  · intro k c hc
    exact expandedMountain_height_original a hbad k
      (by simpa only [CopyCoordinates.Context.width, badCoordinates, Nat.zero_mul, Nat.add_zero] using hc)
  · intro k r c hc
    exact expandedMountain_parent_original a hbad k r
      (by simpa only [CopyCoordinates.Context.width, badCoordinates, Nat.zero_mul, Nat.add_zero] using hc)

theorem copyDiagram_initial_representation {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (bound : Nat)
    (f : Nat → α)
    (hF : Representation lt D R (mountainDiagram bound (x+1) (originalMountain a)) f) :
    Representation lt D R (copyDiagram a hbad bound 0) f :=
  representation_prefix lt D R (copyDiagram_zero_isPrefix a hbad bound) f hF

theorem mem_copyNeeds_iff (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) (e : TopAtom) : e ∈ copyNeeds a hbad bound b ↔
      ∃ k, k < bound ∧ ∃ r, r < needHeight a hbad k b ∧
        rowTemplate k (expandedMountain a hbad k) r ((badCoordinates a hbad).width b) = e := by
  simp [copyNeeds]

theorem needHeight_le (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (k b : Nat) : needHeight a hbad k b ≤
      (expandedMountain a hbad k).height ((badCoordinates a hbad).width b) := by
  unfold needHeight
  dsimp only
  split
  · exact Nat.le_refl _
  · split <;> omega

theorem copyNeeds_valid (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) {e : TopAtom} (he : e ∈ copyNeeds a hbad bound b) :
    e.Valid (copyDiagram a hbad bound b).size := by
  obtain ⟨k, _, r, hr, rfl⟩ := (mem_copyNeeds_iff a hbad bound b e).mp he
  exact rowTemplate_valid k _ (Nat.lt_of_lt_of_le hr (needHeight_le a hbad k b))

theorem copyNeeds_levels (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound b : Nat) {e : TopAtom} (he : e ∈ copyNeeds a hbad bound b) :
    e.layer < K ∨ (e.layer = K ∧ e.root < copyControlRoot a hbad b) := by
  obtain ⟨k, _, r, hr, rfl⟩ := (mem_copyNeeds_iff a hbad bound b e).mp he
  by_cases hk : k < K
  · exact Or.inl hk
  · have hkEq : k = K := by
      by_cases hne : k = K
      · exact hne
      · have hn : needHeight a hbad k b = 0 := by simp [needHeight, hk, hne]
        rw [hn] at hr
        omega
    subst k
    have hrd : r < d := by
      simp only [needHeight, Nat.lt_irrefl, ↓reduceIte] at hr
      omega
    refine Or.inr ⟨rfl, ?_⟩
    have hbase := (badAtTerminalContext a hbad).rootAt_low_last_lt_control hrd b
    have hm : expandedMountain a hbad K = badAtTerminalMountain a hbad := by
      simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
    have hroot : (rowTemplate K (expandedMountain a hbad K) r
        ((badCoordinates a hbad).width b)).root < (originalMountain a K).rootAt d x := by
      rw [hm]
      exact hbase
    apply Nat.lt_of_lt_of_le hroot
    unfold copyControlRoot CopyCoordinates.Context.parentCopy
    split <;> omega

end OneY.RootIndexed

#print axioms OneY.RootIndexed.copyControlRoot_le
#print axioms OneY.RootIndexed.copyDiagram_initial_representation
#print axioms OneY.RootIndexed.copyNeeds_levels
