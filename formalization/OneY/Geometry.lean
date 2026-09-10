import Std

/-!
# A local geometric lemma for 1-Y mountains

This file does not assert termination of 1-Y. It proves the vertex/cone
characterization for a family of nested, leftward parent forests. `rootAt`
is the root of a row's parent forest. The structure fields explicitly list
the local forest facts used here; connecting this structure to a complete
formal definition of the 1-Y algorithm is a separate obligation.
-/

namespace OneY.Geometry

structure Mountain where
  height : Nat → Nat
  parent : Nat → Nat → Option Nat
  rootAt : Nat → Nat → Nat
  parent_exists : ∀ r c, r < height c → ∃ p, parent r c = some p
  parent_left : ∀ {r c p}, parent r c = some p → p < c
  parent_endpoint : ∀ {r c p}, parent r c = some p → r ≤ height p
  parent_source : ∀ {r c p}, parent r c = some p → r < height c
  top_root : ∀ c, rootAt (height c) c = c
  nested_roots : ∀ {h r c p}, h ≤ r → parent r c = some p →
    rootAt h c = rootAt h p

variable (M : Mountain)

/-- A left-up step traverses a pair's left leg in reverse. Right-down
steps remain above the starting vertex's row. -/
inductive Reach (M : Mountain) (y : Nat) : Nat → Nat → Prop where
  | start : Reach M y (M.height y) y
  | leftUp {r p c} : Reach M y r p → M.parent r c = some p → Reach M y (r+1) c
  | rightDown {r c} : M.height y ≤ r → Reach M y (r+1) c → Reach M y r c

def Cone (y c : Nat) : Prop :=
  M.height y ≤ M.height c ∧ M.rootAt (M.height y) c = y

theorem reach_in_cone {y r c} (hr : Reach M y r c) :
    M.height y ≤ r ∧ r ≤ M.height c ∧ Cone M y c := by
  induction hr with
  | start =>
      exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, M.top_root _⟩
  | @leftUp r p c _ hp ih =>
      have hc := M.parent_source hp
      have hh : M.height y ≤ r+1 := by omega
      have hc' : r+1 ≤ M.height c := by omega
      have heq := M.nested_roots ih.1 hp
      exact ⟨hh, hc', by omega, heq.trans ih.2.2.2⟩
  | @rightDown r c hh _ ih =>
      exact ⟨hh, by omega, ih.2.2⟩

theorem descend {y c top bottom : Nat} (hr : Reach M y top c)
    (hbottom : M.height y ≤ bottom) (hle : bottom ≤ top) :
    Reach M y bottom c := by
  have aux : ∀ gap, ∀ bottom,
      M.height y ≤ bottom → top = bottom + gap → Reach M y bottom c := by
    intro gap
    induction gap with
    | zero =>
        intro bottom _ heq
        have : top = bottom := by omega
        simpa [this] using hr
    | succ gap ih =>
        intro bottom hb heq
        have hnext : Reach M y (bottom+1) c :=
          ih (bottom+1) (by omega) (by omega)
        exact Reach.rightDown hb hnext
  exact aux (top-bottom) bottom hbottom (by omega)

theorem top_reachable_of_cone (y c : Nat) (hc : Cone M y c) :
    Reach M y (M.height c) c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases heq : c = y
      · subst c
        exact Reach.start
      · have hstrict : M.height y < M.height c := by
          have hle := hc.1
          by_cases hs : M.height y < M.height c
          · exact hs
          apply False.elim
          have hh : M.height c = M.height y := by omega
          have ht := M.top_root c
          rw [hh] at ht
          have : c = y := ht.symm.trans hc.2
          exact heq this
        obtain ⟨p, hp⟩ := M.parent_exists (M.height c-1) c (by omega)
        have hpleft := M.parent_left hp
        have hpend := M.parent_endpoint hp
        have hfloor : M.height y ≤ M.height c-1 := by omega
        have hroots := M.nested_roots hfloor hp
        have hpcone : Cone M y p := ⟨by omega, hroots.symm.trans hc.2⟩
        have hptop := ih p hpleft hpcone
        have hpatrow : Reach M y (M.height c-1) p :=
          descend M hptop hfloor hpend
        have hup := Reach.leftUp hpatrow hp
        have hh : M.height c-1+1 = M.height c := by omega
        simpa [hh] using hup

/-- Reaching a column's top by the permitted leg walk is equivalent to
belonging to the starting top row's rooted component. -/
theorem vertex_iff_cone (y c : Nat) :
    Reach M y (M.height c) c ↔ Cone M y c := by
  constructor
  · intro hr
    exact (reach_in_cone M hr).2.2
  · exact top_reachable_of_cone M y c

/-- Repeated left-up/right-down pairs, all at a fixed row. -/
inductive Horizontal (M : Mountain) (r q : Nat) : Nat → Prop where
  | start : Horizontal M r q q
  | step {p c} : Horizontal M r q p → M.parent r c = some p → Horizontal M r q c

theorem horizontal_roots {h r q c : Nat} (hh : h ≤ r)
    (hp : Horizontal M r q c) : M.rootAt h c = M.rootAt h q := by
  induction hp with
  | start => rfl
  | step _ hpar ih => exact (M.nested_roots hh hpar).trans ih

theorem horizontal_from_root (r c : Nat) (hc : r ≤ M.height c) :
    M.height (M.rootAt r c) = r ∧ Horizontal M r (M.rootAt r c) c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases heq : r = M.height c
      · have hroot : M.rootAt r c = c := by simpa [heq] using M.top_root c
        rw [hroot]
        exact ⟨heq.symm, Horizontal.start⟩
      · obtain ⟨p, hp⟩ := M.parent_exists r c (by omega)
        have hpend := M.parent_endpoint hp
        have hpleft := M.parent_left hp
        have hroot := M.nested_roots (Nat.le_refl r) hp
        have hprev := ih p hpleft hpend
        rw [hroot]
        exact ⟨hprev.1, Horizontal.step hprev.2 hp⟩

/-- A contour pair lies on a horizontal walk from some reachable top. -/
def Contour (y r c : Nat) : Prop :=
  r < M.height c ∧ ∃ q, Reach M y (M.height q) q ∧
    M.height q = r ∧ Horizontal M r q c

theorem contour_iff (y r c : Nat) :
    Contour M y r c ↔
    r < M.height c ∧ M.height y ≤ r ∧ Cone M y c := by
  constructor
  · rintro ⟨hc, q, hreach, hqr, hpath⟩
    have hq := reach_in_cone M hreach
    have hh : M.height y ≤ r := by omega
    have hroots := horizontal_roots M hh hpath
    exact ⟨hc, hh, by omega, hroots.trans hq.2.2.2⟩
  · rintro ⟨hc, hh, hcone⟩
    have hfrom := horizontal_from_root M r c (Nat.le_of_lt hc)
    have hroots := horizontal_roots M hh hfrom.2
    have hqcone : Cone M y (M.rootAt r c) :=
      ⟨by omega, hroots.symm.trans hcone.2⟩
    exact ⟨hc, M.rootAt r c, top_reachable_of_cone M y _ hqcone,
      hfrom.1, hfrom.2⟩

def Reference (y r c : Nat) : Prop :=
  r = M.height y ∧ r < M.height c ∧ Horizontal M r y c

theorem reference_iff (y r c : Nat) :
    Reference M y r c ↔
    r = M.height y ∧ r < M.height c ∧ Cone M y c := by
  constructor
  · rintro ⟨hr, hc, hpath⟩
    have hroots := horizontal_roots M (by omega : M.height y ≤ r) hpath
    exact ⟨hr, hc, by omega, hroots.trans (M.top_root y)⟩
  · rintro ⟨hr, hc, hcone⟩
    have hfrom := horizontal_from_root M r c (Nat.le_of_lt hc)
    have hroot : M.rootAt r c = y := by simpa [hr] using hcone.2
    exact ⟨hr, hc, by simpa [hroot] using hfrom.2⟩

end OneY.Geometry

#print axioms OneY.Geometry.vertex_iff_cone
#print axioms OneY.Geometry.contour_iff
#print axioms OneY.Geometry.reference_iff
