import OneY.RootIndexed.SpliceGeometry

/-!
# The concrete 1-Y block scheme

All finite geometric fields are proved for the actual copied mountain.
The semantic finite reflection principle remains an explicit argument.
Numerical canonical rebuilding is supplied by `ExpansionCanonical`; the
actual expansion is joined to this scheme in `ExpansionWellFounded`.
-/

namespace OneY.RootIndexed

universe u

open Numeric

def actualBlockScheme (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y)
    (bound : Nat) : BlockScheme where
  layer := K
  graph := copyDiagram a hbad bound
  cut := blockCut (badCoordinates a hbad)
  controlRoot := copyControlRoot a hbad
  facts := copyFacts a hbad bound
  templates := copyTemplates a hbad bound
  needs := copyNeeds a hbad bound
  cut_lt := blockCut_lt_width (badCoordinates a hbad)
  control_le := copyControlRoot_le a hbad
  geometry := actual_splice_geometry a hbad bound
  facts_valid := fun b _ he => copyFacts_valid a hbad bound b he
  templates_valid := fun b _ he => copyTemplates_valid a hbad bound b he
  needs_valid := fun b _ he => copyNeeds_valid a hbad bound b he
  virtual := fun b _ he => copyNeeds_virtual a hbad bound b he
  levels := fun b _ he => copyNeeds_levels a hbad bound b he
  cut_next := blockCut_succ (badCoordinates a hbad)
  control_next := copyControlRoot_succ a hbad bound
  facts_next := copyFacts_succ a hbad bound
  templates_next := copyTemplates_succ a hbad bound

theorem initial_facts_hold {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (bound : Nat)
    (f : Nat → α)
    (hF : Representation lt D R (mountainDiagram bound (x+1) (originalMountain a)) f) :
    ∀ e ∈ copyFacts a hbad bound 0, e.Holds R f := by
  intro e he
  obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
  rw [copyAtom_zero]
  obtain ⟨k, hk, c, hc, r, hr, rfl⟩ := (mem_towerAtoms_iff bound x _ old).mp hOld
  exact hF.relations _ ((mem_towerAtoms_iff bound (x+1) _ _).mpr
    ⟨k, hk, c, by omega, r, hr, rfl⟩)

theorem initial_templates_hold {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (bound : Nat)
    (f : Nat → α)
    (hF : Representation lt D R (mountainDiagram bound (x+1) (originalMountain a)) f) :
    ∀ e ∈ copyTemplates a hbad bound 0, e.Holds R f (f x) := by
  intro e he
  obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp he
  rw [copyTopAtom_zero]
  obtain ⟨k, hk, r, hr, rfl⟩ := (mem_originalTemplates_iff a bound x old).mp hOld
  exact hF.relations (rowAtom k (originalMountain a k) r x)
    ((mem_towerAtoms_iff bound (x+1) _ _).mpr ⟨k, hk, x, by omega, r, hr, rfl⟩)

theorem initial_control_holds {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (bound : Nat)
    (hK : K < bound) (f : Nat → α)
    (hF : Representation lt D R (mountainDiagram bound (x+1) (originalMountain a)) f) :
    R K (f (copyControlRoot a hbad 0)) (f (blockCut (badCoordinates a hbad) 0)) (f x) := by
  have hr : d < (originalMountain a K).height x :=
    (originalMountain a K).parent_source hbad.1
  have he := hF.relations (rowAtom K (originalMountain a K) d x)
    ((mem_towerAtoms_iff bound (x+1) _ _).mpr ⟨K, hK, x, by omega, d, hr, rfl⟩)
  have hR := (rowAtom_holds_iff R f K (originalMountain a K) d x y hbad.1).mp he
  simpa only [copyControlRoot, CopyCoordinates.Context.parentCopy_zero, blockCut,
    Nat.zero_mul, Nat.add_zero, badCoordinates] using hR

theorem copied_diagrams_bounded {α : Type u}
    (lt : α → α → Prop) (D : α → Prop) (R : Nat → α → α → α → Prop)
    (hTrans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (hStrict : ∀ {k index a b}, R k index a b → lt a b)
    (hWeak : ∀ {k small large p c}, lt small large → R k large p c → R k small p c)
    (reflection : FiniteReflection lt D R)
    (a : RootedRow) {K d x y : Nat} (hbad : BadAt a K d x y) (bound : Nat)
    (hK : K < bound) (f : Nat → α)
    (hF : Representation lt D R (mountainDiagram bound (x+1) (originalMountain a)) f)
    (N : Nat) :
    ∃ g, Representation lt D R (copyDiagram a hbad bound N) g ∧
      Bounded lt (copyDiagram a hbad bound N).size g (f x) := by
  have hBound : Bounded lt (copyDiagram a hbad bound 0).size f (f x) := by
    intro c hc
    have hc' : c < x := by
      simpa only [copyDiagram, mountainDiagram, CopyCoordinates.Context.width,
        Nat.zero_mul, Nat.add_zero, badCoordinates] using hc
    exact hF.ordered c x hc' (by change x < x+1; omega)
  obtain ⟨g, hg, hb, _⟩ := blockScheme_bounded_representations lt D R hTrans hStrict hWeak
    reflection (actualBlockScheme a hbad bound) f (f x)
    (hF.domain x (by change x < x+1; omega))
    (copyDiagram_initial_representation lt D R a hbad bound f hF) hBound
    (initial_facts_hold lt D R a hbad bound f hF)
    (initial_templates_hold lt D R a hbad bound f hF)
    (initial_control_holds lt D R a hbad bound hK f hF) N
  exact ⟨g, hg, hb⟩

end OneY.RootIndexed

#print axioms OneY.RootIndexed.actualBlockScheme
#print axioms OneY.RootIndexed.copied_diagrams_bounded
