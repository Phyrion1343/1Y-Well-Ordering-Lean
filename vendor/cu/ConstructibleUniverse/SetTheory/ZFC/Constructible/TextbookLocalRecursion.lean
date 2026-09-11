/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassWellFounded

/-!
# The local-graph proof of textbook class recursion

This file formalizes the existence proof on page 108 of Wang Fangting,
*Axiomatic Set Theory*.  It deliberately constructs the local solutions
`f_x` as actual Kuratowski graphs rather than defining the final class
function first.

For a point `x` the construction is as follows.

* the local domain is `d_x = {x} ∪ cl(A,x,R)`;
* for every immediate predecessor `y R x`, induction supplies a local graph
  `f_y` on `d_y`;
* the local graphs agree on intersections of their domains;
* their set-indexed union `q` is consequently a function graph, with domain
  exactly `cl(A,x,R)`;
* adjoining the pair carrying the value at `x` produces `f_x`.

The only use of Lean's `WellFounded` API is to organize the induction after
`wellFounded_classRel_zfSubtype` has derived it from the textbook set-minimum
and set-likeness hypotheses.  No global recursion solution is assumed or
used.  Every graph occurring below is an ambient `ZFSet`; this file makes no
claim that one of these graphs belongs to an inner model.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Local solutions and overlap uniqueness -/

/-- The recursion equation restricted to the textbook local domain `d_x`. -/
def SatisfiesTextbookLocalRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (value : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ t, t ∈ localRecursionDomain A R hsetLike x →
    value t = step t (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike t) value)

/-- A local solution in the literal set-theoretic form used in the textbook.
`graph` is an actual set of Kuratowski pairs, while `value` records its unique
value semantics in a convenient Lean form. -/
structure TextbookLocalSolution
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) where
  value : ZFSet.{u} → ZFSet.{u}
  graph : ZFSet.{u}
  graph_eq : graph = predecessorRestrictionGraph
    (localRecursionDomain A R hsetLike x) value
  satisfies : SatisfiesTextbookLocalRecursion A R hsetLike step x value

/-- Two local solutions agree wherever their local domains overlap.  This is
the property labelled (3) in the textbook. -/
theorem textbookLocalSolutions_agreeOn_intersection
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x)
    (fy : TextbookLocalSolution A R hR.2.2 step y) :
    ∀ t, t ∈ localRecursionDomain A R hR.2.2 x ∩
        localRecursionDomain A R hR.2.2 y →
      fx.value t = fy.value t := by
  apply recursionSolutions_agreeOn hR.2.1
  · intro t ht
    exact localRecursionDomain_subset hR.2.2 hx
      (ZFSet.mem_inter.mp ht).1
  · intro t ht z hzt
    have ht' := ZFSet.mem_inter.mp ht
    exact ZFSet.mem_inter.mpr
      ⟨localRecursionDomain_predecessorClosed hR.1 hR.2.2 hx ht'.1 hzt,
        localRecursionDomain_predecessorClosed hR.1 hR.2.2 hy ht'.2 hzt⟩
  · intro t ht
    exact displayedPredecessors_spec hR.2.2
      (localRecursionDomain_subset hR.2.2 hx (ZFSet.mem_inter.mp ht).1)
  · intro t ht
    exact fx.satisfies t (ZFSet.mem_inter.mp ht).1
  · intro t ht
    exact fy.satisfies t (ZFSet.mem_inter.mp ht).2

/-- Graph form of textbook property (3): the two actual local graphs have
equal restrictions to the intersection of their domains. -/
theorem textbookLocalSolution_restrictionGraphs_eq_on_intersection
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x)
    (fy : TextbookLocalSolution A R hR.2.2 step y) :
    predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x ∩
          localRecursionDomain A R hR.2.2 y) fx.value =
      predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x ∩
          localRecursionDomain A R hR.2.2 y) fy.value := by
  apply predecessorRestrictionGraph_congr
  exact textbookLocalSolutions_agreeOn_intersection hR hx hy fx fy

/-! ## A closure point lies strictly below its top -/

/-- Membership in a finite predecessor layer gives a nonempty finite
`R`-chain to the top point.  The chain is stated on the subtype of `A`, where
the textbook class-minimum theorem provides genuine well-foundedness. -/
theorem transGen_classRel_of_mem_predecessorLayer
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R)
    {x z : ZFSet.{u}} (hx : x ∈ A) {n : Nat}
    (hz : z ∈ predecessorLayer A R hsetLike x n) :
    Relation.TransGen
      (fun y x : {w : ZFSet.{u} // w ∈ A} => ClassRel R y.1 x.1)
      ⟨z, predecessorLayer_subset hsetLike hx n hz⟩
      ⟨x, hx⟩ := by
  induction n generalizing z with
  | zero =>
      have hzSpec := (displayedPredecessors_spec hsetLike hx z).mp
        (by simpa only [predecessorLayer_zero] using hz)
      exact Relation.TransGen.single hzSpec.2
  | succ n ih =>
      rcases (mem_predecessorLayer_succ_iff hsetLike hx n).mp hz with
        ⟨y, hyLayer, hzA, hzy⟩
      have hyA : y ∈ A := predecessorLayer_subset hsetLike hx n hyLayer
      have htail := ih hyLayer
      exact Relation.TransGen.head hzy htail

/-- A point is not in its own finite predecessor closure.  This is the fact
which makes adjoining the top graph pair a genuine one-point extension. -/
theorem not_mem_predecessorClosure_self
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) {x : ZFSet.{u}} (hx : x ∈ A) :
    x ∉ predecessorClosure A R hR.2.2 x := by
  intro hxx
  rcases mem_predecessorClosure_iff.mp hxx with ⟨n, hxn⟩
  have hcycle := transGen_classRel_of_mem_predecessorLayer
    hR.2.2 hx hxn
  exact (wellFounded_classRel_zfSubtype hR).transGen.irrefl.irrefl
    ⟨x, hx⟩ hcycle

/-! ## Gluing the predecessor-local graphs -/

section Glue

variable {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
variable (hR : IsWellFoundedSetLikeOn A R)
variable (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
variable {x : ZFSet.{u}}

/-- The actual set `d = ⋃ {d_y | y R x}` from the textbook proof. -/
noncomputable def predecessorLocalDomainUnion (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion fun y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x) =>
    localRecursionDomain A R hR.2.2 y.1

/-- The domain of the union of predecessor-local solutions is exactly
`cl(A,x,R)`. -/
theorem predecessorLocalDomainUnion_eq_predecessorClosure
    (hx : x ∈ A) :
    predecessorLocalDomainUnion hR x =
      predecessorClosure A R hR.2.2 x := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases ZFSet.mem_iUnion.mp hz with ⟨y, hzy⟩
    have hySpec := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2
    rcases mem_localRecursionDomain_iff.mp hzy with hzx | hzClosure
    · subst z
      apply mem_predecessorClosure_iff.mpr
      refine ⟨0, ?_⟩
      rw [predecessorLayer_zero]
      exact y.2
    · exact predecessorClosure_subset_of_rel hR.1 hR.2.2 hySpec.2
        hzClosure
  · intro hz
    rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
    have hlevels : ∀ m, ∀ z,
        z ∈ predecessorLayer A R hR.2.2 x m →
          z ∈ predecessorLocalDomainUnion hR x := by
      intro m
      induction m with
      | zero =>
          intro z hz0
          let zPred : ZFCarrier
              (displayedPredecessors A R hR.2.2 x) :=
            ⟨z, by simpa only [predecessorLayer_zero] using hz0⟩
          apply ZFSet.mem_iUnion.mpr
          refine ⟨zPred, ?_⟩
          exact mem_localRecursionDomain_iff.mpr (Or.inl rfl)
      | succ m ih =>
          intro z hzs
          rcases (mem_predecessorLayer_succ_iff hR.2.2 hx m).mp hzs with
            ⟨y, hym, _hzA, hzy⟩
          have hyUnion := ih y hym
          rcases ZFSet.mem_iUnion.mp hyUnion with ⟨w, hyw⟩
          have hwA := (displayedPredecessors_spec hR.2.2 hx w.1).mp w.2 |>.1
          exact ZFSet.mem_iUnion.mpr
            ⟨w, localRecursionDomain_predecessorClosed
              hR.1 hR.2.2 hwA hyw hzy⟩
    exact hlevels n z hzn

variable (children : ∀ y : ZFCarrier
  (displayedPredecessors A R hR.2.2 x),
    TextbookLocalSolution A R hR.2.2 step y.1)

/-- The actual graph `q = ⋃ {f_y | y R x}`. -/
noncomputable def predecessorLocalGraphUnion : ZFSet.{u} :=
  ZFSet.iUnion fun y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x) =>
    (children y).graph

/-- A totalized value function represented by the glued graph.  At a point
in one of the child domains, it takes the value of one chosen child.  Overlap
agreement below proves that this value is independent of the choice. -/
noncomputable def gluedPredecessorValue (t : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if ht : ∃ y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x),
      t ∈ localRecursionDomain A R hR.2.2 y.1 then
    (children (Classical.choose ht)).value t
  else
    ∅

/-- Every child solution agrees with the glued value throughout its domain. -/
theorem child_value_eq_gluedPredecessorValue
    (hx : x ∈ A)
    (y : ZFCarrier (displayedPredecessors A R hR.2.2 x))
    {t : ZFSet.{u}}
    (ht : t ∈ localRecursionDomain A R hR.2.2 y.1) :
    (children y).value t = gluedPredecessorValue hR step children t := by
  classical
  let hex : ∃ z : ZFCarrier
      (displayedPredecessors A R hR.2.2 x),
      t ∈ localRecursionDomain A R hR.2.2 z.1 := ⟨y, ht⟩
  rw [gluedPredecessorValue, dif_pos hex]
  have hyA := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2 |>.1
  have hzA := (displayedPredecessors_spec hR.2.2 hx
    (Classical.choose hex).1).mp (Classical.choose hex).2 |>.1
  apply textbookLocalSolutions_agreeOn_intersection hR hyA hzA
    (children y) (children (Classical.choose hex)) t
  exact ZFSet.mem_inter.mpr ⟨ht, Classical.choose_spec hex⟩

/-- The union `q` is precisely the Kuratowski graph of the glued value on
the union of the child domains. -/
theorem predecessorLocalGraphUnion_eq_restrictionGraph (hx : x ∈ A) :
    predecessorLocalGraphUnion hR step children =
      predecessorRestrictionGraph
        (predecessorLocalDomainUnion hR x)
        (gluedPredecessorValue hR step children) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    rcases ZFSet.mem_iUnion.mp hp with ⟨y, hpy⟩
    rw [(children y).graph_eq] at hpy
    rcases mem_predecessorRestrictionGraph_iff.mp hpy with
      ⟨t, ht, rfl⟩
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨t, ZFSet.mem_iUnion.mpr ⟨y, ht⟩, ?_⟩
    rw [child_value_eq_gluedPredecessorValue
      (hR := hR) (step := step) (children := children) hx y ht]
  · intro hp
    rcases mem_predecessorRestrictionGraph_iff.mp hp with
      ⟨t, ht, rfl⟩
    rcases ZFSet.mem_iUnion.mp ht with ⟨y, hty⟩
    apply ZFSet.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    rw [(children y).graph_eq]
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨t, hty, ?_⟩
    rw [child_value_eq_gluedPredecessorValue
      (hR := hR) (step := step) (children := children) hx y hty]

/-- After identifying the domain union with the closure, the graph `q` has
exactly the domain claimed on page 108. -/
theorem predecessorLocalGraphUnion_eq_closureGraph (hx : x ∈ A) :
    predecessorLocalGraphUnion hR step children =
      predecessorRestrictionGraph
        (predecessorClosure A R hR.2.2 x)
        (gluedPredecessorValue hR step children) := by
  rw [predecessorLocalGraphUnion_eq_restrictionGraph
      (hR := hR) (step := step) (children := children) hx,
    predecessorLocalDomainUnion_eq_predecessorClosure hR hx]

/-- The glued value already satisfies the recursion equation throughout
`cl(A,x,R)`. -/
theorem gluedPredecessorValue_satisfies_on_closure
    (hx : x ∈ A)
    {t : ZFSet.{u}}
    (ht : t ∈ predecessorClosure A R hR.2.2 x) :
    gluedPredecessorValue hR step children t =
      step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t)
        (gluedPredecessorValue hR step children)) := by
  have htUnion : t ∈ predecessorLocalDomainUnion hR x := by
    rw [predecessorLocalDomainUnion_eq_predecessorClosure hR hx]
    exact ht
  rcases ZFSet.mem_iUnion.mp htUnion with ⟨y, hty⟩
  have hyA := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2 |>.1
  calc
    gluedPredecessorValue hR step children t = (children y).value t :=
      (child_value_eq_gluedPredecessorValue
        (hR := hR) (step := step) (children := children) hx y hty).symm
    _ = step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t) (children y).value) :=
      (children y).satisfies t hty
    _ = step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t)
        (gluedPredecessorValue hR step children)) := by
      apply congrArg (step t)
      apply predecessorRestrictionGraph_congr
      intro z hz
      have htA := localRecursionDomain_subset hR.2.2 hyA hty
      have hzt := (displayedPredecessors_spec hR.2.2 htA z).mp hz |>.2
      have hzyDomain := localRecursionDomain_predecessorClosed
        hR.1 hR.2.2 hyA hty hzt
      exact child_value_eq_gluedPredecessorValue
        (hR := hR) (step := step) (children := children)
        hx y hzyDomain

/-! ## Adjoining the top pair -/

/-- The value at the new top point, with the glued predecessor graph as the
second argument of the recursion operator. -/
noncomputable def localTopValue : ZFSet.{u} :=
  step x (predecessorRestrictionGraph
    (displayedPredecessors A R hR.2.2 x)
    (gluedPredecessorValue hR step children))

/-- The value function represented by the graph after adjoining its top
pair. -/
noncomputable def extendedLocalValue (t : ZFSet.{u}) : ZFSet.{u} :=
  by
    classical
    exact if t = x then localTopValue hR step children
    else gluedPredecessorValue hR step children t

/-- The literal graph extension `f_x = q ∪ {⟨x,G(x,q↾x-hat)⟩}`. -/
noncomputable def extendedLocalGraph : ZFSet.{u} :=
  predecessorLocalGraphUnion hR step children ∪
    ({ZFSet.pair x (localTopValue hR step children)} : ZFSet.{u})

@[simp]
theorem extendedLocalValue_at_top :
    extendedLocalValue hR step children x =
      localTopValue hR step children := by
  simp [extendedLocalValue]

theorem extendedLocalValue_eq_glued_of_mem_closure
    (hx : x ∈ A) {t : ZFSet.{u}}
    (ht : t ∈ predecessorClosure A R hR.2.2 x) :
    extendedLocalValue hR step children t =
      gluedPredecessorValue hR step children t := by
  have htx : t ≠ x := by
    intro h
    subst t
    exact not_mem_predecessorClosure_self hR hx ht
  simp [extendedLocalValue, htx]

/-- The adjoined set is exactly the graph of the extended value on `d_x`. -/
theorem extendedLocalGraph_eq_restrictionGraph (hx : x ∈ A) :
    extendedLocalGraph hR step children =
      predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x)
        (extendedLocalValue hR step children) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    rcases ZFSet.mem_union.mp hp with hpq | hpTop
    · rw [predecessorLocalGraphUnion_eq_closureGraph
        (hR := hR) (step := step) (children := children) hx] at hpq
      rcases mem_predecessorRestrictionGraph_iff.mp hpq with
        ⟨t, ht, rfl⟩
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨t, mem_localRecursionDomain_iff.mpr (Or.inr ht), ?_⟩
      rw [extendedLocalValue_eq_glued_of_mem_closure
        (hR := hR) (step := step) (children := children) hx ht]
    · have hpEq : ZFSet.pair x (localTopValue hR step children) = p := by
        exact (ZFSet.mem_singleton.mp hpTop).symm
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨x, mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_⟩
      rw [extendedLocalValue_at_top hR step children]
      exact hpEq
  · intro hp
    rcases mem_predecessorRestrictionGraph_iff.mp hp with
      ⟨t, ht, rfl⟩
    rcases mem_localRecursionDomain_iff.mp ht with rfl | htClosure
    · apply ZFSet.mem_union.mpr
      right
      simp
    · apply ZFSet.mem_union.mpr
      left
      rw [predecessorLocalGraphUnion_eq_closureGraph
        (hR := hR) (step := step) (children := children) hx]
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨t, htClosure, ?_⟩
      rw [extendedLocalValue_eq_glued_of_mem_closure
        (hR := hR) (step := step) (children := children) hx htClosure]

/-- The extended graph satisfies the recursion equation at every point of
its local domain. -/
theorem extendedLocalValue_satisfies (hx : x ∈ A) :
    SatisfiesTextbookLocalRecursion A R hR.2.2 step x
      (extendedLocalValue hR step children) := by
  intro t ht
  rcases mem_localRecursionDomain_iff.mp ht with htEq | htClosure
  · subst t
    rw [extendedLocalValue_at_top]
    unfold localTopValue
    apply congrArg (step x)
    apply predecessorRestrictionGraph_congr
    intro z hz
    have hzSpec := (displayedPredecessors_spec hR.2.2 hx z).mp hz
    have hzLayer : z ∈ predecessorLayer A R hR.2.2 x 0 := by
      simpa only [predecessorLayer_zero] using hz
    have hzClosure : z ∈ predecessorClosure A R hR.2.2 x :=
      mem_predecessorClosure_iff.mpr ⟨0, hzLayer⟩
    exact extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx hzClosure |>.symm
  · rw [extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx htClosure,
      gluedPredecessorValue_satisfies_on_closure
        (hR := hR) (step := step) (children := children) hx htClosure]
    apply congrArg (step t)
    apply predecessorRestrictionGraph_congr
    intro z hz
    have htA := predecessorClosure_subset hR.2.2 hx htClosure
    have hzt := (displayedPredecessors_spec hR.2.2 htA z).mp hz |>.2
    have hzClosure := predecessorClosure_downward_closed
      hR.1 hR.2.2 hx htClosure hzt
    exact (extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx hzClosure).symm

/-- The local solution assembled from the predecessor-local solutions by
the literal union-and-adjoin construction. -/
noncomputable def assembleTextbookLocalSolution (hx : x ∈ A) :
    TextbookLocalSolution A R hR.2.2 step x where
  value := extendedLocalValue hR step children
  graph := extendedLocalGraph hR step children
  graph_eq := extendedLocalGraph_eq_restrictionGraph
    (hR := hR) (step := step) (children := children) hx
  satisfies := extendedLocalValue_satisfies
    (hR := hR) (step := step) (children := children) hx

end Glue

/-! ## Existence by the textbook local induction -/

/-- For every `x ∈ A`, an actual local solution graph on `d_x` exists.
The induction hypothesis supplies only local solutions at direct
predecessors.  The induction step is exactly the graph union and one-pair
extension developed above; no global recursion function occurs in the
proof. -/
theorem nonempty_textbookLocalSolution
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    ∀ x, x ∈ A → Nonempty (TextbookLocalSolution A R hR.2.2 step x) := by
  intro x hx
  let xA : {z : ZFSet.{u} // z ∈ A} := ⟨x, hx⟩
  change Nonempty (TextbookLocalSolution A R hR.2.2 step xA.1)
  apply (wellFounded_classRel_zfSubtype hR).induction
    (C := fun t => Nonempty
      (TextbookLocalSolution A R hR.2.2 step t.1)) xA
  intro t ih
  let children : ∀ y : ZFCarrier
      (displayedPredecessors A R hR.2.2 t.1),
      TextbookLocalSolution A R hR.2.2 step y.1 := fun y => by
    have hySpec := (displayedPredecessors_spec hR.2.2 t.2 y.1).mp y.2
    exact Classical.choice (ih ⟨y.1, hySpec.1⟩ hySpec.2)
  exact ⟨assembleTextbookLocalSolution
    (hR := hR) (step := step) (children := children) t.2⟩

/-- Existential form of the local-graph existence theorem. -/
theorem exists_textbookLocalSolution
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    ∃ solution : TextbookLocalSolution A R hR.2.2 step x,
      solution.graph = predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x) solution.value ∧
      SatisfiesTextbookLocalRecursion A R hR.2.2 step x
        solution.value := by
  let solution := Classical.choice
    (nonempty_textbookLocalSolution hR step x hx)
  exact ⟨solution, solution.graph_eq, solution.satisfies⟩

/-! ## Assembly of the global class function -/

/-- A chosen local solution at each point of `A`.  The existence source is
`nonempty_textbookLocalSolution`, proved above by the textbook local-graph
induction.  This is an ambient Lean choice of witnesses, not an assertion of
an object-theoretic choice function. -/
noncomputable def chosenTextbookLocalSolutionOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : {z : ZFSet.{u} // z ∈ A}) :
    TextbookLocalSolution A R hR.2.2 step x.1 :=
  Classical.choice (nonempty_textbookLocalSolution hR step x.1 x.2)

/-- The global class function assembled on page 108: for `x ∈ A`, set
`F(x) = f_x(x)`.  It is totalized by `∅` away from `A`, where its value has
no mathematical role. -/
noncomputable def textbookGlobalRecursionFromLocalGraphs
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ A then
    (chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩).value x
  else
    ∅

@[simp]
theorem textbookGlobalRecursionFromLocalGraphs_eq_on
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    textbookGlobalRecursionFromLocalGraphs hR step x =
      (chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩).value x := by
  simp [textbookGlobalRecursionFromLocalGraphs, hx]

@[simp]
theorem textbookGlobalRecursionFromLocalGraphs_eq_empty_of_not_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∉ A) :
    textbookGlobalRecursionFromLocalGraphs hR step x = ∅ := by
  simp [textbookGlobalRecursionFromLocalGraphs, hx]

/-- The assembled global function agrees on all of `d_x` with any local
solution at `x`.  At `t ∈ d_x`, the definition of the global function uses
the selected local solution `f_t`; textbook property (3) compares `f_t` and
the given `f_x` at the point `t ∈ d_x ∩ d_t`. -/
theorem textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x)
    {t : ZFSet.{u}}
    (ht : t ∈ localRecursionDomain A R hR.2.2 x) :
    textbookGlobalRecursionFromLocalGraphs hR step t = fx.value t := by
  have htA : t ∈ A := localRecursionDomain_subset hR.2.2 hx ht
  rw [textbookGlobalRecursionFromLocalGraphs_eq_on hR step htA]
  let ft := chosenTextbookLocalSolutionOn hR step ⟨t, htA⟩
  have hagree := textbookLocalSolutions_agreeOn_intersection
    hR hx htA fx ft t
      (ZFSet.mem_inter.mpr
        ⟨ht, mem_localRecursionDomain_iff.mpr (Or.inl rfl)⟩)
  exact hagree.symm

/-- On `d_x`, the actual restriction graph of the assembled global function
is exactly the actual local graph `f_x`. -/
theorem textbookGlobalRecursionFromLocalGraphs_restrictionGraph_eq_local
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x) :
    predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step) =
      fx.graph := by
  calc
    predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step) =
      predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x) fx.value := by
          apply predecessorRestrictionGraph_congr
          intro t ht
          exact textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
            hR step hx fx ht
    _ = fx.graph := fx.graph_eq.symm

/-- In particular, the global and local functions have equal actual graphs
on the immediate predecessor set of `x`. -/
theorem textbookGlobalRecursionFromLocalGraphs_predecessorGraph_eq_local
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x) :
    predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step) =
      predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) fx.value := by
  apply predecessorRestrictionGraph_congr
  intro t ht
  have htx := (displayedPredecessors_spec hR.2.2 hx t).mp ht |>.2
  have htDomain := localRecursionDomain_predecessorClosed
    hR.1 hR.2.2 hx
      (mem_localRecursionDomain_iff.mpr (Or.inl rfl)) htx
  exact textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
    hR step hx fx htDomain

/-! ## Existence and uniqueness of the global recursive function -/

/-- The global recursion equation, stated independently of any particular
construction.  This is definitionally the same mathematical condition as
the one used by the existing class-recursion module: the second argument of
`step` is the actual Kuratowski graph on the displayed full predecessor set. -/
def SatisfiesTextbookGlobalRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (F : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ x, x ∈ A →
    F x = step x (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike x) F)

/-- The function assembled solely from the local graphs satisfies the global
recursion equation. -/
theorem textbookGlobalRecursionFromLocalGraphs_satisfies
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    SatisfiesTextbookGlobalRecursion A R hR.2.2 step
      (textbookGlobalRecursionFromLocalGraphs hR step) := by
  intro x hx
  let fx := chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩
  have hxDomain : x ∈ localRecursionDomain A R hR.2.2 x :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  calc
    textbookGlobalRecursionFromLocalGraphs hR step x = fx.value x :=
      textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
        hR step hx fx hxDomain
    _ = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) fx.value) :=
      fx.satisfies x hxDomain
    _ = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step)) := by
      apply congrArg (step x)
      exact (textbookGlobalRecursionFromLocalGraphs_predecessorGraph_eq_local
        hR step hx fx).symm

/-- Uniqueness on `A`, proved by the previously established class-minimum
lemma.  The set/class of bad points is not assumed to be an object in a
model.  A minimal bad point has only good predecessors, so the two displayed
predecessor graphs and hence the recursive values coincide. -/
theorem satisfiesTextbookGlobalRecursion_uniqueOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {F H : ZFSet.{u} → ZFSet.{u}}
    (hF : SatisfiesTextbookGlobalRecursion A R hR.2.2 step F)
    (hH : SatisfiesTextbookGlobalRecursion A R hR.2.2 step H) :
    ∀ x, x ∈ A → F x = H x := by
  intro x hx
  by_contra hxNe
  let bad : Set ZFSet.{u} := {z | z ∈ A ∧ F z ≠ H z}
  have hbadSubset : bad ⊆ A := by
    intro z hz
    exact hz.1
  have hbadNonempty : bad.Nonempty := ⟨x, hx, hxNe⟩
  rcases hasClassMinimaOn_of_isWellFoundedSetLikeOn hR bad
      hbadSubset hbadNonempty with ⟨z, hzBad, hzMinimal⟩
  have hzEq : F z = H z := by
    rw [hF z hzBad.1, hH z hzBad.1]
    apply congrArg (step z)
    apply predecessorRestrictionGraph_congr
    intro y hy
    have hySpec :=
      (displayedPredecessors_spec hR.2.2 hzBad.1 y).mp hy
    by_contra hyNe
    exact hzMinimal y ⟨hySpec.1, hyNe⟩ hySpec.2
  exact hzBad.2 hzEq

/-- Existence and uniqueness on the intended class domain, with exactly the
same strength as the standard textbook class-recursion conclusion.  Values
of competing totalizations outside `A` are intentionally irrelevant. -/
theorem exists_uniqueOn_satisfiesTextbookGlobalRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    ∃ F : ZFSet.{u} → ZFSet.{u},
      SatisfiesTextbookGlobalRecursion A R hR.2.2 step F ∧
      ∀ H : ZFSet.{u} → ZFSet.{u},
        SatisfiesTextbookGlobalRecursion A R hR.2.2 step H →
        ∀ x, x ∈ A → F x = H x := by
  refine ⟨textbookGlobalRecursionFromLocalGraphs hR step,
    textbookGlobalRecursionFromLocalGraphs_satisfies hR step, ?_⟩
  intro H hH
  exact satisfiesTextbookGlobalRecursion_uniqueOn hR
    (textbookGlobalRecursionFromLocalGraphs_satisfies hR step) hH

end

end Constructible
