/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiCollapse

/-!
# Satisfaction through the Mostowski collapse

The Mostowski collapse is not used only as an extensional membership
isomorphism here.  This file proves, by induction on the complete independent
syntax `FOFormula`, that the collapse preserves satisfaction of every formula.
Consequently a fully elementary set-sized hull and its transitive collapse
have exactly the same first-order theory with corresponding parameters.
-/

@[expose] public section

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

private theorem equivRange_comp_snoc
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat}
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n)
    (x : {x : ZFSet.{u} // x ∈ domain}) :
    (fun i => equivRange hextensional (snoc s x i)) =
      snoc (fun i => equivRange hextensional (s i))
        (equivRange hextensional x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [snoc_last]
  · simp only [snoc_castSucc]

/-- The Mostowski equivalence preserves satisfaction of every first-order
formula, not merely atomic membership. -/
theorem satisfies_equivRange_iff
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat} (phi : FOFormula n)
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n) :
    FOFormula.Satisfies
        (fun x y : {x : ZFSet.{u} // x ∈ domain} => x.1 ∈ y.1)
        phi s ↔
      FOFormula.Satisfies
        (fun x y : {x : ZFSet.{u} // x ∈ range domain} => x.1 ∈ y.1)
        phi (fun i => equivRange hextensional (s i)) := by
  induction phi with
  | mem i j =>
      exact (equivRange_mem_iff hextensional (s i) (s j)).symm
  | eq i j =>
      constructor
      · intro h
        exact congrArg (equivRange hextensional) h
      · intro h
        exact (equivRange hextensional).injective h
  | neg phi ih =>
      exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨equivRange hextensional x, ?_⟩
        have hmapped := (ih (snoc s x)).mp hx
        simpa only [equivRange_comp_snoc] using hmapped
      · rintro ⟨z, hz⟩
        let x := (equivRange hextensional).symm z
        refine ⟨x, ?_⟩
        apply (ih (snoc s x)).mpr
        have hmapX : equivRange hextensional x = z := by
          exact (equivRange hextensional).apply_symm_apply z
        simpa only [equivRange_comp_snoc, hmapX] using hz

/-- Raw-value form of `satisfies_equivRange_iff`.  The tuple on the right is
obtained by applying the collapse to every entry of the tuple on the left. -/
theorem satisfiesIn_collapse_iff
    {domain : ZFSet.{u}} (hextensional : IsExtensional domain)
    {n : Nat} (phi : FOFormula n)
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n) :
    Model.SatisfiesIn (domain : Set ZFSet.{u}) phi
        (fun i => (s i).1) ↔
      Model.SatisfiesIn (range domain : Set ZFSet.{u}) phi
        (fun i => collapse domain (s i).1) := by
  have hdomain := Model.satisfies_subtype_iff_satisfiesIn
    (domain : Set ZFSet.{u}) phi s
  let mapped : Tuple {z : ZFSet.{u} // z ∈ range domain} n :=
    fun i => equivRange hextensional (s i)
  have hrange := Model.satisfies_subtype_iff_satisfiesIn
    (range domain : Set ZFSet.{u}) phi mapped
  have hisomorphism := satisfies_equivRange_iff hextensional phi s
  constructor
  · intro h
    have hsource := hdomain.mpr h
    have htarget := hisomorphism.mp hsource
    have hraw := hrange.mp htarget
    simpa only [mapped, equivRange_apply] using hraw
  · intro h
    apply hdomain.mp
    apply hisomorphism.mpr
    apply hrange.mpr
    simpa only [mapped, equivRange_apply] using h

/-- Full elementarity of a hull transfers to its transitive collapse.  The
comparison with the ambient carrier uses the inverse collapse image of each
parameter tuple; no inclusion of the collapsed range in the ambient carrier
is asserted. -/
theorem satisfiesIn_range_iff_of_satisfactionAbsolute
    {domain : ZFSet.{u}} {big : Set ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (habsolute : SatisfactionAbsolute (domain : Set ZFSet.{u}) big)
    {n : Nat} (phi : FOFormula n)
    (s : Tuple {x : ZFSet.{u} // x ∈ domain} n) :
    Model.SatisfiesIn (range domain : Set ZFSet.{u}) phi
        (fun i => collapse domain (s i).1) ↔
      Model.SatisfiesIn big phi (fun i => (s i).1) := by
  rw [← satisfiesIn_collapse_iff hextensional phi s]
  exact habsolute phi (fun i => (s i).1) (fun i => (s i).2)

end

end Constructible.MostowskiCollapse
