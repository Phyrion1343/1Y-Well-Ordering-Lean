/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaGodel
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryClosureConstructible

/-!
# Full elementarity from closure under rudimentary relations

For a transitive set `U`, every positive-arity first-order formula has a
relation representation whose underlying set belongs to
`rudimentaryClosure U`.  Hence unrestricted relation closure implies full
elementarity.  This is only a semantic sufficient condition, not a
cardinality-controlled Skolem-hull construction: nullary singleton relations
in `rudimentaryClosure U` force any such closed carrier to contain all of
`U`.  A small hull must instead enumerate only formula-compiled relations.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

open Godel

/--
Uniform witness closure for every relation in `rudimentaryClosure U`.
The natural number `n` records the number of parameters before the witness.
This predicate is deliberately not advertised as a small-hull invariant; its
nullary instances imply `U ⊆ small`.
-/
def ClosesUnderRudimentaryRelations
    (small : Set ZFSet.{u}) (U : ZFSet.{u}) : Prop :=
  forall (n : Nat) (relation : ZFSet.{u}),
    relation ∈ rudimentaryClosure U ->
      forall s : Tuple ZFSet.{u} n,
        (forall i, s i ∈ small) ->
        (exists x : ZFSet.{u}, x ∈ U /\
          positiveTupleCode n (snoc s x) ∈ relation) ->
        exists x : ZFSet.{u}, x ∈ small /\
          positiveTupleCode n (snoc s x) ∈ relation

private theorem satisfiesIn_iff_formulaRep
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) (hs : forall i, s i ∈ U)
    (x : ZFSet.{u}) (hx : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u}) phi (snoc s x) <->
      positiveTupleCode n (snoc s x) ∈ (formulaRep U hU phi).set := by
  let sU : Tuple (ZFCarrier U) n := fun i => ⟨s i, hs i⟩
  let xU : ZFCarrier U := ⟨x, hx⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) phi (snoc sU xU)
  have hvalues :
      (fun i => ((snoc sU xU) i).1) = snoc s x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · rfl
  have hsemantics :
      FOFormula.Satisfies (zfCarrierMem U) phi (snoc sU xU) <->
        Model.SatisfiesIn (U : Set ZFSet.{u}) phi (snoc s x) := by
    simpa only [hvalues] using hbridge
  have hcode := (formulaRep U hU phi).correct (snoc sU xU)
  have hcodeRaw :
      positiveTupleCode n (snoc s x) ∈ (formulaRep U hU phi).set <->
        FOFormula.Satisfies (zfCarrierMem U) phi (snoc sU xU) := by
    simpa only [Delta0Formula.val_snoc, sU, xU] using hcode
  exact hsemantics.symm.trans hcodeRaw.symm

/-- Closure under the single internal set of all rudimentary relation
outputs implies Tarski--Vaught closure for every first-order formula. -/
theorem closesWithinAll_of_closesUnderRudimentaryRelations
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hU : U.IsTransitive)
    (hrelations : ClosesUnderRudimentaryRelations small U) :
    ClosesWithinAll small (U : Set ZFSet.{u}) := by
  intro n phi
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ⟨ihPhi, ihPsi⟩
  | @ex n phi ih =>
      refine ⟨ih, ?_⟩
      intro s hs hex
      rcases hex with ⟨x, hxU, hxFormula⟩
      let relation := (formulaRep U hU phi).set
      have hcode : positiveTupleCode n (snoc s x) ∈ relation :=
        (satisfiesIn_iff_formulaRep hU phi s
          (fun i => hsubset (hs i)) x hxU).mp hxFormula
      rcases hrelations n relation (formulaRep U hU phi).set_mem
          s hs ⟨x, hxU, hcode⟩ with ⟨y, hySmall, hyCode⟩
      refine ⟨y, hySmall, ?_⟩
      exact (satisfiesIn_iff_formulaRep hU phi s
        (fun i => hsubset (hs i)) y (hsubset hySmall)).mpr hyCode

/-- The same relation-closure hypothesis yields full satisfaction
absoluteness, not merely absoluteness for a chosen fragment. -/
theorem satisfactionAbsolute_of_closesUnderRudimentaryRelations
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hU : U.IsTransitive)
    (hrelations : ClosesUnderRudimentaryRelations small U) :
    SatisfactionAbsolute small (U : Set ZFSet.{u}) :=
  satisfactionAbsolute_of_closesWithinAll hsubset
    (closesWithinAll_of_closesUnderRudimentaryRelations
      hsubset hU hrelations)

end ZFC

end Constructible
