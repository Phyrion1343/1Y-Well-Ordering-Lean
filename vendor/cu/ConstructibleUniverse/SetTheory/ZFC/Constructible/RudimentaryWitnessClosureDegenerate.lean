/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull

/-!
# Degeneracy of unrestricted rudimentary-witness closure

Quantifying over every member of `rudimentaryClosure U` is too strong for a
cardinality-controlled Skolem hull.  Every singleton of a member of `U` is in
that closure.  The nullary instance of `ClosesUnderRudimentaryWitnesses`
therefore forces every member of `U` into the purported smaller carrier.

The implication from this predicate to elementarity remains logically valid,
but the predicate must not be used as the closure invariant in a downward
Loewenheim--Skolem or Condensation argument.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-- Unrestricted rudimentary-witness closure already contains all of `U`.
No assumed inclusion in the other direction is needed.
-/
theorem subset_of_closesUnderRudimentaryWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hclose : ClosesUnderRudimentaryWitnesses small U) :
    (U : Set ZFSet.{u}) ⊆ small := by
  intro z hzU
  let relation := Godel.F0 z z
  have hzClosure : z ∈ Godel.rudimentaryClosure U :=
    Godel.subset_rudimentaryClosure U hzU
  have hrelation : relation ∈ Godel.rudimentaryClosure U := by
    exact Godel.F0_mem_rudimentaryClosure hzClosure hzClosure
  let params : Tuple (ZFCarrier U) 0 := fun i => Fin.elim0 i
  let zU : ZFCarrier U := ⟨z, hzU⟩
  have hexists :
      ∃ x : ZFCarrier U,
        Godel.positiveTupleCode 0
          (Delta0Formula.val (snoc params x)) ∈ relation := by
    refine ⟨zU, ?_⟩
    have hcode :
        Godel.positiveTupleCode 0
            (Delta0Formula.val (snoc params zU)) = z := by
      simp only [Delta0Formula.val_snoc, Godel.positiveTupleCode]
      rw [show (0 : Fin 1) = Fin.last 0 from Subsingleton.elim _ _,
        snoc_last]
    rw [hcode]
    simp [relation, Godel.F0]
  rcases hclose relation hrelation params (fun i => Fin.elim0 i)
      hexists with ⟨x, hxSmall, hxRelation⟩
  have hxEq : x.1 = z := by
    have hcode :
        Godel.positiveTupleCode 0
            (Delta0Formula.val (snoc params x)) = x.1 := by
      simp only [Delta0Formula.val_snoc, Godel.positiveTupleCode]
      rw [show (0 : Fin 1) = Fin.last 0 from Subsingleton.elim _ _,
        snoc_last]
    have hxRelation' : x.1 ∈ relation := hcode ▸ hxRelation
    simpa [relation, Godel.F0] using hxRelation'
  simpa only [hxEq] using hxSmall

/-- With the usual hull inclusion `small ⊆ U`, unrestricted rudimentary
witness closure is exactly the whole ambient structure.
-/
theorem eq_of_closesUnderRudimentaryWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderRudimentaryWitnesses small U) :
    small = (U : Set ZFSet.{u}) :=
  Set.Subset.antisymm hsubset
    (subset_of_closesUnderRudimentaryWitnesses hclose)

end ZFC

end Constructible
