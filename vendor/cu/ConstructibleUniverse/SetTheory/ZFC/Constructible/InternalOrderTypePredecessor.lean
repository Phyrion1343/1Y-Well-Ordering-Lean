/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentatives
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Separation

/-!
# Internal predecessor sets for an represented relation

This is the Separation part of the order-type construction.  It constructs
an actual `LCarrier` predecessor set from an internally represented relation
graph.  The order-type ordinal and its isomorphism graph are separate
well-founded-recursion obligations and are intentionally not assumed here.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-- Formula with layout `[relation, domain, point, z]` selecting a predecessor. -/
def predecessorMembershipAt : FOFormula 4 :=
  .conj
    (.mem (3 : Fin 4) (1 : Fin 4))
    (graphValueAt (0 : Fin 4) (3 : Fin 4) (2 : Fin 4))

private theorem predecessorMembershipAt_assignment
    (relation domain point z : LCarrier.{u}) :
    snoc ![relation, domain, point] z = ![relation, domain, point, z] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_predecessorMembershipAt
    (relation domain point z : LCarrier.{u}) :
    FOFormula.Satisfies LMem predecessorMembershipAt
        ![relation, domain, point, z] <->
      z.1 ∈ domain.1 /\ GraphValue LMem relation z point := by
  simp [predecessorMembershipAt, FOFormula.Satisfies,
    satisfies_graphValueAt]

/-- Separation produces the exact internal predecessor set. -/
theorem exists_internalPredecessorSet
    (relation domain point : LCarrier.{u}) :
    exists predecessors : LCarrier.{u},
      IsPredecessorSetOf LMem predecessors relation domain point := by
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  rcases Model.exists_separationLCarrier predecessorMembershipAt params domain with
    ⟨predecessors, hpred⟩
  refine ⟨predecessors, ?_⟩
  intro z
  change z.1 ∈ predecessors.1 <->
    z.1 ∈ domain.1 /\ GraphValue LMem relation z point
  rw [hpred z, predecessorMembershipAt_assignment relation domain point z,
    satisfies_predecessorMembershipAt]
  simp

end Constructible.ContinuumFormula
