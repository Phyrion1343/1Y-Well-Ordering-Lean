/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareGodelDefAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageCorrect
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryGlobal
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationOmega

/-!
# The standard Condensation Lemma for constructible limit levels

For every nonzero limit ordinal `theta`, the Mostowski collapse of a
set-sized fully elementary membership substructure of `L_theta` is exactly
the constructible level indexed by the ordinal height of the collapse.

The proof separates the exceptional first limit `theta = omega`, where
`L_omega` is hereditarily finite, from the case `omega < theta`.  In the
second case, local correctness of the relation-free stage predicate follows
from the proved Goedel-evaluator absoluteness theorem and the unconditional
canonical-history bound.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The ordinal height of the first infinite constructible level is exactly
`omega`. -/
theorem ordinalHeight_LStageZF_omega0 :
    ordinalHeight (LStageZF (Ordinal.omega0 : Ordinal.{u})) =
      Ordinal.omega0 := by
  apply le_antisymm
  · unfold ordinalHeight
    apply Ordinal.iSup_le
    intro x
    split_ifs with hx
    · exact Order.succ_le_iff.mpr
        ((ordinal_stage_invariants
          (Ordinal.omega0 : Ordinal.{u})).1 hx x.2)
    · exact bot_le
  · rw [Ordinal.omega0_le]
    intro n
    exact (lt_ordinalHeight_of_mem
      (ordinal_toZFSet_mem_LStageZF_of_lt
        (Ordinal.natCast_lt_omega0 n))).le

/--
The standard Condensation Lemma at an arbitrary nonzero limit level.

`SatisfactionAbsolute domain (LStageZF theta)` is full first-order
elementarity for membership, with all free parameters in `domain`.  The
conclusion identifies the collapse with the precise level determined by its
ordinal height; no reflection-level or evaluator hypothesis is exposed.
-/
theorem condensation_of_elementary_isSuccLimit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    range domain = LStageZF (ordinalHeight (range domain)) := by
  by_cases hthetaOmega : theta = Ordinal.omega0
  · subst theta
    have hrange :
        range domain =
          LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
      condensation_of_elementary_omega hsubset helem
    rw [hrange, ordinalHeight_LStageZF_omega0]
  · have homega : Ordinal.omega0 < theta :=
      lt_of_le_of_ne (Ordinal.omega0_le_of_isSuccLimit htheta)
        (Ne.symm hthetaOmega)
    have hcorrect : BareStageCondensation.BareStageCorrectAt theta :=
      BareStageCondensation.bareStageCorrectAt_of_evaluator_and_history_bounds
        htheta homega
        (Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
          htheta homega)
        Model.canonicalBareHistory_mem_LStageZF_add_omega
    exact
      (BareStageCondensation.stageInterfaces_of_bareStageCorrect
        htheta homega hsubset helem hcorrect).range_eq_LStageZF_ordinalHeight

/-- Existential form of the standard Condensation Lemma. -/
theorem exists_collapse_eq_LStageZF_of_elementary_isSuccLimit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    ∃ beta : Ordinal.{u}, range domain = LStageZF beta :=
  ⟨ordinalHeight (range domain),
    condensation_of_elementary_isSuccLimit htheta hsubset helem⟩

end

end MostowskiCollapse

end Constructible
