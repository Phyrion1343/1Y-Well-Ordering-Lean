/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFModel

/-!
# Formula bridge for the ZF axiom schemes

The construction syntax `FOFormula n` treats its `n` variables as one scoped
tuple.  The Separation and Replacement schemes in `Theory.ZF` instead use
Mathlib formulas whose variables are free variables indexed by `Fin n`.
This file moves the same variables between those two presentations and proves
that realization is unchanged.

This is only a syntax/semantics theorem.  It does not assert that an ambient
separation or replacement result belongs to a particular model.
-/

@[expose] public section

universe u

namespace Constructible.Model

/-- Turn the scoped variables of an `FOFormula` into Mathlib free variables,
as required by the formulas indexing the ZF axiom schemes. -/
def toSchemeFormula {n : Nat} (phi : FOFormula n) :
    FirstOrder.Language.setTheory.Formula (Fin n) :=
  (toBoundedFormula phi).toFormula.relabel
    (Sum.elim Empty.elim id)

/-- Moving all scoped variables to free-variable positions preserves the
independent `FOFormula` satisfaction semantics. -/
@[simp]
theorem realize_toSchemeFormula {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (phi : FOFormula n) (s : Tuple A n) :
    letI : FirstOrder.Language.setTheory.Structure A :=
      FirstOrder.Language.setTheoryStructure E
    (toSchemeFormula phi).Realize s <->
      FOFormula.Satisfies E phi s := by
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  rw [toSchemeFormula, FirstOrder.Language.Formula.realize_relabel,
    FirstOrder.Language.BoundedFormula.realize_toFormula]
  have hfree :
      (s ∘ Sum.elim Empty.elim id) ∘ Sum.inl =
        (Empty.elim : Empty -> A) := by
    funext i
    exact Empty.elim i
  have hscoped :
      (s ∘ Sum.elim Empty.elim id) ∘ Sum.inr = s := by
    funext i
    rfl
  rw [hfree, hscoped]
  exact realizes_toBoundedFormula E phi s

end Constructible.Model
