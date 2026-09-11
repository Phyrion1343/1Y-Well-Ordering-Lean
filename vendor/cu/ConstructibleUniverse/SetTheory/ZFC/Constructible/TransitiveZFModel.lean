/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.ModelTheory.SetTheory.ZF
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Absoluteness

/-!
# Transitive set models of ZF

This file packages the standard set-model hypotheses used in the textbook
development of absoluteness.  The carrier `M` is a genuine `ZFSet`.
`ZFCarrier M` is the Lean subtype of its members, equipped with ambient
membership, while `(M : Set ZFSet)` is only the corresponding external
membership predicate.

The model predicate contains exactly two mathematical assumptions:
transitivity of `M` and satisfaction of the full first-order theory ZF by
the inherited membership structure.  In particular, no Choice axiom,
recursive closure, or absoluteness conclusion is built into the definition.

The remaining results are representation bridges.  They identify the
intrinsically scoped `FOFormula` semantics, Mathlib bounded-formula
semantics, and raw-domain `SatisfiesIn` semantics on the same carrier.  These
bridges require neither transitivity nor the ZF model hypothesis.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

/-! ## The standard transitive-set-model predicate -/

/--
The internal set `M`, with membership inherited from ambient `ZFSet`, models
the full first-order theory ZF.

The structure instance is local to this proposition.  This avoids installing
a competing global structure on the reducible subtype `ZFCarrier M`.
-/
def ZFSetModelsZF (M : ZFSet.{u}) : Prop :=
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF

/-- A standard transitive set model of ZF, stated without hidden closure. -/
def IsTransitiveZFModel (M : ZFSet.{u}) : Prop :=
  M.IsTransitive ∧ ZFSetModelsZF M

/-! ## Formula-semantics bridges -/

/--
Satisfaction on the subtype of members of an internal `ZFSet` agrees with
raw satisfaction whose quantifiers are restricted to that set.
-/
@[simp]
theorem satisfies_zfCarrier_iff_satisfiesIn (M : ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) (s : Tuple (ZFCarrier M) n) :
    FOFormula.Satisfies (zfCarrierMem M) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1) := by
  change
    FOFormula.Satisfies (fun x y : ZFCarrier M => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1)
  exact satisfies_subtype_iff_satisfiesIn
    (M : Set ZFSet.{u}) phi s

/--
Forward syntax bridge: translating an `FOFormula` to Mathlib's bounded
formula syntax and realizing it on `ZFCarrier M` is the same as restricted
raw satisfaction in `M`.
-/
@[simp]
theorem realizes_toBoundedFormula_zfCarrier_iff_satisfiesIn
    (M : ZFSet.{u}) {n : Nat} (phi : FOFormula n)
    (s : Tuple (ZFCarrier M) n) :
    realizes (zfCarrierMem M) (toBoundedFormula phi) s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1) := by
  exact (realizes_toBoundedFormula (zfCarrierMem M) phi s).trans
    (satisfies_zfCarrier_iff_satisfiesIn M phi s)

/--
Reverse syntax bridge: every Mathlib bounded formula in the function-free
membership language has the same restricted semantics as its normalization
to `FOFormula`.
-/
@[simp]
theorem realizes_zfCarrier_iff_satisfiesIn_fromBoundedFormula
    (M : ZFSet.{u}) {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Tuple (ZFCarrier M) n) :
    realizes (zfCarrierMem M) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) (fromBoundedFormula phi)
        (fun i => (s i).1) := by
  exact (realize_fromBoundedFormula (zfCarrierMem M) phi s).trans
    (satisfies_zfCarrier_iff_satisfiesIn M
      (fromBoundedFormula phi) s)

end Model

end Constructible
