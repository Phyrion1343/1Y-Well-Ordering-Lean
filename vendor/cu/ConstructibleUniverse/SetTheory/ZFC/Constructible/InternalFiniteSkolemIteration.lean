/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.AritySeparatedFormulaSkolemStep

/-!
# Internally represented finite Skolem iteration

This file iterates the branch-exact one-formula operation from
`AritySeparatedFormulaSkolemStep` over an explicitly supplied finite list of
existential matrices.  Every pass and every finite stage has type `LCarrier`,
so the invariant that the external carrier is represented by an actual
constructible `ZFSet` is retained.  Nullary matrices use only the nullary
selector, while positive-arity matrices use only the parameter-prefix fiber
selector.

The natural-number stage function is still an external Lean function.  This
file does not claim that its range has been collected inside the model by
Replacement, does not form an internal omega union, and does not prove full
elementarity.  Those steps require a single object-language formula defining
the stage graph uniformly, together with an internal enumeration of all
first-order formulas.

The membership semantics of each one-formula operation is exact, as recorded
by the zero/successor theorems in `AritySeparatedFormulaSkolemStep`.  This
file proves finite-pass witness closure and containment.  It does not by
itself construct a single internal graph for the whole pass or assert a sharp
cardinality bound; those require the later uniform coding and Replacement
arguments.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-- An existential matrix `phi(params, y)` together with its parameter
arity. -/
abbrev InternalSkolemMatrix : Type :=
  Sigma fun n : Nat => FOFormula (n + 1)

/-- Apply the one-formula witness step successively to a finite list.  The
result remains an `LCarrier` at every recursive call. -/
noncomputable def internalFormulaSkolemPass
    (U : LCarrier.{u}) (hU : U.1.IsTransitive) :
    List InternalSkolemMatrix -> LCarrier.{u} -> LCarrier.{u}
  | [], seed => seed
  | matrix :: rest, seed =>
      internalFormulaSkolemPass U hU rest
        (aritySeparatedFormulaSkolemStep seed U hU matrix.2)

@[simp]
theorem internalFormulaSkolemPass_nil
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (seed : LCarrier.{u}) :
    internalFormulaSkolemPass U hU [] seed = seed :=
  rfl

@[simp]
theorem internalFormulaSkolemPass_cons
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrix : InternalSkolemMatrix)
    (rest : List InternalSkolemMatrix) (seed : LCarrier.{u}) :
    internalFormulaSkolemPass U hU (matrix :: rest) seed =
      internalFormulaSkolemPass U hU rest
        (aritySeparatedFormulaSkolemStep seed U hU matrix.2) :=
  rfl

/-- A finite pass retains every member of its input seed. -/
theorem seed_subset_internalFormulaSkolemPass
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u}) :
    seed.1 ⊆ (internalFormulaSkolemPass U hU matrices seed).1 := by
  induction matrices generalizing seed with
  | nil => exact Set.Subset.rfl
  | cons matrix rest ih =>
      exact (seed_subset_aritySeparatedFormulaSkolemStep
        seed U hU matrix.2).trans
          (ih (aritySeparatedFormulaSkolemStep seed U hU matrix.2))

/-- If the input seed lies in `U`, the whole finite pass lies in `U`. -/
theorem internalFormulaSkolemPass_subset
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1) :
    (internalFormulaSkolemPass U hU matrices seed).1 ⊆ U.1 := by
  induction matrices generalizing seed with
  | nil => exact hseed
  | cons matrix rest ih =>
      exact ih (aritySeparatedFormulaSkolemStep seed U hU matrix.2)
        (aritySeparatedFormulaSkolemStep_subset hU hseed matrix.2)

/-- If a matrix occurs in the displayed finite list, one pass supplies a
witness for every parameter tuple from the input seed whenever the ambient
set supplies one. -/
theorem exists_witness_mem_internalFormulaSkolemPass_of_mem
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (matrix : InternalSkolemMatrix) (hmatrix : matrix ∈ matrices)
    (params : Tuple (ZFCarrier U.1) matrix.1)
    (hparams : ∀ i, (params i).1 ∈ seed.1)
    (hexists : ∃ x : ZFCarrier U.1,
      FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
        (snoc params x)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈ (internalFormulaSkolemPass U hU matrices seed).1 ∧
        FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
          (snoc params y) := by
  induction matrices generalizing seed with
  | nil => simp at hmatrix
  | cons head rest ih =>
      rw [List.mem_cons] at hmatrix
      rcases hmatrix with rfl | hmatrix
      · rcases exists_witness_mem_aritySeparatedFormulaSkolemStep
          hU matrix.2 params hparams hexists with
          ⟨y, hyStep, hySat⟩
        refine ⟨y, ?_, hySat⟩
        exact seed_subset_internalFormulaSkolemPass U hU rest
          (aritySeparatedFormulaSkolemStep seed U hU matrix.2) hyStep
      · refine ih
          (seed := aritySeparatedFormulaSkolemStep seed U hU head.2)
          hmatrix ?_
        intro i
        exact seed_subset_aritySeparatedFormulaSkolemStep
          seed U hU head.2 (hparams i)

/-- Repeat one finite pass through externally indexed natural-number
stages.  Each value is nevertheless an actual member of `L`. -/
noncomputable def internalFormulaSkolemStage
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u}) :
    Nat -> LCarrier.{u}
  | 0 => seed
  | n + 1 => internalFormulaSkolemPass U hU matrices
      (internalFormulaSkolemStage U hU matrices seed n)

@[simp]
theorem internalFormulaSkolemStage_zero
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u}) :
    internalFormulaSkolemStage U hU matrices seed 0 = seed :=
  rfl

@[simp]
theorem internalFormulaSkolemStage_succ
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (n : Nat) :
    internalFormulaSkolemStage U hU matrices seed (n + 1) =
      internalFormulaSkolemPass U hU matrices
        (internalFormulaSkolemStage U hU matrices seed n) :=
  rfl

/-- Every finite stage is contained in its successor. -/
theorem internalFormulaSkolemStage_subset_succ
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (n : Nat) :
    (internalFormulaSkolemStage U hU matrices seed n).1 ⊆
      (internalFormulaSkolemStage U hU matrices seed (n + 1)).1 := by
  exact seed_subset_internalFormulaSkolemPass U hU matrices
    (internalFormulaSkolemStage U hU matrices seed n)

/-- The externally indexed finite-stage sequence is monotone. -/
theorem internalFormulaSkolemStage_mono
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    {m n : Nat} (hmn : m ≤ n) :
    (internalFormulaSkolemStage U hU matrices seed m).1 ⊆
      (internalFormulaSkolemStage U hU matrices seed n).1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans
        (internalFormulaSkolemStage_subset_succ U hU matrices seed n)

/-- If the initial seed lies in `U`, every finite stage lies in `U`. -/
theorem internalFormulaSkolemStage_subset
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1) (n : Nat) :
    (internalFormulaSkolemStage U hU matrices seed n).1 ⊆ U.1 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      exact internalFormulaSkolemPass_subset U hU matrices
        (internalFormulaSkolemStage U hU matrices seed n) ih

/-- At the successor of any stage, each listed matrix has the required
witnesses for parameter tuples from the preceding stage. -/
theorem exists_witness_mem_internalFormulaSkolemStage_succ_of_mem
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u})
    (stage : Nat) (matrix : InternalSkolemMatrix)
    (hmatrix : matrix ∈ matrices)
    (params : Tuple (ZFCarrier U.1) matrix.1)
    (hparams : ∀ i,
      (params i).1 ∈
        (internalFormulaSkolemStage U hU matrices seed stage).1)
    (hexists : ∃ x : ZFCarrier U.1,
      FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
        (snoc params x)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈
          (internalFormulaSkolemStage U hU matrices seed (stage + 1)).1 ∧
        FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
          (snoc params y) := by
  exact exists_witness_mem_internalFormulaSkolemPass_of_mem
    U hU matrices
    (internalFormulaSkolemStage U hU matrices seed stage)
    matrix hmatrix params hparams hexists

end

end Constructible.Model
