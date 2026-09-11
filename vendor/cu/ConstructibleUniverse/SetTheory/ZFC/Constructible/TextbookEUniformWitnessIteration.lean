/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessStepFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.UniformFiniteIterationFormula

/-!
# The internal omega iteration of the uniform textbook E witness step

The simultaneous witness operation from
`TextbookEUniformWitnessStepFormula` is defined by one fixed first-order
formula.  This file applies the general finite-iteration formula to that
operation, uses Replacement over the genuine internal omega, and takes the
internal union of the resulting family.

The final closure proof is the standard finite-tuple maximum-stage argument:
each parameter occurs at a finite stage, all parameters occur together at
their maximum stage, and the next stage supplies the requested witness.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Exact finite iteration -/

/-- The four fixed parameters of the simultaneous witness-step formula. -/
def textbookEUniformWitnessStepParameters
    (U : LCarrier.{u}) : Tuple LCarrier.{u} 4 :=
  ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain, omegaLCarrier]

/-- The fixed step formula defines exactly the simultaneous witness step. -/
theorem textbookEUniformWitnessStep_definesFiniteIterationStep
    (U : LCarrier.{u}) :
    DefinesFiniteIterationStep textbookEUniformWitnessStepFormula
      (textbookEUniformWitnessStepParameters U)
      (fun current => textbookEUniformWitnessStep current U) := by
  intro current next
  have hassignment :
      snoc
          (snoc (textbookEUniformWitnessStepParameters U) current)
          next =
        ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain,
          omegaLCarrier, current, next] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  exact satisfies_textbookEUniformWitnessStepFormula_iff U current next

/-- The standard finite iteration beginning with `seed`. -/
def textbookEUniformWitnessStage
    (seed U : LCarrier.{u}) : Nat -> LCarrier.{u} :=
  uniformFiniteIterate
    (fun current => textbookEUniformWitnessStep current U) seed

@[simp]
theorem textbookEUniformWitnessStage_zero
    (seed U : LCarrier.{u}) :
    textbookEUniformWitnessStage seed U 0 = seed :=
  rfl

@[simp]
theorem textbookEUniformWitnessStage_succ
    (seed U : LCarrier.{u}) (n : Nat) :
    textbookEUniformWitnessStage seed U (n + 1) =
      textbookEUniformWitnessStep
        (textbookEUniformWitnessStage seed U n) U :=
  rfl

/-- Each finite stage is contained in its successor. -/
theorem textbookEUniformWitnessStage_subset_succ
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆
      (textbookEUniformWitnessStage seed U (n + 1)).1 := by
  exact seed_subset_textbookEUniformWitnessStep
    (textbookEUniformWitnessStage seed U n) U

/-- The finite-stage sequence is monotone. -/
theorem textbookEUniformWitnessStage_mono
    (seed U : LCarrier.{u}) {m n : Nat} (hmn : m ≤ n) :
    (textbookEUniformWitnessStage seed U m).1 ⊆
      (textbookEUniformWitnessStage seed U n).1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans
        (textbookEUniformWitnessStage_subset_succ seed U n)

/-- If `seed` is contained in `U` and the empty set belongs to `U`, every
finite stage remains contained in `U`. -/
theorem textbookEUniformWitnessStage_subset
    (seed U : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1)
    (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆ U.1 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      exact textbookEUniformWitnessStep_subset ih hempty

/-! ## The internal omega family and its union -/

/--
The fixed finite-history formula, with parameters
`[U, canonicalWitnessOrder U, textbookEWitnessTaskDomain, omega, seed]`,
uniformly defines all finite stages.
-/
noncomputable def textbookEUniformWitnessOmegaFamilySpec
    (seed U : LCarrier.{u}) :
    ParametricUniformOmegaFamilySpec.{u} 5 :=
  uniformFiniteIterationOmegaFamilySpec
    textbookEUniformWitnessStepFormula
    (textbookEUniformWitnessStepParameters U)
    (fun current => textbookEUniformWitnessStep current U)
    seed
    (textbookEUniformWitnessStep_definesFiniteIterationStep U)

@[simp]
theorem textbookEUniformWitnessOmegaFamilySpec_value
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessOmegaFamilySpec seed U).value n =
      textbookEUniformWitnessStage seed U n :=
  rfl

/-- The actual internal union of the Replacement-collected finite stages. -/
noncomputable def textbookEUniformWitnessOmegaUnion
    (seed U : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion
    (textbookEUniformWitnessOmegaFamilySpec seed U)

@[simp]
theorem mem_textbookEUniformWitnessOmegaUnion_iff
    (seed U z : LCarrier.{u}) :
    z.1 ∈ (textbookEUniformWitnessOmegaUnion seed U).1 ↔
      ∃ n : Nat,
        z.1 ∈ (textbookEUniformWitnessStage seed U n).1 := by
  rw [textbookEUniformWitnessOmegaUnion,
    mem_parametricUniformOmegaUnion_iff]
  rfl

/-- Every finite stage is contained in the internally collected union. -/
theorem textbookEUniformWitnessStage_subset_omegaUnion
    (seed U : LCarrier.{u}) (n : Nat) :
    (textbookEUniformWitnessStage seed U n).1 ⊆
      (textbookEUniformWitnessOmegaUnion seed U).1 := by
  simpa only [textbookEUniformWitnessOmegaUnion,
    textbookEUniformWitnessOmegaFamilySpec_value] using
    value_subset_parametricUniformOmegaUnion
      (textbookEUniformWitnessOmegaFamilySpec seed U) n

/-- The internally collected omega union contains the initial seed. -/
theorem seed_subset_textbookEUniformWitnessOmegaUnion
    (seed U : LCarrier.{u}) :
    seed.1 ⊆ (textbookEUniformWitnessOmegaUnion seed U).1 := by
  simpa only [textbookEUniformWitnessStage_zero] using
    textbookEUniformWitnessStage_subset_omegaUnion seed U 0

/-- Under the natural ambient hypotheses, the omega union remains in `U`. -/
theorem textbookEUniformWitnessOmegaUnion_subset
    (seed U : LCarrier.{u})
    (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1) :
    (textbookEUniformWitnessOmegaUnion seed U).1 ⊆ U.1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (textbookEUniformWitnessOmegaUnion seed U).2⟩
  rcases
      (mem_textbookEUniformWitnessOmegaUnion_iff seed U zL).mp hz with
    ⟨n, hzn⟩
  exact textbookEUniformWitnessStage_subset seed U hseed hempty n hzn

/-! ## The finite-tuple maximum-stage argument -/

/-- Every finite tuple from the omega union occurs together in one finite
stage. -/
theorem exists_textbookEUniformWitnessStage_for_tuple
    (seed U : LCarrier.{u})
    {arity : Nat} (params : Tuple (ZFCarrier U.1) arity)
    (hparams : ∀ i,
      (params i).1 ∈ (textbookEUniformWitnessOmegaUnion seed U).1) :
    ∃ stage : Nat, ∀ i,
      (params i).1 ∈
        (textbookEUniformWitnessStage seed U stage).1 := by
  induction arity with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ arity ih =>
      let initial : Tuple (ZFCarrier U.1) arity :=
        fun i => params i.castSucc
      have hinitial : ∀ i,
          (initial i).1 ∈
            (textbookEUniformWitnessOmegaUnion seed U).1 :=
        fun i => hparams i.castSucc
      rcases ih initial hinitial with
        ⟨initialStage, hinitialStage⟩
      let lastL : LCarrier.{u} :=
        ⟨(params (Fin.last arity)).1,
          mem_L_of_mem (hparams (Fin.last arity))
            (textbookEUniformWitnessOmegaUnion seed U).2⟩
      rcases
          (mem_textbookEUniformWitnessOmegaUnion_iff
            seed U lastL).mp (hparams (Fin.last arity)) with
        ⟨lastStage, hlastStage⟩
      refine ⟨max initialStage lastStage, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact textbookEUniformWitnessStage_mono seed U
          (Nat.le_max_right initialStage lastStage) hlastStage
      · exact textbookEUniformWitnessStage_mono seed U
          (Nat.le_max_left initialStage lastStage) (hinitialStage j)

/--
The internally collected omega union is closed under every textbook `E`
witness task.  This is the full closure predicate, obtained only after the
finite iteration has been collected and unioned.
-/
theorem textbookEUniformWitnessOmegaUnion_closes
    (seed U : LCarrier.{u}) :
    ClosesUnderTextbookEWitnesses
      (textbookEUniformWitnessOmegaUnion seed U).1 U.1 := by
  intro arity code params hparams hexists
  rcases exists_textbookEUniformWitnessStage_for_tuple
      seed U params hparams with
    ⟨stage, hstage⟩
  rcases textbookEUniformWitnessStep_closesAt
      (textbookEUniformWitnessStage seed U stage) U arity code
      params hstage hexists with
    ⟨witness, hwitnessNext, hwitnessRelation⟩
  refine ⟨witness, ?_, hwitnessRelation⟩
  let witnessL : LCarrier.{u} :=
    ⟨witness.1, mem_L_of_mem witness.2 U.2⟩
  apply
    (mem_textbookEUniformWitnessOmegaUnion_iff seed U witnessL).mpr
  exact ⟨stage + 1, hwitnessNext⟩

end

end Constructible.Model
