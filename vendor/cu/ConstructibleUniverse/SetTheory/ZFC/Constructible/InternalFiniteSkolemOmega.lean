/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteSkolemIteration

/-!
# Conditional internal omega union for a finite Skolem family

`InternalFiniteSkolemIteration` constructs each finite stage as an actual
member of `L`, but its stage sequence is still an external Lean function.
This file records the exact additional datum needed to internalize that
sequence: one fixed object-language formula which uniformly defines all of
its values on the internal natural numbers.

Once such a specification is supplied, `UniformOmegaFamilySpec` applies
Replacement over internal omega.  The resulting union is an `LCarrier`, and
the usual finite-tuple maximum argument proves witness closure for every
matrix in the displayed finite list.

No uniform stage formula is manufactured here.  Thus this file is a
conditional assembly theorem, not a claim that the full Skolem hull or a
model-internal enumeration of all formulas has already been constructed.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-- A uniform object-language definition of the externally described finite
Skolem stages.  The `family` field is precisely the hypothesis needed for
Replacement; `value_eq_stage` identifies its semantic values with the
recursive construction. -/
structure InternalFormulaSkolemStageSpec
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (matrices : List InternalSkolemMatrix) (seed : LCarrier.{u}) where
  family : UniformOmegaFamilySpec.{u}
  value_eq_stage : ∀ n : Nat,
    family.value n =
      internalFormulaSkolemStage U hU matrices seed n

/-- The internal union obtained by Replacement from a uniform stage
specification. -/
noncomputable def internalFormulaSkolemOmegaUnion
    {U : LCarrier.{u}} {hU : U.1.IsTransitive}
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed) :
    LCarrier.{u} :=
  uniformOmegaUnion spec.family

@[simp]
theorem mem_internalFormulaSkolemOmegaUnion_iff
    {U : LCarrier.{u}} {hU : U.1.IsTransitive}
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed)
    (z : LCarrier.{u}) :
    z.1 ∈ (internalFormulaSkolemOmegaUnion spec).1 ↔
      ∃ n : Nat,
        z.1 ∈
          (internalFormulaSkolemStage U hU matrices seed n).1 := by
  rw [internalFormulaSkolemOmegaUnion, mem_uniformOmegaUnion_iff]
  apply exists_congr
  intro n
  rw [spec.value_eq_stage n]

/-- The internally collected omega union contains the initial seed. -/
theorem seed_subset_internalFormulaSkolemOmegaUnion
    {U : LCarrier.{u}} {hU : U.1.IsTransitive}
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed) :
    seed.1 ⊆ (internalFormulaSkolemOmegaUnion spec).1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz seed.2⟩
  apply (mem_internalFormulaSkolemOmegaUnion_iff spec zL).mpr
  refine ⟨0, ?_⟩
  simpa only [internalFormulaSkolemStage_zero] using hz

/-- If the initial seed lies in `U`, the internally collected omega union
also lies in `U`. -/
theorem internalFormulaSkolemOmegaUnion_subset
    {U : LCarrier.{u}} (hU : U.1.IsTransitive)
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (hseed : seed.1 ⊆ U.1)
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed) :
    (internalFormulaSkolemOmegaUnion spec).1 ⊆ U.1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (internalFormulaSkolemOmegaUnion spec).2⟩
  rcases (mem_internalFormulaSkolemOmegaUnion_iff spec zL).mp hz with
    ⟨n, hzn⟩
  exact internalFormulaSkolemStage_subset U hU matrices seed hseed n hzn

/-- Every finite tuple from the internal omega union occurs together in one
finite stage. -/
theorem exists_internalFormulaSkolemStage_for_tuple
    {U : LCarrier.{u}} (hU : U.1.IsTransitive)
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed)
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (hparams : ∀ i,
      (params i).1 ∈ (internalFormulaSkolemOmegaUnion spec).1) :
    ∃ stage : Nat, ∀ i,
      (params i).1 ∈
        (internalFormulaSkolemStage U hU matrices seed stage).1 := by
  induction n with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let initial : Tuple (ZFCarrier U.1) n :=
        fun i => params i.castSucc
      have hinitial : ∀ i,
          (initial i).1 ∈
            (internalFormulaSkolemOmegaUnion spec).1 :=
        fun i => hparams i.castSucc
      rcases ih initial hinitial with
        ⟨initialStage, hinitialStage⟩
      let lastL : LCarrier.{u} :=
        ⟨(params (Fin.last n)).1,
          mem_L_of_mem (hparams (Fin.last n))
            (internalFormulaSkolemOmegaUnion spec).2⟩
      rcases (mem_internalFormulaSkolemOmegaUnion_iff spec lastL).mp
          (hparams (Fin.last n)) with
        ⟨lastStage, hlastStage⟩
      refine ⟨max initialStage lastStage, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact internalFormulaSkolemStage_mono U hU matrices seed
          (Nat.le_max_right initialStage lastStage) hlastStage
      · exact internalFormulaSkolemStage_mono U hU matrices seed
          (Nat.le_max_left initialStage lastStage) (hinitialStage j)

/-- Every listed matrix has witnesses over tuples from the internal omega
union.  This is finite-family Tarski witness closure, not full elementarity. -/
theorem exists_witness_mem_internalFormulaSkolemOmegaUnion_of_mem
    {U : LCarrier.{u}} (hU : U.1.IsTransitive)
    {matrices : List InternalSkolemMatrix} {seed : LCarrier.{u}}
    (spec : InternalFormulaSkolemStageSpec U hU matrices seed)
    (matrix : InternalSkolemMatrix) (hmatrix : matrix ∈ matrices)
    (params : Tuple (ZFCarrier U.1) matrix.1)
    (hparams : ∀ i,
      (params i).1 ∈ (internalFormulaSkolemOmegaUnion spec).1)
    (hexists : ∃ x : ZFCarrier U.1,
      FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
        (snoc params x)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈ (internalFormulaSkolemOmegaUnion spec).1 ∧
        FOFormula.Satisfies (zfCarrierMem U.1) matrix.2
          (snoc params y) := by
  rcases exists_internalFormulaSkolemStage_for_tuple hU spec params hparams with
    ⟨stage, hstage⟩
  rcases exists_witness_mem_internalFormulaSkolemStage_succ_of_mem
      U hU matrices seed stage matrix hmatrix params hstage hexists with
    ⟨y, hyNext, hySat⟩
  refine ⟨y, ?_, hySat⟩
  let yL : LCarrier.{u} :=
    ⟨y.1, mem_L_of_mem y.2 U.2⟩
  apply (mem_internalFormulaSkolemOmegaUnion_iff spec yL).mpr
  exact ⟨stage + 1, hyNext⟩

end

end Constructible.Model
