/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FunctionGraphFormulaLCarrier

/-!
# Textbook local-solution formulas over L

This file unfolds the local-solution and recursion-value formulas directly
over `LCarrier`.  These are semantic equivalences only: they do not assume
or manufacture an internal local solution graph.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Formula insertion -/

@[simp]
theorem satisfies_localDomainFormulaAt_lCarrier_generic
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (localDomainFormulaAt classFormula relationFormula
          params x domain) s <->
      FOFormula.Satisfies LMem
        (localDomainFormula classFormula relationFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s domain)) := by
  rw [localDomainFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (Fin.lastCases domain (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s domain) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfies_stepFormulaAt_lCarrier_generic
    {n m : Nat} (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (stepFormulaAt stepFormula params x graph value) s <->
      FOFormula.Satisfies LMem stepFormula
        (snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value)) := by
  rw [stepFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (Fin.lastCases value (fun k =>
        Fin.lastCases graph (fun j => Fin.lastCases x params j) k) i)) =
        snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simp
        · simp
  rw [hassignment]

/-! ## Exact local-solution semantics -/

@[simp]
theorem satisfies_localSolutionFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple LCarrier.{u} n) (x graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) graph) <->
      exists domain : LCarrier.{u},
        FOFormula.Satisfies LMem
          (localDomainFormula classFormula relationFormula)
          (snoc (snoc params x) domain) /\
        (((forall input : LCarrier.{u}, input.1 ∈ domain.1 ->
              exists value : LCarrier.{u},
                ZFSet.pair input.1 value.1 ∈ graph.1 /\
                forall other : LCarrier.{u},
                  ZFSet.pair input.1 other.1 ∈ graph.1 ->
                    other = value) /\
            forall pair : LCarrier.{u}, pair.1 ∈ graph.1 ->
              exists input : LCarrier.{u}, input.1 ∈ domain.1 /\
                exists value : LCarrier.{u},
                  pair.1 = ZFSet.pair input.1 value.1) /\
          forall top : LCarrier.{u}, top.1 ∈ domain.1 ->
            exists restriction value : LCarrier.{u},
              (forall pair : LCarrier.{u},
                pair.1 ∈ restriction.1 <->
                  pair.1 ∈ graph.1 /\
                    exists input output : LCarrier.{u},
                      pair.1 = ZFSet.pair input.1 output.1 /\
                      FOFormula.Satisfies LMem classFormula
                        (snoc params input) /\
                      FOFormula.Satisfies LMem relationFormula
                        (snoc (snoc params input) top)) /\
              ZFSet.pair top.1 value.1 ∈ graph.1 /\
              FOFormula.Satisfies LMem stepFormula
                (snoc (snoc (snoc params top) restriction) value)) := by
  simp only [localSolutionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll,
    satisfies_localDomainFormulaAt_lCarrier_generic,
    satisfies_functionGraphOnFormulaAt_lCarrier_iff,
    satisfies_restrictionGraphFormulaAt_lCarrier_iff,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_stepFormulaAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

/-! ## Exact recursion-value semantics -/

@[simp]
theorem satisfies_localSolutionFormulaAt_lCarrier_generic
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (localSolutionFormulaAt classFormula relationFormula stepFormula
          params x graph) s <->
      FOFormula.Satisfies LMem
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s graph)) := by
  rw [localSolutionFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (Fin.lastCases graph (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s graph) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfies_recursionValueFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple LCarrier.{u} n) (x value : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (recursionValueFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) value) <->
      FOFormula.Satisfies LMem classFormula (snoc params x) /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula classFormula relationFormula stepFormula)
            (snoc (snoc params x) graph) /\
          ZFSet.pair x.1 value.1 ∈ graph.1 := by
  simp only [recursionValueFormula, FOFormula.Satisfies,
    satisfies_classFormulaAt_generic,
    satisfies_localSolutionFormulaAt_lCarrier_generic,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    snoc_last, snoc_castSucc]

end

end Constructible.Model
