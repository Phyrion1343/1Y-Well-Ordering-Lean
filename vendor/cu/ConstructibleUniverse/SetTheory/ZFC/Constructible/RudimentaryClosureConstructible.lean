/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaDefinedSet
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryDefOutputFormula

/-!
# Constructibility of the full rudimentary closure

The existing postfix evaluator gives one fixed first-order formula for the
statement that a set is the output of an arbitrary finite rudimentary
program.  Consequently the collection of all such outputs is itself a
constructible set.  This packages `rudimentaryClosure U` as an element of `L`
when `U` belongs to `L`.

This result is needed by the full Skolem-hull construction: all formula
relations over a transitive `U` are members of this one internal index set.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-
The evaluator layout is
`[prefix13, omega, program, result]`.
Under the existential in `rudimentaryClosureMemberFormula` the available
layout is `[prefix13, omega, result, program]`; this renaming swaps the last
two coordinates.
-/
def rudimentaryClosureEvalRename : Fin 16 -> Fin 16 :=
  Fin.lastCases (14 : Fin 16)
    (fun i14 => Fin.lastCases (15 : Fin 16)
      (fun i13 => i13.castSucc.castSucc) i14)

/-- Membership in the full rudimentary closure, with fourteen evaluator
parameters followed by the candidate output. -/
def rudimentaryClosureMemberFormula : FOFormula 15 :=
  .ex (FOFormula.rename rudimentaryClosureEvalRename
    stackProgramEvalFormula)

/-- The evaluator seed and constants used by the membership formula. -/
def rudimentaryClosureParameters
    (U : Constructible.Model.LCarrier.{u}) :
    Tuple Constructible.Model.LCarrier.{u} 14 :=
  snoc (stackStepPrefixLAssignment U.1 U.2)
    ⟨Ordinal.omega0.toZFSet, Constructible.omega_mem_L⟩

private theorem comp_rudimentaryClosureEvalRename
    (U result code : Constructible.Model.LCarrier.{u}) :
    (fun i => snoc (snoc (rudimentaryClosureParameters U) result) code
      (rudimentaryClosureEvalRename i)) =
      stackProgramEvalCodeLAssignment
        U.1 code.1 result.1 U.2 code.2 result.2 := by
  funext i
  fin_cases i <;> rfl

/-- The fixed membership formula recognizes exactly the outputs in the
rudimentary closure. -/
@[simp]
theorem satisfies_rudimentaryClosureMemberFormula
    (U result : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem rudimentaryClosureMemberFormula
        (snoc (rudimentaryClosureParameters U) result) <->
      result.1 ∈ rudimentaryClosure U.1 := by
  simp only [rudimentaryClosureMemberFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨code, heval⟩
    apply (exists_internalProgram_iff_mem_rudimentaryClosure U result).mp
    refine ⟨code, ?_⟩
    simpa only [comp_rudimentaryClosureEvalRename] using heval
  · intro hresult
    rcases (exists_internalProgram_iff_mem_rudimentaryClosure U result).mpr
        hresult with ⟨code, heval⟩
    refine ⟨code, ?_⟩
    simpa only [comp_rudimentaryClosureEvalRename] using heval

/-- The complete finite rudimentary closure of a constructible seed is a
constructible set, not merely an external collection of constructible
outputs. -/
theorem rudimentaryClosure_mem_L
    (U : Constructible.Model.LCarrier.{u}) :
    rudimentaryClosure U.1 ∈ Constructible.L := by
  apply Constructible.Model.mem_L_of_formula_definition_lCarrier
    rudimentaryClosureMemberFormula (rudimentaryClosureParameters U)
  · intro result hresult
    rcases mem_rudimentaryClosure_iff_exists_term.mp hresult with
      ⟨term, rfl⟩
    exact RudimentaryClosureTerm.eval_mem_L U.2 term
  · intro result
    exact (satisfies_rudimentaryClosureMemberFormula U result).symm

/-- The full closure packaged as an element of the membership structure on
`L`. -/
def rudimentaryClosureLCarrier
    (U : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  ⟨rudimentaryClosure U.1, rudimentaryClosure_mem_L U⟩

@[simp]
theorem rudimentaryClosureLCarrier_val
    (U : Constructible.Model.LCarrier.{u}) :
    (rudimentaryClosureLCarrier U).1 = rudimentaryClosure U.1 :=
  rfl

end

end Constructible.Godel.RudimentaryTerm
