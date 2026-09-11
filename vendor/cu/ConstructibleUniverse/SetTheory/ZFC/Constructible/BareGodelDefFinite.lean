/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareGodelDefAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryOmegaBounds

/-!
# The Goedel evaluator on finite constructible predecessors

This file isolates the exceptional carrier used at the first infinite
history stage.  The evaluator is interpreted in `L_(omega+1)`, because its
fixed prefix contains the set `omega`; its actual predecessor, output,
program, and trace data are bounded already by `L_omega`.

No claim is made here about arbitrary predecessor inputs in `L_(omega+1)`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The witness-producing substage `L_omega` is contained in the semantic
carrier `L_(omega+1)`. -/
theorem LStageZF_omega_subset_omega_succ :
    (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u}) ⊆
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  LStageZF_mono (Order.le_succ (Ordinal.omega0 : Ordinal.{u}))

/-- The one fixed parameter absent from `L_omega` itself is available in
the successor carrier in which the finite evaluator is interpreted. -/
theorem omega_toZFSet_mem_LStageZF_omega_succ :
    (Ordinal.omega0 : Ordinal.{u}).toZFSet ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u})) :=
  ordinal_toZFSet_mem_LStageZF_of_lt
    (Order.lt_succ (Ordinal.omega0 : Ordinal.{u}))

/-- A finite predecessor is available in the witness-producing substage. -/
theorem finiteGodelPredecessor_mem_LStageZF_omega (n : Nat) :
    LStageZF (n : Ordinal.{u}) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  LStageZF_natCast_mem_LStageZF_omega n

/-- Its actual Goedel output is available in the same substage. -/
theorem finiteGodelOutput_mem_LStageZF_omega (n : Nat) :
    Godel.godelDef (LStageZF (n : Ordinal.{u})) ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
  godelDef_LStageZF_natCast_mem_LStageZF_omega n

/-- On a finite predecessor, the internal stack evaluator in
`L_(omega+1)` is exact for every result already bounded by `L_omega`.
This is the witness range needed for the finite Goedel output, not a claim
about arbitrary evaluator inputs in the successor carrier. -/
theorem satisfiesIn_stackProgramEvalFormula_omega_succ_natCast_iff_run
    (n : Nat)
    (program : List (Godel.RudimentaryTerm.StackToken
      (Option (Constructible.ZFCarrier
        (LStageZF (n : Ordinal.{u}))))))
    (result : ZFSet.{u})
    (hresult : result ∈
      LStageZF (Ordinal.omega0 : Ordinal.{u})) :
    SatisfiesIn
        (LStageZF (Order.succ
          (Ordinal.omega0 : Ordinal.{u})) : Set ZFSet.{u})
        Godel.RudimentaryTerm.stackProgramEvalFormula
        (Godel.RudimentaryTerm.stackProgramEvalAssignment
          (LStageZF (n : Ordinal.{u}))
          (Godel.RudimentaryTerm.stackProgramZFCode
            (LStageZF (n : Ordinal.{u})) program)
          result) ↔
      Godel.RudimentaryTerm.runStackProgram
          (Godel.rudimentaryGenerator
            (LStageZF (n : Ordinal.{u}))) program [] =
        some [result] := by
  exact
    Godel.RudimentaryTerm.satisfiesIn_stackProgramEvalFormula_of_isSuccLimit_substage_iff_run
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        Ordinal.isSuccLimit_omega0
        LStageZF_omega_subset_omega_succ
        omega_toZFSet_mem_LStageZF_omega_succ
        (LStageZF (n : Ordinal.{u}))
        (finiteGodelPredecessor_mem_LStageZF_omega n)
        program result hresult

/-- Exact pointwise correctness of the Goedel-output formula for an actual
finite constructible predecessor.  The candidate output ranges over all of
`L_(omega+1)`, while the predecessor is explicitly fixed to `L_n`. -/
theorem bareGodelDefOutputIn_omega_succ_natCast_iff
    (n : Nat) (stage : ZFSet.{u})
    (hstage : stage ∈
      LStageZF (Order.succ (Ordinal.omega0 : Ordinal.{u}))) :
    BareGodelDefOutputIn
        (LStageZF (Order.succ
          (Ordinal.omega0 : Ordinal.{u})) : Set ZFSet.{u})
        stageHistoryFixedParametersRaw
        (LStageZF (n : Ordinal.{u})) stage ↔
      stage = Godel.godelDef (LStageZF (n : Ordinal.{u})) := by
  exact
    Godel.RudimentaryTerm.bareGodelDefOutputIn_of_isSuccLimit_substage_iff
        (LStageZF_isTransitive
          (Order.succ (Ordinal.omega0 : Ordinal.{u})))
        Ordinal.isSuccLimit_omega0
        LStageZF_omega_subset_omega_succ
        omega_toZFSet_mem_LStageZF_omega_succ
        (LStageZF (n : Ordinal.{u})) stage
        (finiteGodelPredecessor_mem_LStageZF_omega n) hstage

end

end Constructible.Model
