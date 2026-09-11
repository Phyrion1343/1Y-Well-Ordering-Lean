/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteSkolemIteration

/-!
# External Goedel codes for existential Skolem matrices

This file specializes `FormulaSyntaxCode` to the dependent package

`InternalSkolemMatrix = Sigma fun n => FOFormula (n + 1)`.

It gives a single natural-number coding, decoding, and total surjective
enumeration of all such matrices, together with their von Neumann natural
codes in the internal omega.

The enumerator itself is an external Lean function.  Membership of each
individual code in internal omega does not assert that decoding, satisfaction,
or the compiled-relation map has an object-language graph inside a model.
Those uniform definability facts remain necessary before Replacement can be
used to collect a full Skolem iteration.
-/

@[expose] public section

universe u

namespace Constructible.Model

open FOFormulaCode
open FiniteSequenceZF

/-- Pair the parameter arity with the code of the matrix formula. -/
def internalSkolemMatrixNatCode (matrix : InternalSkolemMatrix) : Nat :=
  Nat.pair matrix.1 (formulaNatCode matrix.2)

/-- Decode a parameter arity and then scope-check its matrix in arity
`n + 1`. -/
def internalSkolemMatrixNatDecode
    (code : Nat) : Option InternalSkolemMatrix :=
  let data := Nat.unpair code
  (formulaNatDecode (data.1 + 1) data.2).map fun formula =>
    ⟨data.1, formula⟩

/-- Matrix decoding is a left inverse of matrix coding. -/
@[simp]
theorem internalSkolemMatrixNatDecode_internalSkolemMatrixNatCode
    (matrix : InternalSkolemMatrix) :
    internalSkolemMatrixNatDecode (internalSkolemMatrixNatCode matrix) =
      some matrix := by
  rcases matrix with ⟨n, formula⟩
  unfold internalSkolemMatrixNatDecode internalSkolemMatrixNatCode
  rw [Nat.unpair_pair]
  dsimp only
  rw [formulaNatDecode_formulaNatCode]
  rfl

/-- Distinct existential matrices have distinct natural-number codes. -/
theorem internalSkolemMatrixNatCode_injective :
    Function.Injective internalSkolemMatrixNatCode := by
  intro left right hcode
  have h := congrArg internalSkolemMatrixNatDecode hcode
  simpa using h

@[simp]
theorem internalSkolemMatrixNatCode_inj
    {left right : InternalSkolemMatrix} :
    internalSkolemMatrixNatCode left = internalSkolemMatrixNatCode right ↔
      left = right :=
  internalSkolemMatrixNatCode_injective.eq_iff

/-- A fixed value used only at invalid matrix codes. -/
def defaultInternalSkolemMatrix : InternalSkolemMatrix :=
  ⟨0, defaultFormula 1⟩

/-- A total external enumeration of all existential matrices. -/
def internalSkolemMatrixNatEnumerate
    (code : Nat) : InternalSkolemMatrix :=
  (internalSkolemMatrixNatDecode code).getD defaultInternalSkolemMatrix

/-- At the genuine code of a matrix, total enumeration recovers it. -/
@[simp]
theorem internalSkolemMatrixNatEnumerate_internalSkolemMatrixNatCode
    (matrix : InternalSkolemMatrix) :
    internalSkolemMatrixNatEnumerate (internalSkolemMatrixNatCode matrix) =
      matrix := by
  simp [internalSkolemMatrixNatEnumerate]

/-- Every existential matrix occurs in the external enumeration. -/
theorem internalSkolemMatrixNatEnumerate_surjective :
    Function.Surjective internalSkolemMatrixNatEnumerate := by
  intro matrix
  exact ⟨internalSkolemMatrixNatCode matrix,
    internalSkolemMatrixNatEnumerate_internalSkolemMatrixNatCode matrix⟩

/-- The von Neumann natural-number code of an existential matrix. -/
noncomputable def internalSkolemMatrixZFCode
    (matrix : InternalSkolemMatrix) : ZFSet.{u} :=
  natCode (internalSkolemMatrixNatCode matrix)

/-- Matrix `ZFSet` codes are injective across all parameter arities. -/
theorem internalSkolemMatrixZFCode_injective :
    Function.Injective
      (internalSkolemMatrixZFCode : InternalSkolemMatrix -> ZFSet.{u}) :=
  natCode_injective.comp internalSkolemMatrixNatCode_injective

@[simp]
theorem internalSkolemMatrixZFCode_inj
    {left right : InternalSkolemMatrix} :
    (internalSkolemMatrixZFCode left : ZFSet.{u}) =
        internalSkolemMatrixZFCode right ↔
      left = right :=
  internalSkolemMatrixZFCode_injective.eq_iff

/-- Every matrix code belongs to the standard internal omega. -/
theorem internalSkolemMatrixZFCode_mem_omega
    (matrix : InternalSkolemMatrix) :
    (internalSkolemMatrixZFCode matrix : ZFSet.{u}) ∈
      Ordinal.omega0.toZFSet := by
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
    (Ordinal.natCast_lt_omega0 (internalSkolemMatrixNatCode matrix))

/-- Every matrix code is constructible. -/
theorem internalSkolemMatrixZFCode_mem_L
    (matrix : InternalSkolemMatrix) :
    (internalSkolemMatrixZFCode matrix : ZFSet.{u}) ∈ L := by
  exact natCode_mem_L (internalSkolemMatrixNatCode matrix)

end Constructible.Model
