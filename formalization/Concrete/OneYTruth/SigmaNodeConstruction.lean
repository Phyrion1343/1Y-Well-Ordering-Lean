import OneYTruth.SigmaComparison
import OneYTruth.ConstructibleDiagramSources

/-! # Constructing Sigma-one nodes from the genuine Sigma-one code set

The remaining syntax obligation is stated as membership of the actual
Sigma-one code range in L. No arbitrary subset-closure principle is used.
-/

namespace OneYTruth.SigmaComparison

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula FormulaCode
open Constructible.Model InternalNodes InternalProducts ConstructibleDiagramSources
open ConstructibleAssignmentCodes

universe u v

abbrev SigmaPacked (k : Nat) (I : Type v) := {φ : Packed k I // IsSigmaOne φ.2}

noncomputable def sigmaCodes {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun φ : SigmaPacked k I => packedCode indexCode φ.val)

noncomputable def sigmaCrossCode {k : Nat} {I : Type v} {U : ZFSet.{u}}
    (indexCode : I → ZFSet.{u}) (z : SigmaPacked k I × PackedAssignment U) : ZFSet.{u} :=
  crossCode indexCode (z.1.val, z.2)

theorem sigmaCrossCode_range {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) :
    ZFSet.range (sigmaCrossCode (k := k) (U := U) indexCode) =
      pairProduct (sigmaCodes (k := k) indexCode) (assignmentCodes U) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨⟨φ, xs⟩, he⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.mem_range.mpr ⟨(⟨packedCode indexCode φ.val, ZFSet.mem_range_self φ⟩,
      ⟨assignmentCode xs.2, ZFSet.mem_range_self xs⟩), he⟩
  · intro hp
    obtain ⟨⟨⟨e, he⟩, ⟨a, ha⟩⟩, h⟩ := ZFSet.mem_range.mp hp
    obtain ⟨φ, rfl⟩ := ZFSet.mem_range.mp he
    obtain ⟨xs, rfl⟩ := ZFSet.mem_range.mp ha
    exact ZFSet.mem_range.mpr ⟨(φ, xs), h⟩

theorem sigmaNodes_eq_filtered_cross {k : Nat} {I : Type v} [Small.{u} I]
    (indexCode : I → ZFSet.{u}) (U : ZFSet.{u}) :
    sigmaNodes (k := k) indexCode U = ZFSet.range
      (fun z : {z : SigmaPacked k I × PackedAssignment U // z.1.val.1 = z.2.1} =>
        sigmaCrossCode indexCode z.val) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨n, φ, hφ, xs, he⟩ := (mem_sigmaNodes_iff indexCode U p).mp hp
    exact ZFSet.mem_range.mpr ⟨⟨(⟨⟨n, φ⟩, hφ⟩, ⟨n, xs⟩), rfl⟩, he⟩
  · intro hp
    obtain ⟨⟨⟨⟨⟨n, φ⟩, hφ⟩, ⟨m, xs⟩⟩, hnm⟩, he⟩ := ZFSet.mem_range.mp hp
    change n = m at hnm
    subst m
    exact (mem_sigmaNodes_iff indexCode U p).mpr ⟨n, φ, hφ, xs, he⟩

theorem sigmaNodes_mem_L_of_sigmaCodes {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} {U : ZFSet.{u}}
    (hSigma : sigmaCodes (k := k) indexCode ∈ L) (hU : U ∈ L) :
    sigmaNodes (k := k) indexCode U ∈ L := by
  have hsource : ZFSet.range (sigmaCrossCode (k := k) (U := U) indexCode) ∈ L := by
    rw [sigmaCrossCode_range]
    exact pairProduct_mem_L hSigma (assignmentCodes_mem_L hU)
  rw [sigmaNodes_eq_filtered_cross]
  apply filtered_range_mem_L matchingArityFormula ![]
    (sigmaCrossCode (k := k) (U := U) indexCode) (fun z => z.1.val.1 = z.2.1) hsource
  intro z
  have ht : snoc (fun i => (![] : Tuple LCarrier.{u} 0) i |>.val) (sigmaCrossCode indexCode z) =
      ![sigmaCrossCode indexCode z] := by funext i; fin_cases i; rfl
  rw [ht]
  exact satisfies_matchingArityFormula indexCode (z.1.val, z.2)

end OneYTruth.SigmaComparison

#print axioms OneYTruth.SigmaComparison.sigmaNodes_eq_filtered_cross
#print axioms OneYTruth.SigmaComparison.sigmaNodes_mem_L_of_sigmaCodes
