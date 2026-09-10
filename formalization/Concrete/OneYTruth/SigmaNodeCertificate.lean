import OneYTruth.SigmaNodeConstruction
import OneYTruth.BoundedFilterGraph

/-! # A bounded canonical check for the genuine Sigma-one node set

The product bound is checked in the same matrix. Once the syntax and assignment
sources have their separate canonical certificates, this matrix admits exactly
the actual Sigma-one formula/assignment pairs of matching arity.
-/

namespace OneYTruth.SigmaNodeCertificate

open Constructible Constructible.Delta0Formula Constructible.Model
open InternalNodes InternalProducts ConstructibleDiagramSources BoundedFilterGraph
open SigmaComparison

universe u v w

theorem sigmaNodes_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) (U : ZFSet.{u}) :
    sigmaNodes (k := k) code U =
      ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x])
        (pairProduct (sigmaCodes (k := k) code) (assignmentCodes U)) := by
  rw [sigmaNodes_eq_filtered_cross, ← sigmaCrossCode_range]
  apply filtered_range_eq_sep (sigmaCrossCode (k := k) (U := U) code)
    (fun z => z.1.val.1 = z.2.1) matchingArityFormula ![]
  intro z
  have ht : snoc (![] : Fin 0 → ZFSet.{u}) (sigmaCrossCode code z) =
      ![sigmaCrossCode code z] := by funext i; fin_cases i; rfl
  rw [ht]
  exact satisfies_matchingArityFormula code (z.1.val, z.2)

/-- Sigma codes, assignments, candidate product, candidate node set. -/
def formula : Delta0Formula 4 :=
  .conj (productAt 2 0 1) (filterAt matchingArityFormula ![] 2 3)

theorem satisfies_formula (p : Fin 4 → ZFSet.{u}) :
    Satisfies ZFMem formula p ↔
      p 2 = pairProduct (p 0) (p 1) ∧
      p 3 = ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x]) (p 2) := by
  have h0 (x : ZFSet.{u}) : snoc (fun i : Fin 0 => p (![] i)) x = ![x] := by
    funext i; fin_cases i; rfl
  simp only [formula, Satisfies, satisfies_productAt, satisfies_filterAt, h0]

attribute [irreducible] formula

theorem satisfies_iff_canonical {k : Nat} {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) (U : ZFSet.{u}) (p : Fin 4 → ZFSet.{u})
    (hSigma : p 0 = sigmaCodes (k := k) code) (hAssignments : p 1 = assignmentCodes U) :
    Satisfies ZFMem formula p ↔
      p 2 = pairProduct (sigmaCodes (k := k) code) (assignmentCodes U) ∧
      p 3 = sigmaNodes (k := k) code U := by
  rw [satisfies_formula, hSigma, hAssignments]
  constructor
  · rintro ⟨hB, hN⟩
    rw [hB, ← sigmaNodes_eq_sep] at hN
    exact ⟨hB, hN⟩
  · rintro ⟨hB, hN⟩
    rw [hB, hN, ← sigmaNodes_eq_sep]
    exact ⟨rfl, rfl⟩

def mixedFormula (K : Nat) (J : Type w) := ofConstructibleDeltaZero K J formula

theorem mixedFormula_isDeltaZero (K : Nat) (J : Type w) : IsDeltaZero (mixedFormula K J) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_iff_canonical {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (code : I → ZFSet.{u}) (U : ZFSet.{u})
    (p : Fin 4 → ZFCarrier V)
    (hSigma : (p 0).val = sigmaCodes (k := k) code)
    (hAssignments : (p 1).val = assignmentCodes U) :
    realize N (mixedFormula K J) Empty.elim p ↔
      (p 2).val = pairProduct (sigmaCodes (k := k) code) (assignmentCodes U) ∧
      (p 3).val = sigmaNodes (k := k) code U := by
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  exact satisfies_iff_canonical code U _ hSigma hAssignments

end OneYTruth.SigmaNodeCertificate

#print axioms OneYTruth.SigmaNodeCertificate.sigmaNodes_eq_sep
#print axioms OneYTruth.SigmaNodeCertificate.realize_iff_canonical
#print axioms OneYTruth.SigmaNodeCertificate.mixedFormula_isDeltaZero
