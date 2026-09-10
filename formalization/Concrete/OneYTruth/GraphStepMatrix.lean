import OneYTruth.GraphRelationCertificate
import OneYTruth.AtomicTruthCertificate
import OneYTruth.StructuralDiagramCertificate
import OneYTruth.UniformSyntaxSource
import OneYTruth.FiniteExistentialBlock

/-! A single fixed pure formula simultaneously checks all data for a real step. -/

namespace OneYTruth.GraphStepMatrix

open Constructible Constructible.Model Constructible.Delta0Formula
open BoundedEvaluation

universe u

def syntaxMap : Fin 14 → Fin 34 := ![2,17,5,16,6,7,8,9,10,11,12,6,5,18]
def relationMap : Fin 11 → Fin 34 := ![14,16,17,0,1,19,20,21,22,23,24]
def structuralMap : Fin 13 → Fin 34 := ![0,18,3,11,12,25,26,27,28,29,30,31,32]
def atomicMap : Fin 13 → Fin 34 := ![0,4,3,5,17,23,24,7,8,9,10,27,33]
def solutionMap : Fin 7 → Fin 34 := ![15,26,27,33,31,28,32]

/-- Fixed13 parameters, coded stage, q, proposed Sat; then eighteen witnesses. -/
def matrix : FOFormula 34 :=
  .conj (kuratowskiPairEqAt 13 16 17).toFO
    (.conj (UniformSyntaxSource.formula.rename syntaxMap)
      (.conj (PredecessorGraph.relationCertificate.toFO.rename relationMap)
        (.conj (StructuralDiagramCertificate.formula.toFO.rename structuralMap)
          (.conj (AtomicTruthFormula.certificate.toFO.rename atomicMap)
            (solutionFormula.toFO.rename solutionMap)))))

def Checks (p : Tuple LCarrier.{u} 34) : Prop :=
  (p 13).val = ZFSet.pair (p 16).val (p 17).val ∧
    FOFormula.Satisfies lCarrierMem UniformSyntaxSource.formula (fun i => p (syntaxMap i)) ∧
    Satisfies ZFMem PredecessorGraph.relationCertificate (fun i => (p (relationMap i)).val) ∧
    Satisfies ZFMem StructuralDiagramCertificate.formula (fun i => (p (structuralMap i)).val) ∧
    Satisfies ZFMem AtomicTruthFormula.certificate (fun i => (p (atomicMap i)).val) ∧
    Satisfies ZFMem solutionFormula (fun i => (p (solutionMap i)).val)

theorem satisfies_matrix (p : Tuple LCarrier.{u} 34) :
    FOFormula.Satisfies lCarrierMem matrix p ↔ Checks p := by
  simp only [matrix, FOFormula.Satisfies, FOFormula.satisfies_rename]
  simp only [Delta0Formula.satisfies_toFO_lCarrier_absolute]
  simp only [Delta0Formula.satisfies_toFO, satisfies_kuratowskiPairEqAt, Checks]

attribute [irreducible] matrix

def formula : FOFormula 16 := FiniteExistentialBlock.bind 16 18 matrix

theorem satisfies_formula (p : Tuple LCarrier.{u} 16) :
    FOFormula.Satisfies lCarrierMem formula p ↔
      ∃ w : Tuple LCarrier.{u} 18, Checks (Fin.append p w) := by
  rw [formula,FiniteExistentialBlock.satisfies_bind]
  exact exists_congr (fun _ => satisfies_matrix _)

end OneYTruth.GraphStepMatrix
