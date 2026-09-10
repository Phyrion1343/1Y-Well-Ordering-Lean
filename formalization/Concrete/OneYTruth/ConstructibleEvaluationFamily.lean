import OneYTruth.ConstructibleDiagramSources

/-! The actual full omega family of Tarski approximations belongs to L. -/

namespace OneYTruth.ConstructibleEvaluationFamily

open Constructible Constructible.Delta0Formula Constructible.Model
open ConstructibleBoundedIteration BoundedEvaluation

universe u

def HasConstructibleFields (D : Diagram.{u}) : Prop :=
  D.nodes ∈ L ∧ D.atoms ∈ L ∧ D.trueAtoms ∈ L ∧
    D.implications ∈ L ∧ D.quantified ∈ L ∧ D.children ∈ L

noncomputable def dataParams (D : Diagram.{u}) (hD : HasConstructibleFields D) :
    Tuple LCarrier.{u} 6 :=
  ![⟨D.nodes, hD.1⟩, ⟨D.atoms, hD.2.1⟩, ⟨D.trueAtoms, hD.2.2.1⟩,
    ⟨D.implications, hD.2.2.2.1⟩, ⟨D.quantified, hD.2.2.2.2.1⟩,
    ⟨D.children, hD.2.2.2.2.2⟩]

/-- Diagram fields, current approximation, candidate node. -/
def evaluationFilter : Delta0Formula 8 := stepAt 6 0 2 3 4 5 7

theorem filterStep_eq_stepSet (D : Diagram.{u}) (hD : HasConstructibleFields D) (S : LCarrier.{u}) :
    (filterStep evaluationFilter 0 (dataParams D hD) S).val = stepSet D S.val := by
  apply ZFSet.ext
  intro x
  change x ∈ deltaSep evaluationFilter
    (snoc (fun i => (dataParams D hD i).val) S.val) D.nodes ↔ _
  rw [deltaSep, ZFSet.mem_sep, mem_stepSet_iff, evaluationFilter, satisfies_stepAt]
  rfl

noncomputable def family (D : Diagram.{u}) (hD : HasConstructibleFields D) :
    ParametricUniformOmegaFamilySpec.{u} 7 :=
  ConstructibleBoundedIteration.family evaluationFilter 0 (dataParams D hD) emptyLCarrier

theorem family_value_eq (D : Diagram.{u}) (hD : HasConstructibleFields D) (n : Nat) :
    ((family D hD).value n).val = iterate D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (filterStep evaluationFilter 0 (dataParams D hD) ((family D hD).value n)).val = _
    rw [filterStep_eq_stepSet, ih]
    rfl

def stageFormula : FOFormula 9 := uniformFiniteIterationFormula (filterGraph evaluationFilter 0).toFO

theorem realizes_stageFormula (D : Diagram.{u}) (hD : HasConstructibleFields D)
    (n : Nat) (S : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem stageFormula
      (snoc (snoc (family D hD).params (natLCarrier n)) S) ↔ S.val = iterate D n := by
  have h := (family D hD).realizes n S
  rw [← family_value_eq D hD n]
  exact h.trans Subtype.coe_injective.eq_iff.symm

end OneYTruth.ConstructibleEvaluationFamily
