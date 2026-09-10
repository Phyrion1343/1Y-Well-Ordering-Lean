import OneYTruth.InitialStageClosure
import OneYTruth.UniformTruth
import OneYTruth.AuxiliaryElementary

/-!
# Initial elementary stages for the constructed auxiliary truth set

Instantiate the stage construction with the actual fixed-domain truth tower.
The ambient bound here is the external omega_1. This theorem does not assume
that the auxiliary predicate lies in L, and hence does not assert expanded
Separation/Collection or the root-indexed finite reflection principle.
-/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Ordinal

universe u

noncomputable def truthAuxiliary : Auxiliary.Interpretation Ambient.{u} :=
  @ExternalTower.auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁)

theorem exists_truth_elementary_LStage (α : Index.{u}) :
    letI := truthAuxiliary.{u}.structure
    ∃ β : Ordinal.{u}, α.val < β ∧ β < ω₁ ∧ Order.IsSuccLimit β ∧
      (stageSubstructure truthAuxiliary β).IsElementary :=
  exists_elementary_LStage truthAuxiliary α

end OneYTruth.InitialStage
