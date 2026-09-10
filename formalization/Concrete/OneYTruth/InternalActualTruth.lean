import OneYTruth.ActualInternalTower

/-! Every actual truth set belongs to an adequate larger level, obtained
from the proved complete tower and transitivity, without a Sat witness input. -/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

theorem truth_mem_of_adequate {κ β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β) {U : ZFSet.{u}}
    (hU : U ∈ LStageZF β) (s : Stage κ) : truth U s ∈ LStageZF β := by
  have hV := LStageZF_isTransitive β
  have hg := graph_mem_of_adequate hβ hκβ hU
  have he : ZFSet.pair (stageCode s) (truth U s) ∈ @graph κ U :=
    ZFSet.mem_range_self (f := fun t : Stage κ => ZFSet.pair (stageCode t) (truth U t)) s
  exact (pair_components_mem hV (hV.mem_trans he hg)).2

theorem truth_LStage_mem_of_adequate {a β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (haβ : a < β) (s : Stage a) :
    truth (LStageZF a) s ∈ LStageZF β :=
  truth_mem_of_adequate hβ haβ (LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 haβ) s

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.truth_mem_of_adequate
#print axioms OneYTruth.ExternalTower.truth_LStage_mem_of_adequate
