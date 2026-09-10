import OneYTruth.ActualInternalTower
import OneYTruth.UniformFromGraph

/-! # The actual uniform auxiliary truth predicate in an adequate level

A bounded Separation flattens the completed actual tower. No second
recursion or unproved membership of a truth set is used.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.Godel
open Constructible.FiniteSequenceZF ConstructibleDiagramSources InternalProducts CodedPaths
open ConstructibleBoundedIteration RootSemantics

universe u

theorem uniformSet_mem_of_adequate {κ β : Ordinal.{u}} (hβ : Adequate β)
    (hκβ : κ < β) {U : ZFSet.{u}} (hU : U ∈ LStageZF β) :
    @uniformSet κ U ∈ LStageZF β := by
  have hg := graph_mem_of_adequate hβ hκβ hU
  let E := recursionEnvironment_of_adequate hβ
  let entries := ZFSet.sUnion (pairField (@graph κ U))
  have heV : entries ∈ LStageZF β := E.sUnion_mem (E.sUnion_mem (E.sUnion_mem hg))
  let source := pairProduct (stageSet κ) entries
  have hsource : source ∈ LStageZF β := by
    dsimp only [source]
    rw [pairProduct_eq_F2]
    exact op_mem_LStageZF_of_isSuccLimit hβ.2.1 2
      (stageSet_mem_LStage hβ.2.1 hβ.1 hκβ) heV
  let params : Tuple (ZFCarrier (LStageZF β)) 2 :=
    ![⟨@graph κ U, hg⟩, ⟨κ.toZFSet, ordinal_toZFSet_mem_LStageZF_of_lt hκβ⟩]
  let N := interpretation (κ := β) (LStageZF β) (0, ⟨0, zero_le⟩)
  have hsep := InternalBoundedIteration.deltaSep_mem E.transitive N rfl
    (hβ.2.2 0 0 zero_le).1 uniformMemberFormula params hsource
  have heq : deltaSep uniformMemberFormula (fun i => (params i).val) source = @uniformSet κ U := by
    apply ZFSet.ext
    intro p
    rw [deltaSep, ZFSet.mem_sep]
    constructor
    · rintro ⟨hp, hφ⟩
      obtain ⟨key, hk, entry, _, rfl⟩ := (mem_F2_iff).mp (by
        simpa only [source, pairProduct_eq_F2] using hp)
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hk
      exact (mem_uniformSet_stage_iff U s entry).mpr
        ((satisfies_uniformMemberFormula U s entry).mp hφ)
    · intro hp
      obtain ⟨⟨s, entry⟩, rfl⟩ := ZFSet.mem_range.mp hp
      refine ⟨?_, ?_⟩
      · dsimp only [source]
        rw [pairProduct_eq_F2]
        apply (mem_F2_iff).mpr
        refine ⟨stageCode (closeStage s), stageCode_mem_stageSet (closeStage s), entry.val, ?_, rfl⟩
        exact ZFSet.mem_sUnion.mpr ⟨truth U (closeStage s),
          pair_right_mem_pairField (ZFSet.mem_range_self (closeStage s)), entry.property⟩
      · exact (satisfies_uniformMemberFormula U (closeStage s) entry.val).mpr
          ⟨s.2.property, entry.property⟩
  exact heq ▸ hsep

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.uniformSet_mem_of_adequate
