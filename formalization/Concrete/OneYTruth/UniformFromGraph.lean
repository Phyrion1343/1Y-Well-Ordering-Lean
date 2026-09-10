import OneYTruth.GraphInputConstructible
import OneYTruth.UniformTruth

/-! # The actual uniform auxiliary truth predicate from the actual tower graph

The conversion is bounded Separation inside a proved constructible product.
It does not require a second transfinite recursion.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.Godel
open Constructible.FiniteSequenceZF ConstructibleDiagramSources InternalProducts CodedPaths
open ConstructibleBoundedIteration

universe u

theorem mem_uniformSet_stage_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ)
    (entry : ZFSet.{u}) : ZFSet.pair (stageCode s) entry ∈ @uniformSet κ U ↔
      s.2.val < κ ∧ entry ∈ truth U s := by
  change ZFSet.pair (ZFSet.pair (natCode s.1) s.2.val.toZFSet) entry ∈ _ ↔ _
  rw [mem_uniformSet_at_block_iff]
  constructor
  · rintro ⟨η, he, h⟩
    have hη : s.2.val = η.val := Ordinal.toZFSet_injective he
    refine ⟨hη ▸ η.property, ?_⟩
    have hs : (s.1, ⟨η.val, η.property.le⟩) = s := Prod.ext rfl (Subtype.ext hη.symm)
    exact hs ▸ h
  · rintro ⟨hη, h⟩
    exact ⟨⟨s.2.val, hη⟩, rfl, h⟩

/-- Parameters: full tower graph, ordinal bound, candidate key/entry pair. -/
def uniformMemberFormula : Delta0Formula 3 :=
  .conj (pathMemAt [false, true] 2 1)
    (.boundedEx 0 (.conj (pathsEqualAt [false] [false] 2 3) (componentMemAt true 2 3)))

theorem satisfies_uniformMemberFormula {κ : Ordinal.{u}}
    (U : ZFSet.{u}) (s : Stage κ) (entry : ZFSet.{u}) :
    Satisfies ZFMem uniformMemberFormula
      ![@graph κ U, κ.toZFSet, ZFSet.pair (stageCode s) entry] ↔
      s.2.val < κ ∧ entry ∈ truth U s := by
  simp only [uniformMemberFormula, Satisfies, satisfies_pathMemAt,
    satisfies_pathsEqualAt, satisfies_componentMemAt]
  change (∃ z, Follows [false, true] (ZFSet.pair (stageCode s) entry) z ∧ z ∈ κ.toZFSet) ∧
    (∃ e ∈ @graph κ U,
      (∃ z, Follows [false] (ZFSet.pair (stageCode s) entry) z ∧ Follows [false] e z) ∧
      ∃ a b, Component true (ZFSet.pair (stageCode s) entry) a ∧ Component true e b ∧ a ∈ b) ↔ _
  have hfirst : (∃ z, Follows [false, true] (ZFSet.pair (stageCode s) entry) z ∧ z ∈ κ.toZFSet) ↔
      s.2.val < κ := by
    simp [stageCode, Follows, Ordinal.toZFSet_mem_toZFSet_iff]
  rw [hfirst]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨e, he, hz, hab⟩
    obtain ⟨t, rfl⟩ := ZFSet.mem_range.mp he
    have hst : stageCode t = stageCode s := by simpa [follows_pair, Follows] using hz
    have hts : t = s := stageCode_injective hst
    subst t
    simpa [Component, ZFSet.pair_inj] using hab
  · intro h
    refine ⟨ZFSet.pair (stageCode s) (truth U s), ZFSet.mem_range_self s, ?_, ?_⟩
    · simp [Follows]
    · exact ⟨entry, truth U s, ⟨_, rfl⟩, ⟨_, rfl⟩, h⟩

theorem uniformSet_mem_L_of_graph {κ : Ordinal.{u}} (U : ZFSet.{u})
    (hg : @graph κ U ∈ L) : @uniformSet κ U ∈ L := by
  let entries := ZFSet.sUnion (pairField (@graph κ U))
  have heL : entries ∈ L := sUnion_mem_L (pairField_mem_L hg)
  let source := pairProduct (stageSet κ) entries
  have hsource : source ∈ L := pairProduct_mem_L (stageSet_mem_L κ) heL
  let params : Tuple LCarrier.{u} 2 :=
    ![⟨@graph κ U, hg⟩, ⟨κ.toZFSet, ordinal_toZFSet_mem_L κ⟩]
  have hsep := deltaSep_mem_L uniformMemberFormula params ⟨source, hsource⟩
  have heq : deltaSep uniformMemberFormula (fun i => (params i).val) source = @uniformSet κ U := by
    apply ZFSet.ext
    intro p
    rw [deltaSep, ZFSet.mem_sep]
    constructor
    · rintro ⟨hp, hφ⟩
      obtain ⟨key, hk, entry, _, rfl⟩ := (mem_F2_iff).mp (by
        simpa only [source, pairProduct_eq_F2] using hp)
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hk
      apply (mem_uniformSet_stage_iff U s entry).mpr
      apply (satisfies_uniformMemberFormula U s entry).mp
      exact hφ
    · intro hp
      obtain ⟨⟨s, entry⟩, rfl⟩ := ZFSet.mem_range.mp hp
      refine ⟨?_, ?_⟩
      · dsimp only [source]
        rw [pairProduct_eq_F2]
        apply (mem_F2_iff).mpr
        refine ⟨stageCode (closeStage s), stageCode_mem_stageSet (closeStage s), entry.val, ?_, rfl⟩
        exact ZFSet.mem_sUnion.mpr ⟨truth U (closeStage s),
          pair_right_mem_pairField (ZFSet.mem_range_self (closeStage s)), entry.property⟩
      · apply (satisfies_uniformMemberFormula U (closeStage s) entry.val).mpr
        exact ⟨s.2.property, entry.property⟩
  exact heq ▸ hsep

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.uniformSet_mem_L_of_graph
