import OneYTruth.TowerRestrictionCertificate

/-! A full graph is determined by totality, no junk, and the genuine local
step equation using its own exact predecessor restrictions. No functionality
or agreement with an external tower is assumed. -/

namespace OneYTruth.TowerRestriction

open Constructible Constructible.Model ExternalTower

universe u

theorem graph_eq_of_steps {κ : Ordinal.{u}} (U g : ZFSet.{u})
    (htotal : ∀ s : Stage κ, ∃ T, ZFSet.pair (stageCode s) T ∈ g)
    (hjunk : ∀ p ∈ g, ∃ s : Stage κ, ∃ T, p = ZFSet.pair (stageCode s) T)
    (hstep : ∀ s : Stage κ, ∀ T, ZFSet.pair (stageCode s) T ∈ g →
      T = graphInputStep κ U (stageCode s) (restrict (stageCode s) g)) :
    g = @graph κ U := by
  have hvalue : ∀ s : Stage κ, ∀ T, ZFSet.pair (stageCode s) T ∈ g → T = truth U s := by
    intro s
    induction s using (earlier_wellFounded κ).induction with
    | h s ih =>
      have hrestriction : restrict (stageCode s) g =
          predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) (codedTruth κ U) := by
        apply ZFSet.ext
        intro p
        rw [restrict,ZFSet.mem_sep,mem_predecessorRestrictionGraph_iff]
        constructor
        · rintro ⟨hpg,hrel⟩
          obtain ⟨t,T,he⟩ := hjunk p hpg
          rw [he] at hpg hrel
          have hts := (satisfies_predicate_pair s t T).mp hrel
          have hT := ih t hts T hpg
          refine ⟨stageCode t,mem_stagePredecessors.mpr ((codedEarlier_codes t s).mpr hts),?_⟩
          rw [codedTruth_code,← hT]
          exact he.symm
        · rintro ⟨z,hz,he⟩
          obtain ⟨t,ht⟩ := ZFSet.mem_range.mp ((stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz))
          have hts : Earlier t s := (codedEarlier_codes t s).mp (ht ▸ mem_stagePredecessors.mp hz)
          obtain ⟨T,hTg⟩ := htotal t
          have hT := ih t hts T hTg
          have hp : p = ZFSet.pair (stageCode t) T := by
            rw [← he,← ht,codedTruth_code,← hT]
          rw [hp]
          exact ⟨hTg,(satisfies_predicate_pair s t T).mpr hts⟩
      intro T hT
      rw [hstep s T hT,hrestriction,← codedTruth_graphInputStep U s,codedTruth_code]
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨s,T,he⟩ := hjunk p hp
    have hT := hvalue s T (he ▸ hp)
    exact ZFSet.mem_range.mpr ⟨s,by rw [← hT]; exact he.symm⟩
  · intro hp
    obtain ⟨s,rfl⟩ := ZFSet.mem_range.mp hp
    obtain ⟨T,hT⟩ := htotal s
    exact hvalue s T hT ▸ hT

end OneYTruth.TowerRestriction
