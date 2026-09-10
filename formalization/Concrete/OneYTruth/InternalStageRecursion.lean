import OneYTruth.InternalStagePresentation
import OneYTruth.InternalFormulaRestriction

/-! # Whole bounded recursion in a weak internal environment

The complete recursive graph is constructed from the one-step presentation:
well-founded induction, exact formula restrictions, Replacement, and unions.
No recursive graph membership is among the hypotheses.
-/

namespace OneYTruth.ExternalTower.InternalStagePresentation

open Constructible Constructible.Model

universe u

variable {V : ZFSet.{u}} {κ : Ordinal.{u}} {op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
variable (P : InternalStagePresentation V κ op)
variable (F : ZFSet.{u} → ZFSet.{u})
variable (hF : ∀ s : Stage κ, F (stageCode s) =
  op (stageCode s) (predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) F))
include P hF in
/-- A constructible canonical local graph satisfies the fixed local-solution
formula. The predecessor restriction is supplied by actual internal Separation. -/
theorem localSolution_of_graph_eq (s : Stage κ) (g : ZFCarrier V)
    (hg : g.val = stageLocalGraph F s) :
    FOFormula.Satisfies (zfCarrierMem V)
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩) g) := by
  classical
  let d : ZFCarrier V := ⟨stageLocalDomain s, P.env.stageLocalDomain_mem P.source_mem s⟩
  have hvalL (z : ZFSet.{u}) (hz : z ∈ d.val) : F z ∈ V :=
    P.env.value_mem_of_restrictionGraph hg g.property hz
  apply (satisfies_localSolutionFormula_carrier_iff P.env.transitive _ _ _ _ _ _).mpr
  refine ⟨d, (P.localDomain_exact s d).mpr rfl, ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    refine ⟨⟨F z.val, hvalL z.val hz⟩, ?_, ?_⟩
    · rw [hg]
      exact pair_mem_predecessorRestrictionGraph F hz
    · intro v hv
      apply Subtype.ext
      rw [hg] at hv
      exact (pair_mem_restrictionGraph_iff.mp hv).2
  · intro pair hp
    rw [hg] at hp
    obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
    exact ⟨⟨z, P.env.transitive.mem_trans hz d.property⟩, hz, ⟨F z, hvalL z hz⟩, he.symm⟩
  · intro z hz
    let q := P.env.formulaRestrictionCarrier P.classFormula P.relationFormula P.params g z
    have hqEq : q.val = predecessorRestrictionGraph (stagePredecessors κ z.val) F := by
      apply ZFSet.ext
      intro pair
      rw [RecursionEnvironment.mem_formulaRestrictionCarrier_raw_iff]
      constructor
      · rintro ⟨hp, w, a, he, _, hrel⟩
        have hwz := (P.relation_exact w z).mp hrel
        have ha : a.val = F w.val := by
          rw [hg, he] at hp
          exact (pair_mem_restrictionGraph_iff.mp hp).2
        exact mem_predecessorRestrictionGraph_iff.mpr
          ⟨w.val, mem_stagePredecessors.mpr hwz, by rw [← ha]; exact he.symm⟩
      · intro hp
        obtain ⟨w, hw, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
        have hwz := mem_stagePredecessors.mp hw
        have hwd := stageLocalDomain_closed s hz hwz
        let wL : ZFCarrier V := ⟨w, P.env.transitive.mem_trans hwd d.property⟩
        let a : ZFCarrier V := ⟨F w, hvalL w hwd⟩
        refine ⟨?_, wL, a, he.symm,
          (P.class_exact wL).mpr (stageLocalDomain_subset_stageSet s hwd),
          (P.relation_exact wL z).mpr hwz⟩
        rw [hg, ← he]
        exact pair_mem_predecessorRestrictionGraph F hwd
    refine ⟨q, ⟨F z.val, hvalL z.val hz⟩, ?_, ?_, ?_⟩
    · exact P.env.mem_formulaRestrictionCarrier_iff _ _ _ _ _
    · rw [hg]
      exact pair_mem_predecessorRestrictionGraph F hz
    · apply (P.step_exact z q _ (stageLocalDomain_subset_stageSet s hz)).mpr
      rw [hqEq]
      obtain ⟨t, ht⟩ := ZFSet.mem_range.mp (stageLocalDomain_subset_stageSet s hz)
      change F z.val = op z.val _
      rw [← ht]
      exact hF t

include P hF in
theorem localSolution_iff_graph_eq (s : Stage κ) (g : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V)
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩) g) ↔
      g.val = stageLocalGraph F s :=
  ⟨P.localSolution_graph_eq F hF s g, P.localSolution_of_graph_eq F hF s g⟩

include P hF in
/-- Replacement collects already constructed local graphs on any internal
stage subdomain. Its functionality comes from the preceding uniqueness proof. -/
theorem collect_localGraphs (d : ZFSet.{u}) (hd : d ∈ V)
    (hsub : ∀ z ∈ d, z ∈ stageSet κ)
    (hlocal : ∀ s : Stage κ, stageCode s ∈ d → stageLocalGraph F s ∈ V) :
    ∃ family : ZFCarrier V, ∀ g : ZFSet.{u}, g ∈ family.val ↔
      ∃ s : Stage κ, stageCode s ∈ d ∧ g = stageLocalGraph F s := by
  classical
  let φ := localSolutionFormula P.classFormula P.relationFormula P.stepFormula
  have hfun : ∀ x : ZFCarrier V, x.val ∈ d → ∃! g : ZFCarrier V,
      FOFormula.Satisfies (zfCarrierMem V) φ (snoc (snoc P.params x) g) := by
    intro x hx
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hsub x.val hx)
    have hxEq : x = ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩ := Subtype.ext hs.symm
    have hsd : stageCode s ∈ d := hs ▸ hx
    refine ⟨⟨stageLocalGraph F s, hlocal s hsd⟩, ?_, ?_⟩
    · rw [hxEq]
      exact P.localSolution_of_graph_eq F hF s _ rfl
    · intro g hg
      apply Subtype.ext
      rw [hxEq] at hg
      exact P.localSolution_graph_eq F hF s g hg
  obtain ⟨family, hfamily⟩ := P.env.replacement P.arity φ P.params ⟨d, hd⟩ hfun
  refine ⟨family, ?_⟩
  intro g
  constructor
  · intro hg
    let gL : ZFCarrier V := ⟨g, P.env.transitive.mem_trans hg family.property⟩
    obtain ⟨x, hx, hφ⟩ := (hfamily gL).mp hg
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hsub x.val hx)
    have hxEq : x = ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩ := Subtype.ext hs.symm
    rw [hxEq] at hφ
    exact ⟨s, hs ▸ hx, P.localSolution_graph_eq F hF s gL hφ⟩
  · rintro ⟨s, hs, rfl⟩
    let gL : ZFCarrier V := ⟨stageLocalGraph F s, hlocal s hs⟩
    exact (hfamily gL).mpr ⟨⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩, hs,
      P.localSolution_of_graph_eq F hF s gL rfl⟩

include P hF in
/-- The real well-founded induction: collect earlier local graphs by
Replacement, union them, and append the new value using one-step closure. -/
theorem stageLocalGraph_mem (s : Stage κ) : stageLocalGraph F s ∈ V := by
  classical
  induction s using (earlier_wellFounded κ).induction with
  | h s ih =>
    let d := stagePredecessors κ (stageCode s)
    have hsub : ∀ z ∈ d, z ∈ stageSet κ := fun z hz =>
      (stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz)
    have hlocal : ∀ t : Stage κ, stageCode t ∈ d → stageLocalGraph F t ∈ V := by
      intro t ht
      exact ih t ((codedEarlier_codes t s).mp (mem_stagePredecessors.mp ht))
    obtain ⟨family, hfamily⟩ := P.collect_localGraphs F hF d
      (P.env.stagePredecessors_mem P.source_mem s) hsub hlocal
    have hunion : ZFSet.sUnion family.val = predecessorRestrictionGraph d F := by
      apply ZFSet.ext
      intro pair
      constructor
      · intro hp
        obtain ⟨g, hg, hp⟩ := ZFSet.mem_sUnion.mp hp
        obtain ⟨t, ht, rfl⟩ := (hfamily g).mp hg
        obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
        have hts := mem_stagePredecessors.mp ht
        have hzd : z ∈ d := by
          apply mem_stagePredecessors.mpr
          rcases (mem_stageLocalDomain t z).mp hz with rfl | hzt
          · exact hts
          · exact codedEarlier_trans hzt hts
        exact mem_predecessorRestrictionGraph_iff.mpr ⟨z, hzd, he⟩
      · intro hp
        obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
        obtain ⟨t, ht⟩ := ZFSet.mem_range.mp (hsub z hz)
        have htd : stageCode t ∈ d := ht ▸ hz
        apply ZFSet.mem_sUnion.mpr
        refine ⟨stageLocalGraph F t, (hfamily _).mpr ⟨t, htd, rfl⟩, ?_⟩
        apply mem_predecessorRestrictionGraph_iff.mpr
        refine ⟨z, ?_, he⟩
        exact (mem_stageLocalDomain t z).mpr (Or.inl ht.symm)
    have hpredL : predecessorRestrictionGraph d F ∈ V :=
      hunion ▸ P.env.sUnion_mem family.property
    have htopL : F (stageCode s) ∈ V := by
      rw [hF s]
      exact P.step_mem ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩
        ⟨predecessorRestrictionGraph d F, hpredL⟩ (stageCode_mem_stageSet s)
    have heq : stageLocalGraph F s =
        ({ZFSet.pair (stageCode s) (F (stageCode s))} : ZFSet.{u}) ∪
          predecessorRestrictionGraph d F := by
      apply ZFSet.ext
      intro pair
      simp only [stageLocalGraph, mem_predecessorRestrictionGraph_iff,
        ZFSet.mem_union, ZFSet.mem_singleton, mem_stageLocalDomain]
      constructor
      · rintro ⟨z, hz, he⟩
        rcases hz with rfl | hz
        · exact Or.inl he.symm
        · exact Or.inr ⟨z, mem_stagePredecessors.mpr hz, he⟩
      · rintro (he | ⟨z, hz, he⟩)
        · exact ⟨stageCode s, Or.inl rfl, he.symm⟩
        · exact ⟨z, Or.inr (mem_stagePredecessors.mp hz), he⟩
    rw [heq]
    exact P.env.union_mem (P.env.singleton_mem (P.env.orderedPair_mem (P.env.stageCode_mem P.source_mem s) htopL)) hpredL

include P hF in
/-- The entire recursively specified graph is in V. No set-sized ZF model
is assumed, and no recursive graph constructibility is supplied as input. -/
theorem stageGraph_mem : predecessorRestrictionGraph (stageSet κ) F ∈ V := by
  obtain ⟨family, hfamily⟩ := P.collect_localGraphs F hF (stageSet κ) P.source_mem
    (fun _ h => h) (fun s _ => P.stageLocalGraph_mem F hF s)
  have heq : ZFSet.sUnion family.val = predecessorRestrictionGraph (stageSet κ) F := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hp
      obtain ⟨g, hg, hp⟩ := ZFSet.mem_sUnion.mp hp
      obtain ⟨s, _, rfl⟩ := (hfamily g).mp hg
      obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
      exact mem_predecessorRestrictionGraph_iff.mpr
        ⟨z, stageLocalDomain_subset_stageSet s hz, he⟩
    · intro hp
      obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
      obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hz
      apply ZFSet.mem_sUnion.mpr
      refine ⟨stageLocalGraph F s, (hfamily _).mpr ⟨s, stageCode_mem_stageSet s, rfl⟩, ?_⟩
      exact mem_predecessorRestrictionGraph_iff.mpr
        ⟨z, (mem_stageLocalDomain s z).mpr (Or.inl hs.symm), he⟩
  exact heq ▸ P.env.sUnion_mem family.property

end OneYTruth.ExternalTower.InternalStagePresentation

#print axioms OneYTruth.ExternalTower.InternalStagePresentation.stageLocalGraph_mem
#print axioms OneYTruth.ExternalTower.InternalStagePresentation.stageGraph_mem
