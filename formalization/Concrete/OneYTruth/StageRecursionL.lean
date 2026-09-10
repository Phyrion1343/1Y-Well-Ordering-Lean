import OneYTruth.StageRecursionDomain
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalSolutionLCarrier
import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier

/-! # Genuine set recursion over the proper class L

The stage order is the actual order from `ExternalTower`. The only formula
interface below concerns the **one-step operator**. Constructibility of
recursive graphs is a conclusion, never a field of that interface.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Godel

universe u

/-- An explicit pending interface for one fixed first-order definition of
the whole one-step operator. This is stronger than a formula testing one
node of its output. It does not assert that any recursive graph belongs to L. -/
structure StageStepPresentation (κ : Ordinal.{u})
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) where
  arity : Nat
  params : Tuple LCarrier.{u} arity
  classFormula : FOFormula (arity + 1)
  relationFormula : FOFormula (arity + 2)
  stepFormula : FOFormula (arity + 3)
  class_exact : ∀ z : LCarrier.{u},
    FOFormula.Satisfies lCarrierMem classFormula (snoc params z) ↔ z.val ∈ stageSet κ
  relation_exact : ∀ y z : LCarrier.{u},
    FOFormula.Satisfies lCarrierMem relationFormula (snoc (snoc params y) z) ↔
      CodedEarlier κ y.val z.val
  step_exact : ∀ x q v : LCarrier.{u}, x.val ∈ stageSet κ →
    (FOFormula.Satisfies lCarrierMem stepFormula (snoc (snoc (snoc params x) q) v) ↔
      v.val = op x.val q.val)
  step_mem_L : ∀ x q : LCarrier.{u}, x.val ∈ stageSet κ → op x.val q.val ∈ L

noncomputable def stageLocalGraph {κ : Ordinal.{u}}
    (F : ZFSet.{u} → ZFSet.{u}) (s : Stage κ) : ZFSet.{u} :=
  predecessorRestrictionGraph (stageLocalDomain s) F

theorem stageLocalDomain_subset_stageSet {κ : Ordinal.{u}} (s : Stage κ)
    {z : ZFSet.{u}} (hz : z ∈ stageLocalDomain s) : z ∈ stageSet κ := by
  rcases (mem_stageLocalDomain s z).mp hz with rfl | h
  · exact stageCode_mem_stageSet s
  · exact (stage_relationOn κ).left_mem h

theorem stageLocalDomain_closed {κ : Ordinal.{u}} (s : Stage κ)
    {z w : ZFSet.{u}} (hz : z ∈ stageLocalDomain s) (hw : CodedEarlier κ w z) :
    w ∈ stageLocalDomain s := by
  apply (mem_stageLocalDomain s w).mpr
  rcases (mem_stageLocalDomain s z).mp hz with rfl | h
  · exact Or.inr hw
  · exact Or.inr (codedEarlier_trans hw h)

theorem value_mem_L_of_restrictionGraph {d g : ZFSet.{u}}
    {F : ZFSet.{u} → ZFSet.{u}} (hg : g = predecessorRestrictionGraph d F)
    (hgL : g ∈ L) {z : ZFSet.{u}} (hz : z ∈ d) : F z ∈ L := by
  apply mem_L_of_mem (pair_right_mem_pairField (r := g) (x := z) (y := F z) ?_)
    (pairField_mem_L hgL)
  rw [hg]
  exact pair_mem_predecessorRestrictionGraph F hz

theorem pair_mem_restrictionGraph_iff {d z v : ZFSet.{u}}
    {F : ZFSet.{u} → ZFSet.{u}} :
    ZFSet.pair z v ∈ predecessorRestrictionGraph d F ↔ z ∈ d ∧ v = F z := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := mem_predecessorRestrictionGraph_iff.mp h
    obtain ⟨hwz, hv⟩ := ZFSet.pair_inj.mp he
    subst z
    exact ⟨hw, hv.symm⟩
  · rintro ⟨hz, rfl⟩
    exact pair_mem_predecessorRestrictionGraph F hz

namespace StageStepPresentation

variable {κ : Ordinal.{u}} {op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
variable (P : StageStepPresentation κ op)
variable (F : ZFSet.{u} → ZFSet.{u})
variable (hF : ∀ s : Stage κ, F (stageCode s) =
  op (stageCode s) (predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) F))

theorem localDomain_exact (s : Stage κ) (d : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem (localDomainFormula P.classFormula P.relationFormula)
      (snoc (snoc P.params ⟨stageCode s, stageCode_mem_L s⟩) d) ↔
      d.val = stageLocalDomain s := by
  have h := satisfies_localDomainFormula_lCarrier_iff_eq_localRecursionDomain
    (A := (stageSet κ : Set ZFSet.{u})) (R := stageClassRelation κ)
    P.classFormula P.relationFormula P.params P.class_exact P.relation_exact
    (stage_relationOn κ) (stage_setPredecessors κ) (stage_predecessorsClosedIn_L κ)
    (x := ⟨stageCode s, stageCode_mem_L s⟩) (domain := d)
    (stageCode_mem_stageSet s) (localRecursionDomain_mem_L_stage s)
  simpa only [localRecursionDomain_eq_stage] using h

include P hF in
/-- Any L-internal local solution has exactly the external recursively
specified values. This uses actual well-founded induction on the coded order. -/
theorem localSolution_graph_eq (s : Stage κ) (g : LCarrier.{u})
    (hg : FOFormula.Satisfies lCarrierMem
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, stageCode_mem_L s⟩) g)) :
    g.val = stageLocalGraph F s := by
  classical
  obtain ⟨d, hd, hfun, hsteps⟩ :=
    (satisfies_localSolutionFormula_lCarrier_iff _ _ _ _ _ _).mp hg
  have hdEq := (P.localDomain_exact s d).mp hd
  have hvalue : ∀ z : ZFSet.{u}, z ∈ stageLocalDomain s →
      ∀ v : LCarrier.{u}, ZFSet.pair z v.val ∈ g.val → v.val = F z := by
    intro z
    induction z using (codedEarlier_wellFounded κ).induction with
    | h z ih =>
      intro hz v hv
      let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz (stageLocalDomain_mem_L s)⟩
      have hzD : zL.val ∈ d.val := by rw [hdEq]; exact hz
      obtain ⟨q, out, hq, hout, hstep⟩ := hsteps zL hzD
      have hqEq : q.val = predecessorRestrictionGraph (stagePredecessors κ z) F := by
        apply ZFSet.ext
        intro pair
        constructor
        · intro hp
          let pL : LCarrier.{u} := ⟨pair, mem_L_of_mem hp q.property⟩
          obtain ⟨hpg, w, a, he, _, hrel⟩ := (hq pL).mp hp
          have hwz := (P.relation_exact w zL).mp hrel
          have hw := stageLocalDomain_closed s hz hwz
          have ha : a.val = F w.val := ih w.val hwz hw a (he ▸ hpg)
          apply mem_predecessorRestrictionGraph_iff.mpr
          exact ⟨w.val, mem_stagePredecessors.mpr hwz, by rw [← ha]; exact he.symm⟩
        · intro hp
          obtain ⟨w, hw, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
          have hwz := mem_stagePredecessors.mp hw
          have hwd := stageLocalDomain_closed s hz hwz
          let wL : LCarrier.{u} := ⟨w, mem_L_of_mem hwd (stageLocalDomain_mem_L s)⟩
          obtain ⟨a, ha, _⟩ := hfun.1 wL (by rw [hdEq]; exact hwd)
          have haF : a.val = F w := ih w hwz hwd a ha
          let pL : LCarrier.{u} := orderedPairLCarrier wL a
          have hpq : pL.val ∈ q.val := (hq pL).mpr
            ⟨ha, wL, a, rfl, (P.class_exact wL).mpr (stageLocalDomain_subset_stageSet s hwd),
              (P.relation_exact wL zL).mpr hwz⟩
          rw [← he, ← haF]
          exact hpq
      obtain ⟨t, ht⟩ := ZFSet.mem_range.mp (stageLocalDomain_subset_stageSet s hz)
      have houtEq : out.val = F z := by
        rw [(P.step_exact zL q out (stageLocalDomain_subset_stageSet s hz)).mp hstep, hqEq]
        change op z _ = F z
        rw [← ht]
        exact (hF t).symm
      obtain ⟨a, _, ha⟩ := hfun.1 zL hzD
      have hvo : v = out := (ha v hv).trans (ha out hout).symm
      rw [hvo, houtEq]
  apply ZFSet.ext
  intro pair
  constructor
  · intro hp
    let pL : LCarrier.{u} := ⟨pair, mem_L_of_mem hp g.property⟩
    obtain ⟨z, hz, v, he⟩ := hfun.2 pL hp
    have hz' : z.val ∈ stageLocalDomain s := hdEq ▸ hz
    have hv := hvalue z.val hz' v (he ▸ hp)
    exact mem_predecessorRestrictionGraph_iff.mpr ⟨z.val, hz', by rw [← hv]; exact he.symm⟩
  · intro hp
    obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
    let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz (stageLocalDomain_mem_L s)⟩
    obtain ⟨v, hv, _⟩ := hfun.1 zL (by rw [hdEq]; exact hz)
    rw [← he, ← hvalue z hz v hv]
    exact hv

include P hF in
/-- A constructible canonical local graph satisfies the fixed local-solution
formula. The predecessor restriction is supplied by actual L Separation. -/
theorem localSolution_of_graph_eq (s : Stage κ) (g : LCarrier.{u})
    (hg : g.val = stageLocalGraph F s) :
    FOFormula.Satisfies lCarrierMem
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, stageCode_mem_L s⟩) g) := by
  classical
  let d : LCarrier.{u} := ⟨stageLocalDomain s, stageLocalDomain_mem_L s⟩
  have hvalL (z : ZFSet.{u}) (hz : z ∈ d.val) : F z ∈ L :=
    value_mem_L_of_restrictionGraph hg g.property hz
  apply (satisfies_localSolutionFormula_lCarrier_iff _ _ _ _ _ _).mpr
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
    exact ⟨⟨z, mem_L_of_mem hz d.property⟩, hz, ⟨F z, hvalL z hz⟩, he.symm⟩
  · intro z hz
    let q := formulaRestrictionLCarrier P.classFormula P.relationFormula P.params g z
    have hqEq : q.val = predecessorRestrictionGraph (stagePredecessors κ z.val) F := by
      apply ZFSet.ext
      intro pair
      rw [mem_formulaRestrictionLCarrier_raw_iff]
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
        let wL : LCarrier.{u} := ⟨w, mem_L_of_mem hwd d.property⟩
        let a : LCarrier.{u} := ⟨F w, hvalL w hwd⟩
        refine ⟨?_, wL, a, he.symm,
          (P.class_exact wL).mpr (stageLocalDomain_subset_stageSet s hwd),
          (P.relation_exact wL z).mpr hwz⟩
        rw [hg, ← he]
        exact pair_mem_predecessorRestrictionGraph F hwd
    refine ⟨q, ⟨F z.val, hvalL z.val hz⟩, ?_, ?_, ?_⟩
    · exact mem_formulaRestrictionLCarrier_iff _ _ _ _ _
    · rw [hg]
      exact pair_mem_predecessorRestrictionGraph F hz
    · apply (P.step_exact z q _ (stageLocalDomain_subset_stageSet s hz)).mpr
      rw [hqEq]
      obtain ⟨t, ht⟩ := ZFSet.mem_range.mp (stageLocalDomain_subset_stageSet s hz)
      change F z.val = op z.val _
      rw [← ht]
      exact hF t

include P hF in
theorem localSolution_iff_graph_eq (s : Stage κ) (g : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, stageCode_mem_L s⟩) g) ↔
      g.val = stageLocalGraph F s :=
  ⟨P.localSolution_graph_eq F hF s g, P.localSolution_of_graph_eq F hF s g⟩

include P hF in
/-- Replacement collects already constructed local graphs on any internal
stage subdomain. Its functionality comes from the preceding uniqueness proof. -/
theorem collect_localGraphs (d : ZFSet.{u}) (hd : d ∈ L)
    (hsub : ∀ z ∈ d, z ∈ stageSet κ)
    (hlocal : ∀ s : Stage κ, stageCode s ∈ d → stageLocalGraph F s ∈ L) :
    ∃ family : LCarrier.{u}, ∀ g : ZFSet.{u}, g ∈ family.val ↔
      ∃ s : Stage κ, stageCode s ∈ d ∧ g = stageLocalGraph F s := by
  classical
  let φ := localSolutionFormula P.classFormula P.relationFormula P.stepFormula
  have hfun : ∀ x : LCarrier.{u}, x.val ∈ d → ∃! g : LCarrier.{u},
      FOFormula.Satisfies lCarrierMem φ (snoc (snoc P.params x) g) := by
    intro x hx
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hsub x.val hx)
    have hxEq : x = ⟨stageCode s, stageCode_mem_L s⟩ := Subtype.ext hs.symm
    have hsd : stageCode s ∈ d := hs ▸ hx
    refine ⟨⟨stageLocalGraph F s, hlocal s hsd⟩, ?_, ?_⟩
    · rw [hxEq]
      exact P.localSolution_of_graph_eq F hF s _ rfl
    · intro g hg
      apply Subtype.ext
      rw [hxEq] at hg
      exact P.localSolution_graph_eq F hF s g hg
  obtain ⟨family, hfamily⟩ := exists_replacementLCarrier φ P.params ⟨d, hd⟩ hfun
  refine ⟨family, ?_⟩
  intro g
  constructor
  · intro hg
    let gL : LCarrier.{u} := ⟨g, mem_L_of_mem hg family.property⟩
    obtain ⟨x, hx, hφ⟩ := (hfamily gL).mp hg
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hsub x.val hx)
    have hxEq : x = ⟨stageCode s, stageCode_mem_L s⟩ := Subtype.ext hs.symm
    rw [hxEq] at hφ
    exact ⟨s, hs ▸ hx, P.localSolution_graph_eq F hF s gL hφ⟩
  · rintro ⟨s, hs, rfl⟩
    let gL : LCarrier.{u} := ⟨stageLocalGraph F s, hlocal s hs⟩
    exact (hfamily gL).mpr ⟨⟨stageCode s, stageCode_mem_L s⟩, hs,
      P.localSolution_of_graph_eq F hF s gL rfl⟩

include P hF in
/-- The real well-founded induction: collect earlier local graphs by
Replacement, union them, and append the new value using one-step closure. -/
theorem stageLocalGraph_mem_L (s : Stage κ) : stageLocalGraph F s ∈ L := by
  classical
  induction s using (earlier_wellFounded κ).induction with
  | h s ih =>
    let d := stagePredecessors κ (stageCode s)
    have hsub : ∀ z ∈ d, z ∈ stageSet κ := fun z hz =>
      (stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz)
    have hlocal : ∀ t : Stage κ, stageCode t ∈ d → stageLocalGraph F t ∈ L := by
      intro t ht
      exact ih t ((codedEarlier_codes t s).mp (mem_stagePredecessors.mp ht))
    obtain ⟨family, hfamily⟩ := P.collect_localGraphs F hF d
      (stagePredecessors_mem_L s) hsub hlocal
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
    have hpredL : predecessorRestrictionGraph d F ∈ L :=
      hunion ▸ sUnion_mem_L family.property
    have htopL : F (stageCode s) ∈ L := by
      rw [hF s]
      exact P.step_mem_L ⟨stageCode s, stageCode_mem_L s⟩
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
    exact union_mem_L (singleton_mem_L (orderedPair_mem_L (stageCode_mem_L s) htopL)) hpredL

include P hF in
/-- The entire recursively specified graph is in L. No set-sized ZF model
is assumed, and no recursive graph constructibility is supplied as input. -/
theorem stageGraph_mem_L : predecessorRestrictionGraph (stageSet κ) F ∈ L := by
  obtain ⟨family, hfamily⟩ := P.collect_localGraphs F hF (stageSet κ) (stageSet_mem_L κ)
    (fun _ h => h) (fun s _ => P.stageLocalGraph_mem_L F hF s)
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
  exact heq ▸ sUnion_mem_L family.property

include P hF in
/-- The textbook value formula now defines the actual recursive values;
its existential local-graph witness is supplied by the proved construction. -/
theorem recursionValue_exact (s : Stage κ) (v : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem
      (recursionValueFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, stageCode_mem_L s⟩) v) ↔
      v.val = F (stageCode s) := by
  rw [satisfies_recursionValueFormula_lCarrier_iff]
  constructor
  · rintro ⟨_, g, hg, hv⟩
    rw [P.localSolution_graph_eq F hF s g hg] at hv
    exact (pair_mem_restrictionGraph_iff.mp hv).2
  · intro hv
    let g : LCarrier.{u} := ⟨stageLocalGraph F s, P.stageLocalGraph_mem_L F hF s⟩
    refine ⟨(P.class_exact _).mpr (stageCode_mem_stageSet s), g,
      P.localSolution_of_graph_eq F hF s g rfl, ?_⟩
    rw [hv]
    exact pair_mem_predecessorRestrictionGraph F
      ((mem_stageLocalDomain s _).mpr (Or.inl rfl))

end StageStepPresentation
end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.StageStepPresentation.localSolution_graph_eq
#print axioms OneYTruth.ExternalTower.StageStepPresentation.stageLocalGraph_mem_L
#print axioms OneYTruth.ExternalTower.StageStepPresentation.stageGraph_mem_L
#print axioms OneYTruth.ExternalTower.StageStepPresentation.recursionValue_exact


