import OneYTruth.InternalLocalSolutionFormula

/-! # Exact internal step presentations and uniqueness of their local graphs

The step's exactness is explicitly on the displayed smaller carrier.
It is not inferred from arbitrary first-order exactness on L. A canonical
bounded certificate must supply this interface in the final instance.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

structure InternalStagePresentation (V : ZFSet.{u}) (κ : Ordinal.{u})
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) where
  env : RecursionEnvironment V
  source_mem : stageSet κ ∈ V
  arity : Nat
  params : Tuple (ZFCarrier V) arity
  classFormula : FOFormula (arity + 1)
  relationFormula : FOFormula (arity + 2)
  stepFormula : FOFormula (arity + 3)
  class_exact : ∀ z : ZFCarrier V,
    FOFormula.Satisfies (zfCarrierMem V) classFormula (snoc params z) ↔ z.val ∈ stageSet κ
  relation_exact : ∀ y z : ZFCarrier V,
    FOFormula.Satisfies (zfCarrierMem V) relationFormula (snoc (snoc params y) z) ↔
      CodedEarlier κ y.val z.val
  step_exact : ∀ x q v : ZFCarrier V, x.val ∈ stageSet κ →
    (FOFormula.Satisfies (zfCarrierMem V) stepFormula (snoc (snoc (snoc params x) q) v) ↔
      v.val = op x.val q.val)
  step_mem : ∀ x q : ZFCarrier V, x.val ∈ stageSet κ → op x.val q.val ∈ V

namespace InternalStagePresentation

variable {V : ZFSet.{u}} {κ : Ordinal.{u}} {op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
variable (P : InternalStagePresentation V κ op)

theorem class_raw (z : ZFSet.{u}) (hz : z ∈ V) :
    SatisfiesIn (V : Set ZFSet.{u}) P.classFormula (snoc (fun i => (P.params i).val) z) ↔
      z ∈ stageSet κ := by
  have h := satisfies_zfCarrier_iff_satisfiesIn V P.classFormula (snoc P.params ⟨z, hz⟩)
  simpa only [subtypeVal_snoc] using h.symm.trans (P.class_exact ⟨z, hz⟩)

theorem relation_raw (y : ZFSet.{u}) (hy : y ∈ V) (z : ZFSet.{u}) (hz : z ∈ V) :
    SatisfiesIn (V : Set ZFSet.{u}) P.relationFormula
      (snoc (snoc (fun i => (P.params i).val) y) z) ↔ CodedEarlier κ y z := by
  have h := satisfies_zfCarrier_iff_satisfiesIn V P.relationFormula
    (snoc (snoc P.params ⟨y, hy⟩) ⟨z, hz⟩)
  simpa only [subtypeVal_snoc] using h.symm.trans (P.relation_exact ⟨y, hy⟩ ⟨z, hz⟩)

theorem localDomain_exact (s : Stage κ) (d : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V) (localDomainFormula P.classFormula P.relationFormula)
      (snoc (snoc P.params ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩) d) ↔
      d.val = stageLocalDomain s := by
  apply (satisfies_zfCarrier_iff_satisfiesIn V _ _).trans
  simp only [subtypeVal_snoc]
  have h := satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain P.env.transitive
    (A := (stageSet κ : Set ZFSet.{u})) (R := stageClassRelation κ)
    P.classFormula P.relationFormula (fun i => (P.params i).val)
    P.class_raw P.relation_raw (stage_relationOn κ) (stage_setPredecessors κ)
    (fun _ _ _ hy _ => P.env.transitive.mem_trans hy P.source_mem)
    (x := stageCode s) (domain := d.val) (P.env.stageCode_mem P.source_mem s)
    (stageCode_mem_stageSet s) d.property (by
      rw [localRecursionDomain_eq_stage]
      exact P.env.stageLocalDomain_mem P.source_mem s)
  simpa only [localRecursionDomain_eq_stage] using h

variable (F : ZFSet.{u} → ZFSet.{u})
variable (hF : ∀ s : Stage κ, F (stageCode s) =
  op (stageCode s) (predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) F))
include P hF in
/-- Any internally checked local solution has exactly the external recursively
specified values. This uses actual well-founded induction on the coded order. -/
theorem localSolution_graph_eq (s : Stage κ) (g : ZFCarrier V)
    (hg : FOFormula.Satisfies (zfCarrierMem V)
      (localSolutionFormula P.classFormula P.relationFormula P.stepFormula)
      (snoc (snoc P.params ⟨stageCode s, P.env.stageCode_mem P.source_mem s⟩) g)) :
    g.val = stageLocalGraph F s := by
  classical
  obtain ⟨d, hd, hfun, hsteps⟩ :=
    (satisfies_localSolutionFormula_carrier_iff P.env.transitive _ _ _ _ _ _).mp hg
  have hdEq := (P.localDomain_exact s d).mp hd
  have hvalue : ∀ z : ZFSet.{u}, z ∈ stageLocalDomain s →
      ∀ v : ZFCarrier V, ZFSet.pair z v.val ∈ g.val → v.val = F z := by
    intro z
    induction z using (codedEarlier_wellFounded κ).induction with
    | h z ih =>
      intro hz v hv
      let zL : ZFCarrier V := ⟨z, P.env.transitive.mem_trans hz (P.env.stageLocalDomain_mem P.source_mem s)⟩
      have hzD : zL.val ∈ d.val := by rw [hdEq]; exact hz
      obtain ⟨q, out, hq, hout, hstep⟩ := hsteps zL hzD
      have hqEq : q.val = predecessorRestrictionGraph (stagePredecessors κ z) F := by
        apply ZFSet.ext
        intro pair
        constructor
        · intro hp
          let pL : ZFCarrier V := ⟨pair, P.env.transitive.mem_trans hp q.property⟩
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
          let wL : ZFCarrier V := ⟨w, P.env.transitive.mem_trans hwd (P.env.stageLocalDomain_mem P.source_mem s)⟩
          obtain ⟨a, ha, _⟩ := hfun.1 wL (by rw [hdEq]; exact hwd)
          have haF : a.val = F w := ih w hwz hwd a ha
          let pL : ZFCarrier V := (⟨ZFSet.pair wL.val a.val, P.env.orderedPair_mem wL.property a.property⟩ : ZFCarrier V)
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
    let pL : ZFCarrier V := ⟨pair, P.env.transitive.mem_trans hp g.property⟩
    obtain ⟨z, hz, v, he⟩ := hfun.2 pL hp
    have hz' : z.val ∈ stageLocalDomain s := hdEq ▸ hz
    have hv := hvalue z.val hz' v (he ▸ hp)
    exact mem_predecessorRestrictionGraph_iff.mpr ⟨z.val, hz', by rw [← hv]; exact he.symm⟩
  · intro hp
    obtain ⟨z, hz, he⟩ := mem_predecessorRestrictionGraph_iff.mp hp
    let zL : ZFCarrier V := ⟨z, P.env.transitive.mem_trans hz (P.env.stageLocalDomain_mem P.source_mem s)⟩
    obtain ⟨v, hv, _⟩ := hfun.1 zL (by rw [hdEq]; exact hz)
    rw [← he, ← hvalue z hz v hv]
    exact hv

end InternalStagePresentation
end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.InternalStagePresentation.localDomain_exact

