import OneYTruth.InternalRecursionEnvironment

/-! Exact local-solution semantics on any transitive set carrier. -/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model

universe u

theorem satisfies_localSolutionFormula_carrier_iff {V : ZFSet.{u}}
    (hV : V.IsTransitive) {n : Nat} (cf : FOFormula (n + 1))
    (rf : FOFormula (n + 2)) (sf : FOFormula (n + 3))
    (ps : Tuple (ZFCarrier V) n) (x g : ZFCarrier V) :
    FOFormula.Satisfies (zfCarrierMem V) (localSolutionFormula cf rf sf)
      (snoc (snoc ps x) g) ↔
      ∃ d : ZFCarrier V,
        FOFormula.Satisfies (zfCarrierMem V) (localDomainFormula cf rf)
          (snoc (snoc ps x) d) ∧
        (((∀ z : ZFCarrier V, z.val ∈ d.val → ∃ v : ZFCarrier V,
            ZFSet.pair z.val v.val ∈ g.val ∧ ∀ w : ZFCarrier V,
              ZFSet.pair z.val w.val ∈ g.val → w = v) ∧
          ∀ p : ZFCarrier V, p.val ∈ g.val → ∃ z : ZFCarrier V,
            z.val ∈ d.val ∧ ∃ v : ZFCarrier V, p.val = ZFSet.pair z.val v.val) ∧
        ∀ z : ZFCarrier V, z.val ∈ d.val → ∃ q v : ZFCarrier V,
          (∀ p : ZFCarrier V, p.val ∈ q.val ↔ p.val ∈ g.val ∧
            ∃ a b : ZFCarrier V, p.val = ZFSet.pair a.val b.val ∧
              FOFormula.Satisfies (zfCarrierMem V) cf (snoc ps a) ∧
              FOFormula.Satisfies (zfCarrierMem V) rf (snoc (snoc ps a) z)) ∧
          ZFSet.pair z.val v.val ∈ g.val ∧
          FOFormula.Satisfies (zfCarrierMem V) sf (snoc (snoc (snoc ps z) q) v)) := by
  have ht := satisfies_zfCarrier_iff_satisfiesIn V
    (localSolutionFormula cf rf sf) (snoc (snoc ps x) g)
  apply ht.trans
  simp only [subtypeVal_snoc]
  rw [satisfiesIn_localSolutionFormula_iff hV cf rf sf
    (fun i => (ps i).val) x.val g.val (fun i => (ps i).property) x.property g.property]
  simp_rw [satisfies_zfCarrier_iff_satisfiesIn, subtypeVal_snoc]
  simp only [Subtype.exists, Subtype.forall, Subtype.mk.injEq, exists_prop]

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.satisfies_localSolutionFormula_carrier_iff
