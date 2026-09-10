import OneYTruth.Auxiliary
import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections
import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalWellOrder

/-!
# The auxiliary predicate is a fixed pure membership formula with a set parameter

This is the literal code used by uniformSet: ((block,index),(formula,assignment))
belongs to W. Both intermediate pairs are represented explicitly. No truth
predicate or definability premise is hidden in the formula compiler.
-/

namespace OneYTruth.AuxiliaryCode

open Constructible Constructible.Model Constructible.ContinuumFormula

universe u

/-- Layout [W,block,index,formula,assignment], then the two pair witnesses. -/
def relationFormula : FOFormula 5 :=
  .ex (.ex (.conj
    (kuratowskiPairAt (5 : Fin 7) (1 : Fin 7) (2 : Fin 7))
    (.conj (kuratowskiPairAt (6 : Fin 7) (3 : Fin 7) (4 : Fin 7))
      (FOFormula.rename ![(0 : Fin 7), (5 : Fin 7), (6 : Fin 7)] graphRelFormula))))

theorem satisfies_relationFormula (s : Tuple LCarrier.{u} 5) :
    FOFormula.Satisfies lCarrierMem relationFormula s ↔
      ZFSet.pair (ZFSet.pair (s 1).val (s 2).val)
        (ZFSet.pair (s 3).val (s 4).val) ∈ (s 0).val := by
  change (∃ p q : LCarrier.{u},
    FOFormula.Satisfies lCarrierMem
      (kuratowskiPairAt (5 : Fin 7) (1 : Fin 7) (2 : Fin 7)) (snoc (snoc s p) q) ∧
    FOFormula.Satisfies lCarrierMem
      (kuratowskiPairAt (6 : Fin 7) (3 : Fin 7) (4 : Fin 7)) (snoc (snoc s p) q) ∧
    FOFormula.Satisfies lCarrierMem
      (FOFormula.rename ![(0 : Fin 7), (5 : Fin 7), (6 : Fin 7)] graphRelFormula)
      (snoc (snoc s p) q)) ↔ _
  simp only [satisfies_kuratowskiPairAt, FOFormula.satisfies_rename,
    satisfies_graphRelFormula]
  change (∃ p q : LCarrier.{u}, IsKuratowskiPairOf lCarrierMem p (s 1) (s 2) ∧
    IsKuratowskiPairOf lCarrierMem q (s 3) (s 4) ∧ GraphRel (s 0) p q) ↔ _
  simp only [isKuratowskiPairOf_lCarrier_iff, GraphRel]
  constructor
  · rintro ⟨p, q, hp, hq, hW⟩
    simpa only [hp, hq] using hW
  · intro hW
    exact ⟨orderedPairLCarrier (s 1) (s 2), orderedPairLCarrier (s 3) (s 4),
      rfl, rfl, hW⟩

end OneYTruth.AuxiliaryCode
