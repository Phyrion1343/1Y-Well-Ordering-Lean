import OneYTruth.RootSemantics
import OneYTruth.ClosedSigmaMaps
import OneYTruth.SigmaComparison

/-!
# Actual root relations and bounded comparisons of their canonical truth sets

The three set parameters are explicit. This file proves the comparison's
meaning and complexity, without asserting that these parameters are already
members of the ambient stage or that a tower certificate has been built.
-/

namespace OneYTruth.RootSemantics

open Constructible FirstOrder FirstOrder.Language ExternalTower SigmaComparison FormulaCode

universe u v

theorem R_iff_closed {k : Nat} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b) :
    R k η a b ↔
      ClosedSigmaOneMap (interpretation (LStageZF a) (k, ⟨η, hηa⟩))
        (interpretation (LStageZF b) (k, ⟨η, hηa.trans hab.le⟩))
        (Auxiliary.inclusion (LStageZF_mono hab.le)) := by
  constructor
  · rintro ⟨_, _, hf⟩
    exact (sigmaOneMap_iff_closed _ _ _).mp hf
  · intro hf
    exact ⟨hηa, hab, (sigmaOneMap_iff_closed _ _ _).mpr hf⟩

theorem R_iff_truth_agree {k : Nat} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b) :
    R k η a b ↔
      Agree (sigmaNodes (k := k) (ordinalIndexCode (η := η)) (LStageZF a))
        (truth (LStageZF a) (k, ⟨η, hηa⟩))
        (truth (LStageZF b) (k, ⟨η, hηa.trans hab.le⟩)) := by
  rw [R_iff_closed hηa hab, truth_eq_satisfactionSet, truth_eq_satisfactionSet]
  exact (agree_satisfaction_iff_closed ordinalIndexCode ordinalIndexCode_injective
    _ _ (Auxiliary.inclusion (LStageZF_mono hab.le)) (fun _ => rfl)).symm

theorem realize_comparison_iff_R {k : Nat} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    {W : ZFSet.{u}} {K : Nat} {J : Type v} (hW : W.IsTransitive)
    (A : Interpretation K J (ZFCarrier W)) (hmem : A.mem = zfCarrierMem W)
    (p : Fin 3 → ZFCarrier W)
    (hp : ∀ i, (p i).val = parameters
      (sigmaNodes (k := k) (ordinalIndexCode (η := η)) (LStageZF a))
      (truth (LStageZF a) (k, ⟨η, hηa⟩))
      (truth (LStageZF b) (k, ⟨η, hηa.trans hab.le⟩)) i) :
    realize A (mixedComparisonFormula K J) Empty.elim p ↔ R k η a b :=
  (realize_mixedComparisonFormula hW A hmem _ _ _ p hp).trans
    (R_iff_truth_agree hηa hab).symm

end OneYTruth.RootSemantics

#print axioms OneYTruth.RootSemantics.R_iff_truth_agree
#print axioms OneYTruth.RootSemantics.realize_comparison_iff_R
