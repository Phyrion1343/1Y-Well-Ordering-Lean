import OneYTruth.InternalActualStep

/-! The explicit twenty-one-witness semantics, useful when a whole tower
collects every local tuple under a common internal bound. -/

namespace OneYTruth.GraphStepSigma

open Constructible Constructible.Delta0Formula

universe u v

theorem realize_query_iff_matrix {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 16 → ZFCarrier V) :
    OneYTruth.realize N (query K J) Empty.elim p ↔
      ∃ w : Fin 21 → ZFCarrier V,
        Satisfies ZFMem matrix (val (Fin.append p w)) := by
  rw [realize_query_iff_fo]
  change FOFormula.Satisfies N.mem (FiniteExistentialBlock.bind 16 21 matrix.toFO) p ↔ _
  rw [FiniteExistentialBlock.satisfies_bind]
  apply exists_congr
  intro w
  rw [satisfies_toFO,hmem,satisfies_absolute hV]

end OneYTruth.GraphStepSigma
