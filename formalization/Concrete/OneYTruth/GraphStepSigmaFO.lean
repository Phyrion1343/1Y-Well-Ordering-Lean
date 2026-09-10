import OneYTruth.GraphStepSigmaComplete

/-! The same literal Sigma-one certificate in the pure library syntax, with
semantics proved on the actual smaller carrier. -/

namespace OneYTruth.GraphStepSigma

open Constructible

universe u v

def foFormula : FOFormula 16 :=
  FiniteExistentialBlock.bind 16 18 (.ex (.ex (.ex matrix.toFO)))

theorem realize_query_iff_fo {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 16 → A) :
    OneYTruth.realize N (query K J) Empty.elim p ↔
      FOFormula.Satisfies N.mem foFormula p := by
  rw [query, ScopedExistentialBlock.realize_bind,foFormula,FiniteExistentialBlock.satisfies_bind]
  apply exists_congr
  intro w
  simp only [partialQuery,realize_scoped_ex,FOFormula.Satisfies,
    realize_ofConstructibleDeltaZero,Delta0Formula.satisfies_toFO,constructible_snoc_eq]

end OneYTruth.GraphStepSigma
