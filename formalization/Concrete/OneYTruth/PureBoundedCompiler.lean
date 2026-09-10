import OneYTruth.PureDefTranslation
import OneYTruth.InternalFiniteRanges

/-! Compile genuine pure Delta-zero syntax back to the native bounded
syntax. A displayed coordinate represents falsity without an unbounded
quantifier. -/

namespace OneYTruth.PureBoundedCompiler

open Constructible Constructible.Delta0Formula FirstOrder FirstOrder.Language
open PureDefTranslation

universe u

theorem exists_native {n : Nat} {φ : (language 0 Empty).BoundedFormula Empty n}
    (hφ : IsDeltaZero φ) (hn : 0 < n) :
    ∃ δ : Delta0Formula n, ∀ (A : Type u) (M : Interpretation 0 Empty A) (p : Fin n → A),
      Satisfies M.mem δ p ↔ realize M φ Empty.elim p := by
  induction hφ with
  | @falsum n =>
      refine ⟨.neg (.eq ⟨0,hn⟩ ⟨0,hn⟩),?_⟩
      intro A M p
      simp [Satisfies,realize,BoundedFormula.Realize]
  | equal t s =>
      refine ⟨.eq (termIndex t) (termIndex s),?_⟩
      intro A M p
      change (p (termIndex t) = p (termIndex s)) ↔ _
      rw [← realize_termIndex M t p,← realize_termIndex M s p]
      rfl
  | rel r ts =>
      cases r with
      | mem =>
          refine ⟨.mem (termIndex (ts 0)) (termIndex (ts 1)),?_⟩
          intro A M p
          change M.mem (p (termIndex (ts 0))) (p (termIndex (ts 1))) ↔ _
          rw [← realize_termIndex M (ts 0) p,← realize_termIndex M (ts 1) p]
          rfl
      | named i => exact i.elim
      | diagonal i => exact Fin.elim0 i
  | imp hφ hψ ihφ ihψ =>
      obtain ⟨δ,hδ⟩ := ihφ hn
      obtain ⟨ε,hε⟩ := ihψ hn
      refine ⟨.imp δ ε,?_⟩
      intro A M p
      rw [satisfies_imp,hδ,hε]
      rfl
  | @boundedAll n t φ hφ ih =>
      obtain ⟨δ,hδ⟩ := ih (Nat.zero_lt_succ n)
      refine ⟨.boundedAll (termIndex t) δ,?_⟩
      intro A M p
      rw [satisfies_boundedAll,realize_boundedAll,realize_termIndex]
      simp only [constructible_snoc_eq,hδ]

end OneYTruth.PureBoundedCompiler
