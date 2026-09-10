import OneYTruth.ConstructibleProductRanges

/-! Bounded filters for the actual relations read from a predecessor graph. -/

namespace OneYTruth.PredecessorGraph

open Constructible Constructible.Delta0Formula Constructible.Godel
open Constructible.FiniteSequenceZF BoundedEvaluation AtomicRelationGraphs FiniteCodeFormula

universe u v

def interpretation (k : Nat) {I : Type v} (U : ZFSet.{u})
    (indexCode : I → ZFSet.{u}) (κ q : ZFSet.{u}) : Interpretation k I (ZFCarrier U) where
  mem x y := x.val ∈ y.val
  named i e a := Read q (natCode k) (indexCode i) e.val a.val
  diagonal j ξ e a := ξ.val ∈ κ ∧ Read q (natCode j.val) ξ.val e.val a.val

/-- Parameters q, block, alphabet, domain, candidate. -/
def namedFormula : Delta0Formula 5 :=
  .boundedEx 2 (.boundedEx 3 (.boundedEx 3
    (.conj (tripleEqAt 4 5 6 7) (readAt 0 1 5 6 7))))

theorem satisfies_namedFormula (q b A U p : ZFSet.{u}) :
    Satisfies ZFMem namedFormula ![q,b,A,U,p] ↔
      ∃ ξ ∈ A, ∃ e ∈ U, ∃ a ∈ U, p = triple ξ e a ∧ Read q b ξ e a := by
  simp only [namedFormula, Satisfies, satisfies_tripleEqAt, satisfies_readAt,
    snoc_last, snoc_castSucc]
  rfl

/-- Parameters q, ordinal bound, finite block codes, domain, candidate. -/
def diagonalFormula : Delta0Formula 5 :=
  .boundedEx 2 (.boundedEx 3 (.boundedEx 3 (.boundedEx 3
    (.conj (chainEqAt 3 ![5,6,7] 4 8)
      (.conj (.mem 6 1) (readAt 0 5 6 7 8))))))

theorem satisfies_diagonalFormula (q κ B U p : ZFSet.{u}) :
    Satisfies ZFMem diagonalFormula ![q,κ,B,U,p] ↔
      ∃ b ∈ B, ∃ ξ ∈ U, ∃ e ∈ U, ∃ a ∈ U,
        p = quad b ξ e a ∧ ξ ∈ κ ∧ Read q b ξ e a := by
  simp only [diagonalFormula, Satisfies, satisfies_chainEqAt, satisfies_readAt,
    snoc_last, snoc_castSucc]
  change (∃ b ∈ B, ∃ ξ ∈ U, ∃ e ∈ U, ∃ a ∈ U,
    p = chainCode a (List.ofFn ![b,ξ,e]) ∧ ξ ∈ κ ∧ Read q b ξ e a) ↔ _
  simp [chainCode, List.ofFn_succ, quad, triple]

attribute [irreducible] namedFormula diagonalFormula

theorem satisfies_namedFormula_triple (q b A U ξ e a : ZFSet.{u})
    (hξ : ξ ∈ A) (he : e ∈ U) (ha : a ∈ U) :
    Satisfies ZFMem namedFormula ![q,b,A,U,triple ξ e a] ↔ Read q b ξ e a := by
  rw [satisfies_namedFormula]
  constructor
  · rintro ⟨x, _, y, _, z, _, heq, h⟩
    obtain ⟨hx, hyz⟩ := ZFSet.pair_inj.mp heq
    obtain ⟨hy, hz⟩ := ZFSet.pair_inj.mp hyz
    subst x y z
    exact h
  · intro h
    exact ⟨ξ,hξ,e,he,a,ha,rfl,h⟩

theorem satisfies_diagonalFormula_quad (q κ B U b ξ e a : ZFSet.{u})
    (hb : b ∈ B) (hξ : ξ ∈ U) (he : e ∈ U) (ha : a ∈ U) :
    Satisfies ZFMem diagonalFormula ![q,κ,B,U,quad b ξ e a] ↔ ξ ∈ κ ∧ Read q b ξ e a := by
  rw [satisfies_diagonalFormula]
  constructor
  · rintro ⟨b', _, x, _, y, _, z, _, heq, hκ, h⟩
    obtain ⟨hb', hxyz⟩ := ZFSet.pair_inj.mp heq
    obtain ⟨hx, hyz⟩ := ZFSet.pair_inj.mp hxyz
    obtain ⟨hy, hz⟩ := ZFSet.pair_inj.mp hyz
    subst b' x y z
    exact ⟨hκ,h⟩
  · rintro ⟨hκ,h⟩
    exact ⟨b,hb,ξ,hξ,e,he,a,ha,rfl,hκ,h⟩

end OneYTruth.PredecessorGraph
