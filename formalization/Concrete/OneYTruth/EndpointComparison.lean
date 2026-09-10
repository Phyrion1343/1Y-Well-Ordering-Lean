import OneYTruth.RootComparison

/-!
# Bounded comparisons with an available endpoint truth predicate

The endpoint truth is queried by an actual named or lower-diagonal atom.
It is never inserted as a set parameter. The other parameters remain explicit:
a bound for pair components, the Sigma-one nodes, and the smaller truth set.
-/

namespace OneYTruth.EndpointComparison

open Constructible FirstOrder FirstOrder.Language BoundedEvaluation

universe u v

def pairQuery {k : Nat} {I : Type u} {n : Nat} (r e a : Fin n) :
    (language k I).BoundedFormula Empty n :=
  ofConstructibleDeltaZero k I (pairMemAt r e a)

theorem pairQuery_isDeltaZero {k : Nat} {I : Type u} {n : Nat} (r e a : Fin n) :
    IsDeltaZero (pairQuery (k := k) (I := I) r e a) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_pairQuery {k : Nat} {I : Type u} {W : ZFSet.{v}}
    (hW : W.IsTransitive) (M : Interpretation k I (ZFCarrier W))
    (hmem : M.mem = zfCarrierMem W) {n : Nat} (r e a : Fin n)
    (p : Fin n → ZFCarrier W) :
    realize M (pairQuery r e a) Empty.elim p ↔
      ZFSet.pair (p e).val (p a).val ∈ (p r).val := by
  rw [pairQuery, realize_ofConstructibleDeltaZero_absolute hW M hmem,
    satisfies_pairMemAt]
  rfl

/-- Layout: component bound, nodes, smaller truth, optional ordinal index; then e,a. -/
def comparison {k : Nat} {I : Type u}
    (query : (language k I).BoundedFormula Empty 6) :
    (language k I).BoundedFormula Empty 4 :=
  boundedAll (.var (.inr 0)) (boundedAll (.var (.inr 0))
    ((pairQuery 1 4 5).imp ((pairQuery 2 4 5).iff query)))

theorem comparison_isDeltaZero {k : Nat} {I : Type u}
    {query : (language k I).BoundedFormula Empty 6} (hq : IsDeltaZero query) :
    IsDeltaZero (comparison query) := by
  apply IsDeltaZero.boundedAll
  apply IsDeltaZero.boundedAll
  apply IsDeltaZero.imp (pairQuery_isDeltaZero _ _ _)
  exact .imp (.imp (.imp (pairQuery_isDeltaZero _ _ _) hq)
    (.imp (.imp hq (pairQuery_isDeltaZero _ _ _)) .falsum)) .falsum

theorem realize_comparison {k : Nat} {I : Type u} {W : ZFSet.{v}}
    (hW : W.IsTransitive) (M : Interpretation k I (ZFCarrier W))
    (hmem : M.mem = zfCarrierMem W)
    (query : (language k I).BoundedFormula Empty 6) (p : Fin 4 → ZFCarrier W) :
    realize M (comparison query) Empty.elim p ↔
      ∀ e : ZFCarrier W, e.val ∈ (p 0).val →
        ∀ a : ZFCarrier W, a.val ∈ (p 0).val →
          ZFSet.pair e.val a.val ∈ (p 1).val →
            (ZFSet.pair e.val a.val ∈ (p 2).val ↔
              realize M query Empty.elim (Fin.snoc (Fin.snoc p e) a)) := by
  letI := M.structure
  unfold comparison
  rw [realize_boundedAll]
  change (∀ e : ZFCarrier W, M.mem e (p 0) → _) ↔ _
  simp only [hmem, zfCarrierMem]
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro he
  rw [realize_boundedAll]
  change (∀ a : ZFCarrier W, M.mem a ((Fin.snoc p e : Fin 5 → ZFCarrier W) 0) → _) ↔ _
  simp only [hmem, zfCarrierMem]
  apply forall_congr'
  intro a
  change (_ → realize M ((pairQuery 1 4 5).imp ((pairQuery 2 4 5).iff query))
    Empty.elim (Fin.snoc (Fin.snoc p e) a)) ↔ _
  have hbase : ((Fin.snoc p e : Fin 5 → ZFCarrier W) 0).val = (p 0).val := rfl
  rw [hbase]
  apply imp_congr_right
  intro ha
  change (((pairQuery 1 4 5 : (language k I).BoundedFormula Empty 6).Realize Empty.elim
      (Fin.snoc (Fin.snoc p e) a)) → _) ↔ _
  rw [BoundedFormula.realize_iff]
  change (realize M (pairQuery 1 4 5) Empty.elim (Fin.snoc (Fin.snoc p e) a) →
    (realize M (pairQuery 2 4 5) Empty.elim (Fin.snoc (Fin.snoc p e) a) ↔ _)) ↔ _
  rw [realize_pairQuery hW M hmem, realize_pairQuery hW M hmem]
  rfl

def namedQuery {k : Nat} {I : Type u} (ξ : I) : (language k I).BoundedFormula Empty 6 :=
  .rel (.named ξ) ![.var (.inr 4), .var (.inr 5)]

def diagonalQuery {k : Nat} {I : Type u} (j : Fin k) :
    (language k I).BoundedFormula Empty 6 :=
  .rel (.diagonal j) ![.var (.inr 3), .var (.inr 4), .var (.inr 5)]

theorem named_comparison_isDeltaZero {k : Nat} {I : Type u} (ξ : I) :
    IsDeltaZero (comparison (namedQuery (k := k) ξ)) := comparison_isDeltaZero (.rel _ _)

theorem diagonal_comparison_isDeltaZero {k : Nat} {I : Type u} (j : Fin k) :
    IsDeltaZero (comparison (diagonalQuery (I := I) j)) := comparison_isDeltaZero (.rel _ _)

theorem realize_named_comparison {k : Nat} {I : Type u} {W : ZFSet.{v}}
    (hW : W.IsTransitive) (M : Interpretation k I (ZFCarrier W))
    (hmem : M.mem = zfCarrierMem W) (ξ : I) (p : Fin 4 → ZFCarrier W) :
    realize M (comparison (namedQuery ξ)) Empty.elim p ↔
      ∀ e : ZFCarrier W, e.val ∈ (p 0).val →
        ∀ a : ZFCarrier W, a.val ∈ (p 0).val →
          ZFSet.pair e.val a.val ∈ (p 1).val →
            (ZFSet.pair e.val a.val ∈ (p 2).val ↔ M.named ξ e a) := by
  rw [realize_comparison hW M hmem]
  rfl

theorem realize_diagonal_comparison {k : Nat} {I : Type u} {W : ZFSet.{v}}
    (hW : W.IsTransitive) (M : Interpretation k I (ZFCarrier W))
    (hmem : M.mem = zfCarrierMem W) (j : Fin k) (p : Fin 4 → ZFCarrier W) :
    realize M (comparison (diagonalQuery j)) Empty.elim p ↔
      ∀ e : ZFCarrier W, e.val ∈ (p 0).val →
        ∀ a : ZFCarrier W, a.val ∈ (p 0).val →
          ZFSet.pair e.val a.val ∈ (p 1).val →
            (ZFSet.pair e.val a.val ∈ (p 2).val ↔ M.diagonal j (p 3) e a) := by
  rw [realize_comparison hW M hmem]
  rfl

end OneYTruth.EndpointComparison
