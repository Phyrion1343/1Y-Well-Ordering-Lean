import OneYTruth.InternalIterationUnion
import OneYTruth.InternalBoundedIteration

/-! # A complete Sigma-one candidate check for every displayed bounded grammar

Both the exact step graph and the internal step closure are proved from the
actual bounded filter. They are not hypotheses of the grammar query.
-/

namespace OneYTruth.InternalBoundedIteration

open Constructible Constructible.Delta0Formula InternalClosure
open ConstructibleBoundedIteration InternalIteration

universe u v

def grammarQueryAt (k : Nat) (I : Type v) {p n : Nat}
    (φ : Delta0Formula (p+2)) (bound : Fin p) (params : Fin p → Fin n)
    (initial omega zero out : Fin n) :=
  unionQueryAt k I (filterGraph φ bound) params initial omega zero out

theorem grammarQueryAt_isSigmaOne (k : Nat) (I : Type v) {p n : Nat}
    (φ : Delta0Formula (p+2)) (bound : Fin p) (params : Fin p → Fin n)
    (initial omega zero out : Fin n) :
    IsSigmaOne (grammarQueryAt k I φ bound params initial omega zero out) :=
  unionQueryAt_isSigmaOne k I _ _ _ _ _ _

theorem realize_grammarQueryAt_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {p n : Nat} (φ : Delta0Formula (p+2)) (bound : Fin p)
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) :
    OneYTruth.realize N (grammarQueryAt k I φ bound params initial omega zero out) Empty.elim s ↔
      (s out).val = ZFSet.sUnion
        (InternalIteration.family (step φ bound (fun i => (s (params i)).val)) (s initial).val) := by
  apply realize_unionQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    (filterGraph φ bound) params initial omega zero out s hOmega hZero
    (step φ bound (fun i => (s (params i)).val))
    (fun S T => satisfies_filterGraph φ bound _ S T)
  intro S hS
  have h := deltaSep_mem hV N hmem hSep φ (Fin.snoc (fun i => s (params i)) ⟨S, hS⟩)
    (s (params bound)).property
  have he : (fun i => ((Fin.snoc (fun i : Fin p => s (params i)) (⟨S, hS⟩ : ZFCarrier V) :
      Fin (p+1) → ZFCarrier V) i).val) = snoc (fun i => (s (params i)).val) S := by
    rw [constructible_snoc_eq]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [he] at h
  exact h

end OneYTruth.InternalBoundedIteration

#print axioms OneYTruth.InternalBoundedIteration.realize_grammarQueryAt_iff
