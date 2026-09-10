import OneYTruth.BoundedGrammarCertificate

/-! Soundness of a grammar certificate requires no Collection or Separation. -/

namespace OneYTruth.InternalBoundedIteration

open Constructible Constructible.Delta0Formula ConstructibleBoundedIteration InternalIteration

universe u v

theorem grammarQueryAt_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {p n : Nat}
    (φ : Delta0Formula (p+2)) (bound : Fin p) (params : Fin p → Fin n)
    (initial omega zero out : Fin n) (s : Fin n → ZFCarrier V)
    (hOmega : (s omega).val = Ordinal.omega0.toZFSet) (hZero : (s zero).val = ∅)
    (h : OneYTruth.realize N (grammarQueryAt k I φ bound params initial omega zero out) Empty.elim s) :
    (s out).val = ZFSet.sUnion
      (InternalIteration.family (step φ bound (fun i => (s (params i)).val)) (s initial).val) :=
  unionQueryAt_sound hV N hmem (filterGraph φ bound) params initial omega zero out s hOmega hZero
    (step φ bound (fun i => (s (params i)).val))
    (fun S T => satisfies_filterGraph φ bound _ S T) h

end OneYTruth.InternalBoundedIteration
