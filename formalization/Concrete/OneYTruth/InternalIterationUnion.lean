import OneYTruth.IterationUnionCertificate
import OneYTruth.InternalFullHistory

/-! The actual internal history supplies the witnesses of the bounded
complete-family certificate. No candidate graph or family is assumed. -/

namespace OneYTruth.InternalIteration

open Constructible Constructible.Delta0Formula InternalClosure

universe u v

theorem realize_unionQueryAt_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ
      (snoc (snoc (fun a => (s (params a)).val) S) T) ↔ T = step S)
    (hclosed : ∀ S ∈ V, step S ∈ V) :
    OneYTruth.realize N (unionQueryAt k I φ params initial omega zero out) Empty.elim s ↔
      (s out).val = ZFSet.sUnion (family step (s initial).val) := by
  constructor
  · exact unionQueryAt_sound hV N hmem φ params initial omega zero out s hOmega hZero step hStep
  · intro hout
    obtain ⟨F, H, B, hF⟩ := exists_internal_familyCertificate hV N hmem hCol hSep hpair hUnion
      hempty (hOmega ▸ (s omega).property) φ (fun i => s (params i)) step hStep hclosed (s initial).property
    apply (realize_unionQueryAt hV N hmem φ params initial omega zero out s hOmega hZero step hStep).mpr
    exact ⟨F, H, B, hF, hout.trans (congrArg ZFSet.sUnion hF.family_eq.symm)⟩

end OneYTruth.InternalIteration
