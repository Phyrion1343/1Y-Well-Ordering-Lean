import OneYTruth.RootSemantics
import OneYTruth.PureFOTranslation

/-! # Pure first-order schemas supplied by actual mixed adequacy

The translation below preserves semantics on the same carrier. It makes
no absoluteness claim for arbitrary unbounded first-order formulas.
-/

namespace OneYTruth

open Constructible Constructible.Model FirstOrder FirstOrder.Language

universe u v

namespace InternalClosure

def HasFOSeparation (V : ZFSet.{u}) : Prop :=
  ∀ (n : Nat) (φ : FOFormula (n + 1)) (params : Tuple (ZFCarrier V) n) (a : ZFCarrier V),
    ∃ b : ZFCarrier V, ∀ x : ZFCarrier V, x.val ∈ b.val ↔
      x.val ∈ a.val ∧ FOFormula.Satisfies (zfCarrierMem V) φ (snoc params x)

def HasFOReplacement (V : ZFSet.{u}) : Prop :=
  ∀ (n : Nat) (φ : FOFormula (n + 2)) (params : Tuple (ZFCarrier V) n) (a : ZFCarrier V),
    (∀ x : ZFCarrier V, x.val ∈ a.val → ∃! y : ZFCarrier V,
      FOFormula.Satisfies (zfCarrierMem V) φ (snoc (snoc params x) y)) →
    ∃ b : ZFCarrier V, ∀ y : ZFCarrier V, y.val ∈ b.val ↔
      ∃ x : ZFCarrier V, x.val ∈ a.val ∧
        FOFormula.Satisfies (zfCarrierMem V) φ (snoc (snoc params x) y)

theorem hasFOSeparation_of_mixed {V : ZFSet.{u}} {k : Nat} {I : Type v}
    (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (h : HasSeparation N) : HasFOSeparation V := by
  intro n φ params a
  obtain ⟨b, hb⟩ := h n (ofConstructibleFO k I φ) params a
  refine ⟨b, ?_⟩
  intro x
  simpa only [realize_ofConstructibleFO, hmem, constructible_snoc_eq] using hb x

theorem hasFOReplacement_of_mixed {V : ZFSet.{u}} {k : Nat} {I : Type v}
    (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (h : HasReplacement N) : HasFOReplacement V := by
  intro n φ params a hfun
  have hf : ∀ x : ZFCarrier V, x.val ∈ a.val → ∃! y : ZFCarrier V,
      OneYTruth.realize N (ofConstructibleFO k I φ) Empty.elim
        (Fin.snoc (Fin.snoc params x) y) := by
    simpa only [realize_ofConstructibleFO, hmem, constructible_snoc_eq] using hfun
  obtain ⟨b, hb⟩ := h n (ofConstructibleFO k I φ) params a hf
  exact ⟨b, fun y => by
    simpa only [realize_ofConstructibleFO, hmem, constructible_snoc_eq] using hb y⟩

end InternalClosure

namespace RootSemantics

/-- Only the actual zero-block, zero-index schemas are used to obtain
ordinary first-order Separation and Replacement. Power Set is not assumed. -/
theorem Adequate.pureFOSchemas {a : Ordinal.{u}} (h : Adequate a) :
    InternalClosure.HasFOSeparation (LStageZF a) ∧
      InternalClosure.HasFOReplacement (LStageZF a) := by
  let N := ExternalTower.interpretation (κ := a) (LStageZF a) (0, ⟨0, zero_le⟩)
  have hs := h.2.2 0 0 zero_le
  exact ⟨InternalClosure.hasFOSeparation_of_mixed N rfl hs.1,
    InternalClosure.hasFOReplacement_of_mixed N rfl
      (InternalClosure.hasReplacement_of_collection_separation N rfl hs.2 hs.1)⟩

end RootSemantics
end OneYTruth

#print axioms OneYTruth.RootSemantics.Adequate.pureFOSchemas
