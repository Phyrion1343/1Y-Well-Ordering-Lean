import OneYTruth.LocalTruthQuery

/-!
# Exact separation and replacement instances in an expanded set structure

Only the displayed individual schema instances are assumed. In particular,
no Power Set, global model-of-ZF assumption, or truth-set closure is used.
An internal witness is first obtained from the schema instance; only then
is it identified extensionally with the external range under discussion.
-/

namespace OneYTruth.InternalClosure

open FirstOrder FirstOrder.Language Constructible

universe u v w

/-- The usual expanded-language Separation instance for one actual formula. -/
def SeparationInstance {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 1)) : Prop :=
  ∀ (params : Fin n → ZFCarrier V) (a : ZFCarrier V),
    ∃ b : ZFCarrier V, ∀ x : ZFCarrier V,
      x.val ∈ b.val ↔ x.val ∈ a.val ∧ OneYTruth.realize N φ Empty.elim (Fin.snoc params x)

/-- The usual functional Replacement instance for one actual expanded formula. -/
def ReplacementInstance {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) : Prop :=
  ∀ (params : Fin n → ZFCarrier V) (a : ZFCarrier V),
    (∀ x : ZFCarrier V, x.val ∈ a.val →
      ∃! y : ZFCarrier V, OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y)) →
    ∃ b : ZFCarrier V, ∀ y : ZFCarrier V,
      y.val ∈ b.val ↔ ∃ x : ZFCarrier V, x.val ∈ a.val ∧
        OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y)

/-- All expanded Separation instances, with their actual semantics displayed above. -/
def HasSeparation {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) : Prop :=
  ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty (n + 1)), SeparationInstance N φ

/-- All expanded functional Replacement instances. This includes no Power Set axiom. -/
def HasReplacement {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) : Prop :=
  ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty (n + 2)), ReplacementInstance N φ

/-- Separation internalizes a filtered range when the source range is already internal
and the filtering predicate is represented by the given formula. -/
theorem filtered_range_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 1)) (hSep : SeparationInstance N φ)
    (params : Fin n → ZFCarrier V) {W : Type w} [Small.{u} W]
    (code : W → ZFSet.{u}) (P : W → Prop) (hsource : ZFSet.range code ∈ V)
    (hφ : ∀ z (hz : code z ∈ V),
      OneYTruth.realize N φ Empty.elim (Fin.snoc params ⟨code z, hz⟩) ↔ P z) :
    ZFSet.range (fun z : {z : W // P z} => code z.val) ∈ V := by
  obtain ⟨b, hb⟩ := hSep params ⟨ZFSet.range code, hsource⟩
  have heq : b.val = ZFSet.range (fun z : {z : W // P z} => code z.val) := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hxb
      have hxV := hV.mem_trans hxb b.property
      obtain ⟨hsourceX, htest⟩ := (hb ⟨x, hxV⟩).mp hxb
      obtain ⟨z, hz⟩ := ZFSet.mem_range.mp hsourceX
      change code z = x at hz
      subst x
      exact ZFSet.mem_range.mpr ⟨⟨z, (hφ z hxV).mp htest⟩, rfl⟩
    · intro hx
      obtain ⟨⟨z, hzP⟩, hz⟩ := ZFSet.mem_range.mp hx
      subst x
      have hzV := hV.mem_trans (ZFSet.mem_range_self (f := code) z) hsource
      exact (hb ⟨code z, hzV⟩).mpr
        ⟨ZFSet.mem_range_self z, (hφ z hzV).mpr hzP⟩
  exact heq ▸ b.property

/-- Functional Replacement internalizes the output range. The input codes are injective,
the full source range is internal, and the actual formula defines the code-to-output map. -/
theorem image_range_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) (hRep : ReplacementInstance N φ)
    (params : Fin n → ZFCarrier V) {W : Type w} [Small.{u} W]
    (code output : W → ZFSet.{u}) (hi : Function.Injective code)
    (hsource : ZFSet.range code ∈ V) (hout : ∀ z, output z ∈ V)
    (hφ : ∀ (x y : ZFCarrier V), x.val ∈ ZFSet.range code →
      (OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y) ↔
        ∃ z : W, code z = x.val ∧ output z = y.val)) :
    ZFSet.range output ∈ V := by
  have hfun : ∀ x : ZFCarrier V, x.val ∈ ZFSet.range code →
      ∃! y : ZFCarrier V, OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y) := by
    intro x hx
    obtain ⟨z, hz⟩ := ZFSet.mem_range.mp hx
    refine ⟨⟨output z, hout z⟩, (hφ x _ hx).mpr ⟨z, hz, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨w, hw, hwy⟩ := (hφ x y hx).mp hy
    have hwz : w = z := hi (hw.trans hz.symm)
    apply Subtype.ext
    simpa only [hwz] using hwy.symm
  obtain ⟨b, hb⟩ := hRep params ⟨ZFSet.range code, hsource⟩ hfun
  have heq : b.val = ZFSet.range output := by
    apply ZFSet.ext
    intro y
    constructor
    · intro hyb
      have hyV := hV.mem_trans hyb b.property
      obtain ⟨x, hx, htest⟩ := (hb ⟨y, hyV⟩).mp hyb
      obtain ⟨z, _, hz⟩ := (hφ x ⟨y, hyV⟩ hx).mp htest
      exact ZFSet.mem_range.mpr ⟨z, hz⟩
    · intro hy
      obtain ⟨z, hz⟩ := ZFSet.mem_range.mp hy
      subst y
      have hzSource := ZFSet.mem_range_self (f := code) z
      let x : ZFCarrier V := ⟨code z, hV.mem_trans hzSource hsource⟩
      exact (hb ⟨output z, hout z⟩).mpr
        ⟨x, hzSource, (hφ x _ hzSource).mpr ⟨z, rfl, rfl⟩⟩
  exact heq ▸ b.property

end OneYTruth.InternalClosure
