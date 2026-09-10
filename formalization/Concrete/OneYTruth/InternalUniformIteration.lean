import OneYTruth.InternalIterationFamily
import OneYTruth.ConstructibleBoundedIteration

/-! # Identification of the genuine L-valued iteration inside a smaller domain -/

namespace OneYTruth.InternalIteration

open Constructible Constructible.Delta0Formula Constructible.Model InternalClosure

universe u v

theorem iterate_eq_uniform (step : ZFSet.{u} → ZFSet.{u})
    (stepL : LCarrier.{u} → LCarrier.{u}) (hStepL : ∀ S, (stepL S).val = step S.val)
    (initial : LCarrier.{u}) (n : Nat) :
    iterate step initial.val n = (uniformFiniteIterate stepL initial n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step (iterate step initial.val n) = (stepL (uniformFiniteIterate stepL initial n)).val
      rw [ih, hStepL]

theorem union_eq_uniform {p : Nat} (φ : FOFormula (p+2))
    (params : Tuple LCarrier.{u} p) (step : ZFSet.{u} → ZFSet.{u})
    (stepL : LCarrier.{u} → LCarrier.{u}) (hStepL : ∀ S, (stepL S).val = step S.val)
    (initial : LCarrier.{u}) (hDefines : DefinesFiniteIterationStep φ params stepL) :
    ZFSet.sUnion (family step initial.val) =
      (parametricUniformOmegaUnion
        (uniformFiniteIterationOmegaFamilySpec φ params stepL initial hDefines)).val := by
  let spec := uniformFiniteIterationOmegaFamilySpec φ params stepL initial hDefines
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨S, hS, hx⟩
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hS
    rw [iterate_eq_uniform step stepL hStepL initial n] at hx
    have hxL := mem_L_of_mem hx (uniformFiniteIterate stepL initial n).property
    exact (mem_parametricUniformOmegaUnion_iff spec ⟨x, hxL⟩).mpr ⟨n, hx⟩
  · intro hx
    have hxL := mem_L_of_mem hx (parametricUniformOmegaUnion spec).property
    obtain ⟨n, hn⟩ := (mem_parametricUniformOmegaUnion_iff spec ⟨x, hxL⟩).mp hx
    refine ⟨iterate step initial.val n, ZFSet.mem_range_self (f := iterate step initial.val) n, ?_⟩
    rwa [iterate_eq_uniform step stepL hStepL initial n]

theorem uniformUnion_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {p : Nat} (φ : Delta0Formula (p+2))
    (params : Tuple LCarrier.{u} p) (hparams : ∀ i, (params i).val ∈ V)
    (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun i => (params i).val) S) T) ↔ T = step S)
    (stepL : LCarrier.{u} → LCarrier.{u}) (hStepL : ∀ S, (stepL S).val = step S.val)
    (hDefines : DefinesFiniteIterationStep φ.toFO params stepL)
    (hclosed : ∀ S ∈ V, step S ∈ V) (initial : LCarrier.{u}) (hinitial : initial.val ∈ V) :
    (parametricUniformOmegaUnion
      (uniformFiniteIterationOmegaFamilySpec φ.toFO params stepL initial hDefines)).val ∈ V := by
  rw [← union_eq_uniform φ.toFO params step stepL hStepL initial hDefines]
  exact hUnion _ (family_mem hV N hmem hCol hSep hpair hUnion hempty hOmega φ
    (fun i => ⟨(params i).val, hparams i⟩) step hStep hclosed hinitial)

end OneYTruth.InternalIteration

#print axioms OneYTruth.InternalIteration.uniformUnion_mem
