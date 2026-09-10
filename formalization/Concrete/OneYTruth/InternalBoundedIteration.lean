import OneYTruth.InternalIterationFamily
import OneYTruth.ConstructibleBoundedIteration

/-! # Complete bounded grammar iterations inside an adequate transitive domain

Every finite step follows from the actual Separation schema. The complete
omega family follows from the displayed history formula and Collection.
The final union is identified with the pre-existing genuine L construction.
-/

namespace OneYTruth.InternalBoundedIteration

open Constructible Constructible.Delta0Formula Constructible.Model
open InternalClosure InternalIteration ConstructibleBoundedIteration

universe u v

theorem deltaSep_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hSep : HasSeparation N)
    {p : Nat} (φ : Delta0Formula (p+1)) (params : Fin p → ZFCarrier V)
    {B : ZFSet.{u}} (hB : B ∈ V) : deltaSep φ (fun i => (params i).val) B ∈ V := by
  obtain ⟨T, hT⟩ := hSep p (ofConstructibleDeltaZero k I φ) params ⟨B, hB⟩
  have he : T.val = deltaSep φ (fun i => (params i).val) B := by
    apply ZFSet.ext
    intro x
    have hsem (a : ZFCarrier V) :
        OneYTruth.realize N (ofConstructibleDeltaZero k I φ) Empty.elim (Fin.snoc params a) ↔
          Satisfies ZFMem φ (snoc (fun i => (params i).val) a.val) := by
      rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
      have ht : Constructible.Delta0Formula.val (Fin.snoc params a) =
          snoc (fun i => (params i).val) a.val := by
        rw [constructible_snoc_eq]
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Constructible.Delta0Formula.val]
      rw [ht]
    rw [deltaSep, ZFSet.mem_sep]
    constructor
    · intro hx
      let a : ZFCarrier V := ⟨x, hV.mem_trans hx T.property⟩
      exact (hT a).mp hx |>.imp_right ((hsem a).mp)
    · intro hx
      let a : ZFCarrier V := ⟨x, hV.mem_trans hx.1 hB⟩
      exact (hT a).mpr ⟨hx.1, (hsem a).mpr hx.2⟩
  exact he ▸ T.property

noncomputable def step {p : Nat} (φ : Delta0Formula (p+2)) (bound : Fin p)
    (params : Tuple ZFSet.{u} p) (S : ZFSet.{u}) : ZFSet.{u} :=
  deltaSep φ (snoc params S) (params bound)

theorem iterate_eq_L {p : Nat} (φ : Delta0Formula (p+2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) (initial : LCarrier.{u}) (n : Nat) :
    InternalIteration.iterate (step φ bound (fun i => (params i).val)) initial.val n =
      (uniformFiniteIterate (filterStep φ bound params) initial n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step φ bound _ (InternalIteration.iterate _ _ n) = _
      rw [ih]
      rfl

theorem union_eq_L {p : Nat} (φ : Delta0Formula (p+2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) (initial : LCarrier.{u}) :
    ZFSet.sUnion (InternalIteration.family (step φ bound (fun i => (params i).val)) initial.val) =
      (parametricUniformOmegaUnion (ConstructibleBoundedIteration.family φ bound params initial)).val := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨S, hS, hx⟩
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hS
    rw [iterate_eq_L] at hx
    have hxL := mem_L_of_mem hx (uniformFiniteIterate (filterStep φ bound params) initial n).property
    exact (mem_parametricUniformOmegaUnion_iff
      (ConstructibleBoundedIteration.family φ bound params initial) ⟨x, hxL⟩).mpr ⟨n, hx⟩
  · intro hx
    have hxL := mem_L_of_mem hx
      (parametricUniformOmegaUnion (ConstructibleBoundedIteration.family φ bound params initial)).property
    obtain ⟨n, hn⟩ := (mem_parametricUniformOmegaUnion_iff
      (ConstructibleBoundedIteration.family φ bound params initial) ⟨x, hxL⟩).mp hx
    refine ⟨InternalIteration.iterate (step φ bound (fun i => (params i).val)) initial.val n,
      ZFSet.mem_range_self (f := InternalIteration.iterate
        (step φ bound (fun i => (params i).val)) initial.val) n, ?_⟩
    rwa [iterate_eq_L]

theorem allStages_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {p : Nat} (φ : Delta0Formula (p+2)) (bound : Fin p)
    (params : Tuple LCarrier.{u} p) (hparams : ∀ i, (params i).val ∈ V)
    (initial : LCarrier.{u}) (hinitial : initial.val ∈ V) :
    (parametricUniformOmegaUnion (ConstructibleBoundedIteration.family φ bound params initial)).val ∈ V := by
  rw [← union_eq_L]
  apply hUnion
  apply InternalIteration.family_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    (filterGraph φ bound) (fun i => ⟨(params i).val, hparams i⟩)
    (step φ bound (fun i => (params i).val))
    (fun S T => satisfies_filterGraph φ bound _ S T) _ hinitial
  intro S hS
  have ht := deltaSep_mem hV N hmem hSep φ
    (Fin.snoc (fun i => (⟨(params i).val, hparams i⟩ : ZFCarrier V)) ⟨S, hS⟩) (hparams bound)
  have he : (fun i => ((Fin.snoc (fun i : Fin p => (⟨(params i).val, hparams i⟩ : ZFCarrier V))
      (⟨S, hS⟩ : ZFCarrier V) : Fin (p+1) → ZFCarrier V) i).val) =
      snoc (fun i => (params i).val) S := by
    rw [constructible_snoc_eq]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [he] at ht
  exact ht

end OneYTruth.InternalBoundedIteration

#print axioms OneYTruth.InternalBoundedIteration.allStages_mem
