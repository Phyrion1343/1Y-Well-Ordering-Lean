import OneYTruth.BoundedExistentialBlock

/-! Collection supplies one genuine internal set bounding every finite local
certificate over a given set of inputs. No externally selected family is
assumed to belong to the smaller domain. -/

namespace OneYTruth.UniformWitnessBound

open Constructible Constructible.Delta0Formula InternalClosure InternalProducts
open BoundedExistentialBlock

universe u v

theorem realize_certificate {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {n : Nat} (m : Nat) (φ : Delta0Formula (n+m))
    (p : Fin n → ZFCarrier V) (B : ZFCarrier V) :
    OneYTruth.realize N (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim (Fin.snoc p B) ↔
      ∃ w : Tuple ZFSet.{u} m, (∀ i, w i ∈ B.val) ∧
        Satisfies ZFMem φ (Fin.append (fun i => (p i).val) w) := by
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have he : val (Fin.snoc p B) = snoc (fun i => (p i).val) B.val := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [val]
  rw [he,satisfies_certificate]

theorem exists_bound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {n : Nat} (m : Nat) (φ : Delta0Formula (n+m)) (p : Fin n → ZFCarrier V)
    (w : Fin m → ZFCarrier V)
    (hφ : Satisfies ZFMem φ (Fin.append (fun i => (p i).val) (fun i => (w i).val))) :
    ∃ B : ZFCarrier V, OneYTruth.realize N
      (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim (Fin.snoc p B) := by
  let B : ZFCarrier V := ⟨ZFSet.range (fun i => (w i).val),
    finiteRange_mem hV hpair hUnion hempty (fun i => (w i).val) (fun i => (w i).property)⟩
  refine ⟨B,(realize_certificate hV N hmem m φ p B).mpr ?_⟩
  exact ⟨fun i => (w i).val,fun i => ZFSet.mem_range_self (f := fun j : Fin m => (w j).val) i,hφ⟩

theorem monotone {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {n : Nat} (m : Nat) (φ : Delta0Formula (n+m))
    (p : Fin n → ZFCarrier V) (A B : ZFCarrier V) (hAB : A.val ⊆ B.val)
    (h : OneYTruth.realize N (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim (Fin.snoc p A)) :
    OneYTruth.realize N (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim (Fin.snoc p B) := by
  obtain ⟨w,hw,hφ⟩ := (realize_certificate hV N hmem m φ p A).mp h
  exact (realize_certificate hV N hmem m φ p B).mpr ⟨w,fun i => hAB (hw i),hφ⟩

theorem exists_uniform_bound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {n : Nat} (m : Nat) (φ : Delta0Formula ((n+1)+m))
    (p : Fin n → ZFCarrier V) (source : ZFCarrier V)
    (h : ∀ x : ZFCarrier V, x.val ∈ source.val → ∃ w : Fin m → ZFCarrier V,
      Satisfies ZFMem φ (Fin.append (fun i => ((Fin.snoc p x : Fin (n+1) → ZFCarrier V) i).val) (fun i => (w i).val))) :
    ∃ B : ZFCarrier V, ∀ x : ZFCarrier V, x.val ∈ source.val →
      OneYTruth.realize N (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim
        (Fin.snoc (Fin.snoc p x) B) := by
  have ht (x : ZFCarrier V) (hx : x.val ∈ source.val) : ∃ B : ZFCarrier V,
      OneYTruth.realize N (ofConstructibleDeltaZero K J (certificate m φ)) Empty.elim
        (Fin.snoc (Fin.snoc p x) B) := by
    obtain ⟨w,hw⟩ := h x hx
    exact exists_bound hV N hmem hpair hUnion hempty m φ (Fin.snoc p x) w hw
  obtain ⟨C,hC⟩ := hCol n (ofConstructibleDeltaZero K J (certificate m φ)) p source ht
  let B : ZFCarrier V := ⟨ZFSet.sUnion C.val,hUnion _ C.property⟩
  refine ⟨B,?_⟩
  intro x hx
  obtain ⟨A,hAC,hA⟩ := hC x hx
  exact monotone hV N hmem m φ (Fin.snoc p x) A B
    (fun _ hz => ZFSet.mem_sUnion.mpr ⟨A.val,hAC,hz⟩) hA

end OneYTruth.UniformWitnessBound
