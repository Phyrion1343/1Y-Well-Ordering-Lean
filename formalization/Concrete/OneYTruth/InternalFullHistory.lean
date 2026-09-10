import OneYTruth.IterationFamilyCertificate

/-! # The actual complete indexed iteration history is internal

The output of the finite-history query is packed with its natural index.
The actual Replacement consequence of Collection and Separation collects
these ordered pairs, producing the precise infinite history used by the
bounded completeness certificate.
-/

namespace OneYTruth.InternalIteration

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF InternalClosure

universe u v

def packedQueryAt (k : Nat) (I : Type v) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero index output : Fin n) :
    (language k I).BoundedFormula Empty n :=
  (ofConstructibleDeltaZero k I (kuratowskiPairEqAt output.castSucc index.castSucc (Fin.last n)) ⊓
    queryAt k I φ (fun i => (params i).castSucc) initial.castSucc omega.castSucc zero.castSucc
      index.castSucc (Fin.last n)).ex

theorem realize_packedQueryAt {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (initial omega zero index output : Fin n) (s : Fin n → ZFCarrier V)
    (hOmega : (s omega).val = Ordinal.omega0.toZFSet) (hZero : (s zero).val = ∅)
    (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun i => (s (params i)).val) S) T) ↔ T = step S) :
    OneYTruth.realize N (packedQueryAt k I φ params initial omega zero index output) Empty.elim s ↔
      ∃ S : ZFCarrier V, (s output).val = ZFSet.pair (s index).val S.val ∧
        ∃ H B : ZFCarrier V, IsHistory step (s initial).val H.val B.val ∧
          ZFSet.pair (s index).val S.val ∈ H.val := by
  letI := N.structure
  change (packedQueryAt k I φ params initial omega zero index output).Realize Empty.elim s ↔ _
  rw [packedQueryAt, BoundedFormula.realize_ex]
  apply exists_congr
  intro S
  rw [BoundedFormula.realize_inf]
  apply and_congr
  · change OneYTruth.realize N (ofConstructibleDeltaZero k I _) Empty.elim (Fin.snoc s S) ↔ _
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem, satisfies_kuratowskiPairEqAt]
    simp only [Constructible.Delta0Formula.val, Fin.snoc_castSucc, Fin.snoc_last]
  · have hh := realize_queryAt hV N hmem φ (fun i => (params i).castSucc)
      initial.castSucc omega.castSucc zero.castSucc index.castSucc (Fin.last n)
      (Fin.snoc s S) (by simpa) (by simpa) step (by simpa only [Fin.snoc_castSucc] using hStep)
    simpa only [OneYTruth.realize, Fin.snoc_castSucc, Fin.snoc_last] using hh

def packedQueryFormula (k : Nat) (I : Type v) {p : Nat} (φ : Delta0Formula (p+2)) :
    (language k I).BoundedFormula Empty (p+5) :=
  packedQueryAt k I φ (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last p).castSucc.castSucc.castSucc.castSucc
    (Fin.last (p+1)).castSucc.castSucc.castSucc (Fin.last (p+2)).castSucc.castSucc
    (Fin.last (p+3)).castSucc (Fin.last (p+4))

theorem fullHistory_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {p : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → ZFCarrier V) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun i => (params i).val) S) T) ↔ T = step S)
    (hclosed : ∀ S ∈ V, step S ∈ V) {initial : ZFSet.{u}} (hinitial : initial ∈ V) :
    fullHistory step initial ∈ V := by
  have hNat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩) hOmega
  have hIter (n : Nat) : iterate step initial n ∈ V := by
    induction n with
    | zero => exact hinitial
    | succ n ih => exact hclosed _ ih
  have hw (n : Nat) := finite_witnesses_mem hV hpair hUnion hempty hNat step initial hIter n
  let inputs : Fin (p+3) → ZFCarrier V :=
    Fin.snoc (Fin.snoc (Fin.snoc params ⟨initial, hinitial⟩) ⟨Ordinal.omega0.toZFSet, hOmega⟩) ⟨∅, hempty⟩
  have hsource : ZFSet.range (natCode : Nat → ZFSet.{u}) ∈ V := by
    rw [BoundedEvaluation.range_natCode_eq_omega]
    exact hOmega
  apply image_range_mem hV N (packedQueryFormula k I φ)
    (hasReplacement_of_collection_separation N hmem hCol hSep (p+3) (packedQueryFormula k I φ))
    inputs natCode (fun n => ZFSet.pair (natCode n) (iterate step initial n)) natCode_injective hsource
    (fun n => hpair _ (hNat n) _ (hIter n))
  intro x y hx
  have hq : OneYTruth.realize N (packedQueryFormula k I φ) Empty.elim (Fin.snoc (Fin.snoc inputs x) y) ↔
      ∃ S : ZFCarrier V, y.val = ZFSet.pair x.val S.val ∧
        ∃ H B : ZFCarrier V, IsHistory step initial H.val B.val ∧ ZFSet.pair x.val S.val ∈ H.val := by
    have hh := realize_packedQueryAt hV N hmem φ
      (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last p).castSucc.castSucc.castSucc.castSucc
      (Fin.last (p+1)).castSucc.castSucc.castSucc (Fin.last (p+2)).castSucc.castSucc
      (Fin.last (p+3)).castSucc (Fin.last (p+4))
      (Fin.snoc (Fin.snoc inputs x) y) (by simp [inputs]) (by simp [inputs]) step
      (by simpa only [inputs, Fin.snoc_castSucc] using hStep)
    simpa only [packedQueryFormula, inputs, Fin.snoc_last, Fin.snoc_castSucc] using hh
  rw [hq]
  constructor
  · rintro ⟨S, hy, H, B, hh, hxy⟩
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp hx
    have hny : ZFSet.pair (natCode n) S.val ∈ H.val := hn.symm ▸ hxy
    refine ⟨n, hn, ?_⟩
    rw [← hh.value_eq_iterate n hny, hn]
    exact hy.symm
  · rintro ⟨n, hn, hny⟩
    refine ⟨⟨iterate step initial n, hIter n⟩, ?_,
      ⟨finiteHistory step initial n, (hw n).1⟩,
      ⟨historyContainer step initial n, (hw n).2⟩, finiteHistory_isHistory step initial n, ?_⟩
    · rw [← hn, ← hny]
    · rw [← hn]
      exact last_mem_finiteHistory step initial n

theorem exists_internal_familyCertificate {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {p : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → ZFCarrier V) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun i => (params i).val) S) T) ↔ T = step S)
    (hclosed : ∀ S ∈ V, step S ∈ V) {initial : ZFSet.{u}} (hinitial : initial ∈ V) :
    ∃ F H B : ZFCarrier V, IsFamilyCertificate step initial F.val H.val B.val := by
  have hF := family_mem hV N hmem hCol hSep hpair hUnion hempty hOmega φ params step hStep hclosed hinitial
  have hH := fullHistory_mem hV N hmem hCol hSep hpair hUnion hempty hOmega φ params step hStep hclosed hinitial
  exact ⟨⟨family step initial, hF⟩, ⟨fullHistory step initial, hH⟩,
    ⟨Ordinal.omega0.toZFSet ∪ family step initial,
      InternalProducts.binaryUnion_mem hV hpair hUnion hOmega hF⟩,
    fullHistory_isFamilyCertificate step initial⟩

end OneYTruth.InternalIteration

#print axioms OneYTruth.InternalIteration.fullHistory_mem
#print axioms OneYTruth.InternalIteration.exists_internal_familyCertificate
