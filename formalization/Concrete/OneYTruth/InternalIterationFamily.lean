import OneYTruth.InternalIterationHistory

/-! # Actual internal collection of a displayed iteration's complete omega family

The querying formula has two existential set witnesses over a bounded
matrix. Collection and Separation internalize its functional image of
omega, after canonical finite witnesses have been constructed internally.
-/

namespace OneYTruth.InternalIteration

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF InternalClosure

universe u v

def queryMatrixAt {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (initial omega zero index output : Fin n) : Delta0Formula (n+2) :=
  .conj (historyAt φ (fun i => (params i).castSucc.castSucc)
    initial.castSucc.castSucc omega.castSucc.castSucc zero.castSucc.castSucc
    (Fin.last n).castSucc (Fin.last (n+1)))
    (BoundedEvaluation.pairMemAt (Fin.last n).castSucc index.castSucc.castSucc output.castSucc.castSucc)

theorem satisfies_queryMatrixAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero index output : Fin n)
    (s : Tuple ZFSet.{u} n) (hOmega : s omega = Ordinal.omega0.toZFSet) (hZero : s zero = ∅)
    (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun a => s (params a)) S) T) ↔ T = step S)
    (H B : ZFSet.{u}) :
    Satisfies ZFMem (queryMatrixAt φ params initial omega zero index output) (snoc (snoc s H) B) ↔
      IsHistory step (s initial) H B ∧ ZFSet.pair (s index) (s output) ∈ H := by
  change (Satisfies ZFMem (historyAt φ _ _ _ _ _ _) _ ∧
    Satisfies ZFMem (BoundedEvaluation.pairMemAt _ _ _) _) ↔ _
  rw [satisfies_historyAt _ _ _ _ _ _ _ _ (by simpa) (by simpa) step (by simpa),
    BoundedEvaluation.satisfies_pairMemAt]
  simp only [snoc_last, snoc_castSucc]

def queryAt (k : Nat) (I : Type v) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero index output : Fin n) :
    (language k I).BoundedFormula Empty n :=
  (ofConstructibleDeltaZero k I (queryMatrixAt φ params initial omega zero index output)).ex.ex

theorem queryAt_isSigmaOne (k : Nat) (I : Type v) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero index output : Fin n) :
    IsSigmaOne (queryAt k I φ params initial omega zero index output) :=
  .ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero k I _)))

theorem realize_queryAt {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero index output : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ
      (snoc (snoc (fun a => (s (params a)).val) S) T) ↔ T = step S) :
    OneYTruth.realize N (queryAt k I φ params initial omega zero index output) Empty.elim s ↔
      ∃ H B : ZFCarrier V, IsHistory step (s initial).val H.val B.val ∧
        ZFSet.pair (s index).val (s output).val ∈ H.val := by
  have hc (H B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero k I
        (queryMatrixAt φ params initial omega zero index output)) Empty.elim
        (Fin.snoc (Fin.snoc s H) B) ↔
      IsHistory step (s initial).val H.val B.val ∧ ZFSet.pair (s index).val (s output).val ∈ H.val := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    have he : Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc s H) B) =
        snoc (snoc (fun i => (s i).val) H.val) B.val := by
      rw [constructible_snoc_eq, constructible_snoc_eq]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Constructible.Delta0Formula.val]
      · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [Constructible.Delta0Formula.val]
    rw [he]
    exact satisfies_queryMatrixAt φ params initial omega zero index output _ hOmega hZero step hStep _ _
  letI := N.structure
  change (ofConstructibleDeltaZero k I _).ex.ex.Realize Empty.elim s ↔ _
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro H
  rw [BoundedFormula.realize_ex]
  exact exists_congr (hc H)

def queryFormula (k : Nat) (I : Type v) {p : Nat} (φ : Delta0Formula (p+2)) :
    (language k I).BoundedFormula Empty (p+5) :=
  queryAt k I φ (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last p).castSucc.castSucc.castSucc.castSucc
    (Fin.last (p+1)).castSucc.castSucc.castSucc (Fin.last (p+2)).castSucc.castSucc
    (Fin.last (p+3)).castSucc (Fin.last (p+4))

noncomputable def family (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (iterate step initial)

theorem family_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {p : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → ZFCarrier V) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun i => (params i).val) S) T) ↔ T = step S)
    (hclosed : ∀ S ∈ V, step S ∈ V) {initial : ZFSet.{u}} (hinitial : initial ∈ V) :
    family step initial ∈ V := by
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
  apply image_range_mem hV N (queryFormula k I φ)
    (hasReplacement_of_collection_separation N hmem hCol hSep (p+3) (queryFormula k I φ))
    inputs natCode (iterate step initial) natCode_injective hsource hIter
  intro x y hx
  have hq : OneYTruth.realize N (queryFormula k I φ) Empty.elim (Fin.snoc (Fin.snoc inputs x) y) ↔
      ∃ H B : ZFCarrier V, IsHistory step initial H.val B.val ∧ ZFSet.pair x.val y.val ∈ H.val := by
    have hh := realize_queryAt hV N hmem φ
      (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last p).castSucc.castSucc.castSucc.castSucc
      (Fin.last (p+1)).castSucc.castSucc.castSucc (Fin.last (p+2)).castSucc.castSucc
      (Fin.last (p+3)).castSucc (Fin.last (p+4))
      (Fin.snoc (Fin.snoc inputs x) y) (by simp [inputs]) (by simp [inputs]) step
      (by simpa only [inputs, Fin.snoc_castSucc] using hStep)
    simpa only [queryFormula, inputs, Fin.snoc_last, Fin.snoc_castSucc] using hh
  rw [hq]
  constructor
  · rintro ⟨H, B, hh, hxy⟩
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp hx
    have hny : ZFSet.pair (natCode n) y.val ∈ H.val := hn.symm ▸ hxy
    exact ⟨n, hn, (hh.value_eq_iterate n hny).symm⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨⟨finiteHistory step initial n, (hw n).1⟩,
      ⟨historyContainer step initial n, (hw n).2⟩, finiteHistory_isHistory step initial n, ?_⟩
    rw [← hn, ← hny]
    exact last_mem_finiteHistory step initial n

end OneYTruth.InternalIteration

#print axioms OneYTruth.InternalIteration.family_mem
#print axioms OneYTruth.InternalIteration.queryAt_isSigmaOne
