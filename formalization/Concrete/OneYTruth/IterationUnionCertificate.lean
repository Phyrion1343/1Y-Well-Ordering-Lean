import OneYTruth.IterationFamilyCertificate

/-! A complete omega iteration has a finite existential certificate with a
literal bounded matrix. A satisfying certificate cannot omit any stage.
Its internal existence remains explicit until the actual witnesses are supplied. -/

namespace OneYTruth.InternalIteration

open Constructible Constructible.Delta0Formula FirstOrder FirstOrder.Language

universe u v

def unionAt {n : Nat} (out F : Fin n) : Delta0Formula n :=
  .conj (.boundedAll out (.boundedEx F.castSucc
    (.mem (Fin.last n).castSucc (Fin.last (n+1)))))
    (.boundedAll F (.boundedAll (Fin.last n)
      (.mem (Fin.last (n+1)) out.castSucc.castSucc)))

theorem satisfies_unionAt {n : Nat} (out F : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (unionAt out F) s ↔ s out = ZFSet.sUnion (s F) := by
  simp only [unionAt, Satisfies, satisfies_boundedAll, snoc_last, snoc_castSucc]
  change ((∀ x ∈ s out, ∃ S ∈ s F, x ∈ S) ∧
    (∀ S ∈ s F, ∀ x ∈ S, x ∈ s out)) ↔ _
  constructor
  · rintro ⟨hleft, hright⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sUnion]
    exact ⟨hleft x, fun ⟨S, hS, hx⟩ => hright S hS x hx⟩
  · intro h
    constructor
    · intro x hx
      rw [h] at hx
      exact ZFSet.mem_sUnion.mp hx
    · intro S hS x hx
      rw [h]
      exact ZFSet.mem_sUnion.mpr ⟨S, hS, hx⟩

def unionMatrixAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n) : Delta0Formula (n+3) :=
  .conj (familyCertificateAt φ (fun i => (params i).castSucc.castSucc.castSucc)
    initial.castSucc.castSucc.castSucc omega.castSucc.castSucc.castSucc
    zero.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc
    (Fin.last (n+1)).castSucc (Fin.last (n+2)))
    (unionAt out.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc)

theorem satisfies_unionMatrixAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Tuple ZFSet.{u} n) (hOmega : s omega = Ordinal.omega0.toZFSet)
    (hZero : s zero = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun a => s (params a)) S) T) ↔ T = step S)
    (F H B : ZFSet.{u}) :
    Satisfies ZFMem (unionMatrixAt φ params initial omega zero out)
      (snoc (snoc (snoc s F) H) B) ↔
      IsFamilyCertificate step (s initial) F H B ∧ s out = ZFSet.sUnion F := by
  change (Satisfies ZFMem (familyCertificateAt φ _ _ _ _ _ _ _) _ ∧
    Satisfies ZFMem (unionAt _ _) _) ↔ _
  rw [satisfies_familyCertificateAt _ _ _ _ _ _ _ _ _ (by simpa) (by simpa) step
    (by simpa using hStep), satisfies_unionAt]
  simp only [snoc_last, snoc_castSucc]

def unionQueryAt (k : Nat) (I : Type v) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n) :
    (language k I).BoundedFormula Empty n :=
  (ofConstructibleDeltaZero k I (unionMatrixAt φ params initial omega zero out)).ex.ex.ex

theorem unionQueryAt_isSigmaOne (k : Nat) (I : Type v) {p n : Nat}
    (φ : Delta0Formula (p+2)) (params : Fin p → Fin n) (initial omega zero out : Fin n) :
    IsSigmaOne (unionQueryAt k I φ params initial omega zero out) :=
  .ex (.ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero k I _))))

theorem realize_unionQueryAt {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ
      (snoc (snoc (fun a => (s (params a)).val) S) T) ↔ T = step S) :
    OneYTruth.realize N (unionQueryAt k I φ params initial omega zero out) Empty.elim s ↔
      ∃ F H B : ZFCarrier V, IsFamilyCertificate step (s initial).val F.val H.val B.val ∧
        (s out).val = ZFSet.sUnion F.val := by
  have hc (F H B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero k I
        (unionMatrixAt φ params initial omega zero out)) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc s F) H) B) ↔
      IsFamilyCertificate step (s initial).val F.val H.val B.val ∧
        (s out).val = ZFSet.sUnion F.val := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    have he : Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc (Fin.snoc s F) H) B) =
        snoc (snoc (snoc (fun i => (s i).val) F.val) H.val) B.val := by
      rw [constructible_snoc_eq, constructible_snoc_eq, constructible_snoc_eq]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Constructible.Delta0Formula.val]
      · refine Fin.lastCases ?_ (fun l => ?_) j
        · simp [Constructible.Delta0Formula.val]
        · refine Fin.lastCases ?_ (fun t => ?_) l <;> simp [Constructible.Delta0Formula.val]
    rw [he]
    exact satisfies_unionMatrixAt φ params initial omega zero out _ hOmega hZero step hStep _ _ _
  letI := N.structure
  change (ofConstructibleDeltaZero k I _).ex.ex.ex.Realize Empty.elim s ↔ _
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro F
  rw [BoundedFormula.realize_ex]
  apply exists_congr
  intro H
  rw [BoundedFormula.realize_ex]
  exact exists_congr (hc F H)

theorem unionQueryAt_sound {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ
      (snoc (snoc (fun a => (s (params a)).val) S) T) ↔ T = step S)
    (h : OneYTruth.realize N (unionQueryAt k I φ params initial omega zero out) Empty.elim s) :
    (s out).val = ZFSet.sUnion (family step (s initial).val) := by
  obtain ⟨F, H, B, hF, hout⟩ := (realize_unionQueryAt hV N hmem φ params initial omega zero out
    s hOmega hZero step hStep).mp h
  exact hout.trans (congrArg ZFSet.sUnion hF.family_eq)

theorem unionQueryAt_complete_of_witnesses {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero out : Fin n)
    (s : Fin n → ZFCarrier V) (hOmega : (s omega).val = Ordinal.omega0.toZFSet)
    (hZero : (s zero).val = ∅) (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ
      (snoc (snoc (fun a => (s (params a)).val) S) T) ↔ T = step S)
    (hF : family step (s initial).val ∈ V)
    (hH : fullHistory step (s initial).val ∈ V)
    (hB : Ordinal.omega0.toZFSet ∪ family step (s initial).val ∈ V)
    (hout : (s out).val = ZFSet.sUnion (family step (s initial).val)) :
    OneYTruth.realize N (unionQueryAt k I φ params initial omega zero out) Empty.elim s := by
  apply (realize_unionQueryAt hV N hmem φ params initial omega zero out s hOmega hZero step hStep).mpr
  exact ⟨⟨_, hF⟩, ⟨_, hH⟩, ⟨_, hB⟩, fullHistory_isFamilyCertificate step _, hout⟩

end OneYTruth.InternalIteration
