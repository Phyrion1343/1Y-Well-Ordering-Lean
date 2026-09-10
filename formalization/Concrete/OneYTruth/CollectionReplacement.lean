import OneYTruth.InternalClosure
import OneYTruth.ScopedReindex

/-!
# Functional Replacement from expanded Collection and Separation

The image-filtering formula is constructed explicitly in the mixed
language. For a fixed functional formula, only its Collection instance and
the Separation instance for this constructed formula are used. Power Set
and a full model-of-ZF hypothesis do not occur.
-/

namespace OneYTruth.InternalClosure

open FirstOrder FirstOrder.Language Constructible

universe u v

def CollectionInstance {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) : Prop :=
  ∀ (params : Fin n → ZFCarrier V) (a : ZFCarrier V),
    (∀ x : ZFCarrier V, x.val ∈ a.val →
      ∃ y : ZFCarrier V, OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y)) →
    ∃ b : ZFCarrier V, ∀ x : ZFCarrier V, x.val ∈ a.val →
      ∃ y : ZFCarrier V, y.val ∈ b.val ∧
        OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y)

def HasCollection {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) : Prop :=
  ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty (n + 2)), CollectionInstance N φ

/-- `(params,x,y)` is read from the larger scope `(params,a,y,x)`. -/
def rangeReindex (n : Nat) : Fin (n + 2) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 1)).castSucc
    (fun j => Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc) j)

theorem snoc_comp_rangeReindex {A : Type*} {n : Nat} (params : Fin n → A) (a y x : A) :
    Fin.snoc (Fin.snoc (Fin.snoc params a) y) x ∘ rangeReindex n =
      Fin.snoc (Fin.snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [rangeReindex]
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp [rangeReindex]
    · simp [rangeReindex]

/-- `exists x in a, φ(params,x,y)`, with `(params,a,y)` as the current scope. -/
def rangePredicate {k : Nat} {I : Type v} {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2)) :
    (language k I).BoundedFormula Empty (n + 2) :=
  ((.rel .mem ![.var (.inr (Fin.last (n + 2))),
      .var (.inr (Fin.last n).castSucc.castSucc)]) ⊓ reindexScoped (rangeReindex n) φ).ex

theorem realize_rangePredicate {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (N : Interpretation k I (ZFCarrier V)) (hmem : N.mem = Constructible.zfCarrierMem V)
    {n : Nat} (φ : (language k I).BoundedFormula Empty (n + 2))
    (params : Fin n → ZFCarrier V) (a y : ZFCarrier V) :
    OneYTruth.realize N (rangePredicate φ) Empty.elim (Fin.snoc (Fin.snoc params a) y) ↔
      ∃ x : ZFCarrier V, x.val ∈ a.val ∧
        OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y) := by
  letI := N.structure
  change (BoundedFormula.ex _).Realize Empty.elim (Fin.snoc (Fin.snoc params a) y) ↔ _
  rw [BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_inf]
  change (∃ x : ZFCarrier V, N.mem
    ((Fin.snoc (Fin.snoc (Fin.snoc params a) y) x : Fin (n + 3) → ZFCarrier V)
      (Fin.last (n + 2)))
    ((Fin.snoc (Fin.snoc (Fin.snoc params a) y) x : Fin (n + 3) → ZFCarrier V)
      (Fin.last n).castSucc.castSucc) ∧
    OneYTruth.realize N (reindexScoped (rangeReindex n) φ) Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc params a) y) x)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc, realize_reindexScoped,
    snoc_comp_rangeReindex, hmem, Constructible.zfCarrierMem]

theorem replacementInstance_of_collection_separation {k : Nat} {I : Type v}
    {V : ZFSet.{u}} (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) {n : Nat}
    (φ : (language k I).BoundedFormula Empty (n + 2))
    (hCol : CollectionInstance N φ) (hSep : SeparationInstance N (rangePredicate φ)) :
    ReplacementInstance N φ := by
  intro params a hfun
  obtain ⟨b, hb⟩ := hCol params a (fun x hx => (hfun x hx).exists)
  obtain ⟨c, hc⟩ := hSep (Fin.snoc params a) b
  refine ⟨c, ?_⟩
  intro y
  rw [hc, realize_rangePredicate N hmem]
  constructor
  · exact And.right
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hzb, hxz⟩ := hb x hx
    have hyz : y = z := (hfun x hx).unique hxy hxz
    exact ⟨by simpa only [hyz] using hzb, x, hx, hxy⟩

theorem hasReplacement_of_collection_separation {k : Nat} {I : Type v}
    {V : ZFSet.{u}} (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N) : HasReplacement N := by
  intro n φ
  exact replacementInstance_of_collection_separation N hmem φ (hCol n φ)
    (hSep (n + 1) (rangePredicate φ))

end OneYTruth.InternalClosure
