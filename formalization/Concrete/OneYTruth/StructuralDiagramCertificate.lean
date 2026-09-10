import OneYTruth.StructuralSetEquations

/-! A single literal bounded matrix uniquely checks all five structural
diagram sets, given the actual full syntax and assignment sources. -/

namespace OneYTruth.StructuralDiagramCertificate

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language FormulaCode SyntaxDiagram InternalNodes InternalProducts
open BoundedFilterGraph AtomicCodeFormula QuantifiedCodeFormula
open ImplicationCodeFormula ChildrenCodeFormula StructuralSetEquations

universe u v

/-- U, syntax, assignments, five, six; cross, nodes, atoms, quantified,
square, triples, implications, children. Every product is checked too. -/
def formula : Delta0Formula 13 :=
  .conj (productAt 5 1 2)
    (.conj (filterAt matchingArityFormula ![] 5 6)
      (.conj (filterAt atomicFormula ![3] 6 7)
        (.conj (filterAt quantifiedFormula ![4] 6 8)
          (.conj (productAt 9 6 6)
            (.conj (productAt 10 6 9)
              (.conj (filterAt implicationFormula ![3] 10 11)
                (filterAt childrenFormula ![4, 0] 9 12)))))))

def Checks (p : Fin 13 → ZFSet.{u}) : Prop :=
  p 5 = pairProduct (p 1) (p 2) ∧
  p 6 = ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x]) (p 5) ∧
  p 7 = ZFSet.sep (fun x => Satisfies ZFMem atomicFormula ![p 3, x]) (p 6) ∧
  p 8 = ZFSet.sep (fun x => Satisfies ZFMem quantifiedFormula ![p 4, x]) (p 6) ∧
  p 9 = pairProduct (p 6) (p 6) ∧
  p 10 = pairProduct (p 6) (p 9) ∧
  p 11 = ZFSet.sep (fun x => Satisfies ZFMem implicationFormula ![p 3, x]) (p 10) ∧
  p 12 = ZFSet.sep (fun x => Satisfies ZFMem childrenFormula ![p 4, p 0, x]) (p 9)

theorem satisfies_formula (p : Fin 13 → ZFSet.{u}) :
    Satisfies ZFMem formula p ↔ Checks p := by
  have h0 (x : ZFSet.{u}) : snoc (fun i : Fin 0 => p (![] i)) x = ![x] := by
    funext i; fin_cases i; rfl
  have h1 (a : Fin 13) (x : ZFSet.{u}) :
      snoc (fun i : Fin 1 => p (![a] i)) x = ![p a, x] := by
    funext i; fin_cases i <;> rfl
  have h2 (a b : Fin 13) (x : ZFSet.{u}) :
      snoc (fun i : Fin 2 => p (![a, b] i)) x = ![p a, p b, x] := by
    funext i; fin_cases i <;> rfl
  simp only [formula, Satisfies, satisfies_productAt, satisfies_filterAt, h0, h1, h2, Checks]

attribute [irreducible] formula

def SourceParameters {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) (p : Fin 13 → ZFSet.{u}) : Prop :=
  p 0 = U ∧ p 1 = syntaxCodes (k := k) code ∧ p 2 = assignmentCodes U ∧
    p 3 = natCode 5 ∧ p 4 = natCode 6

def Canonical {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) (p : Fin 13 → ZFSet.{u}) : Prop :=
  p 5 = pairProduct (syntaxCodes (k := k) code) (assignmentCodes U) ∧
  p 6 = scopedPairs (k := k) U code ∧
  p 7 = atomSet (k := k) U code ∧
  p 8 = quantifiedSet (k := k) U code ∧
  p 9 = pairProduct (scopedPairs (k := k) U code) (scopedPairs (k := k) U code) ∧
  p 10 = pairProduct (scopedPairs (k := k) U code)
    (pairProduct (scopedPairs (k := k) U code) (scopedPairs (k := k) U code)) ∧
  p 11 = implicationSet (k := k) U code ∧
  p 12 = childrenSet (k := k) U code

theorem satisfies_iff_canonical {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u}) (p : Fin 13 → ZFSet.{u})
    (hp : SourceParameters (k := k) U code p) :
    Satisfies ZFMem formula p ↔ Canonical (k := k) U code p := by
  rw [satisfies_formula]
  obtain ⟨hU, hF, hA, h5, h6⟩ := hp
  constructor
  · rintro ⟨hcross, hn, ha, hq, hsq, ht, hi, hc⟩
    rw [hF, hA] at hcross
    rw [hcross, ← scopedPairs_eq_sep] at hn
    rw [h5, hn, ← atomSet_eq_sep] at ha
    rw [h6, hn, ← quantifiedSet_eq_sep] at hq
    rw [hn] at hsq
    rw [hn, hsq] at ht
    rw [h5, ht, ← implicationSet_eq_sep] at hi
    rw [h6, hU, hsq, ← childrenSet_eq_sep] at hc
    exact ⟨hcross, hn, ha, hq, hsq, ht, hi, hc⟩
  · rintro ⟨hcross, hn, ha, hq, hsq, ht, hi, hc⟩
    unfold Checks
    rw [hU, hF, hA, h5, h6, hcross, hn, ha, hq, hsq, ht, hi, hc]
    rw [← scopedPairs_eq_sep, ← atomSet_eq_sep, ← quantifiedSet_eq_sep,
      ← implicationSet_eq_sep, ← childrenSet_eq_sep]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def mixedFormula (K : Nat) (J : Type v) := ofConstructibleDeltaZero K J formula

theorem mixedFormula_isDeltaZero (K : Nat) (J : Type v) : IsDeltaZero (mixedFormula K J) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_iff_canonical {k : Nat} {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (code : I → ZFSet.{u})
    {W : ZFSet.{u}} {K : Nat} {J : Type v} (hW : W.IsTransitive)
    (N : Interpretation K J (ZFCarrier W)) (hmem : N.mem = zfCarrierMem W)
    (p : Fin 13 → ZFCarrier W)
    (hp : SourceParameters (k := k) U code (fun i => (p i).val)) :
    realize N (mixedFormula K J) Empty.elim p ↔
      Canonical (k := k) U code (fun i => (p i).val) := by
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute hW N hmem]
  exact satisfies_iff_canonical U code _ hp

end OneYTruth.StructuralDiagramCertificate
