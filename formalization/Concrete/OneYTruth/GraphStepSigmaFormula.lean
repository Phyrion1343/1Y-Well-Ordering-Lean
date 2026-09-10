import OneYTruth.GraphStepCorrect
import OneYTruth.GraphStepSyntaxCertificate
import OneYTruth.ScopedExistentialBlock

/-! A literal twenty-one-existential prefix over a bounded whole-step matrix.
The fixed sources are the same thirteen parameters as the pure FO definition. -/

namespace OneYTruth.GraphStepSigma

open Constructible Constructible.Model Constructible.Delta0Formula
open FirstOrder FirstOrder.Language GraphStepMatrix BoundedEvaluation
open InternalIteration ConstructibleBoundedIteration

universe u v

def grammarMap : Fin 11 → Fin 34 := ![2,17,5,16,6,7,8,9,10,11,12]

def rest : Delta0Formula 34 :=
  .conj (kuratowskiPairEqAt 13 16 17)
    (.conj (PredecessorGraph.relationCertificate.rename relationMap)
      (.conj (StructuralDiagramCertificate.formula.rename structuralMap)
        (.conj (AtomicTruthFormula.certificate.rename atomicMap)
          (solutionFormula.rename solutionMap))))

def RestChecks (p : Tuple ZFSet.{u} 34) : Prop :=
  p 13 = ZFSet.pair (p 16) (p 17) ∧
    Satisfies ZFMem PredecessorGraph.relationCertificate (p ∘ relationMap) ∧
    Satisfies ZFMem StructuralDiagramCertificate.formula (p ∘ structuralMap) ∧
    Satisfies ZFMem AtomicTruthFormula.certificate (p ∘ atomicMap) ∧
    Satisfies ZFMem solutionFormula (p ∘ solutionMap)

theorem satisfies_rest (p : Tuple ZFSet.{u} 34) :
    Satisfies ZFMem rest p ↔ RestChecks p := by
  simp only [rest, Satisfies, satisfies_rename, satisfies_kuratowskiPairEqAt, RestChecks]
  rfl

def grammarMatrix : Delta0Formula 37 :=
  unionMatrixAt (filterGraph SyntaxGrammar.ruleFormula 0) grammarMap 6 5 6 18

def matrix : Delta0Formula 37 :=
  .conj (rest.rename (Fin.castAdd 3)) grammarMatrix

def syntaxQueryAt (K : Nat) (J : Type v) :=
  InternalBoundedIteration.grammarQueryAt K J SyntaxGrammar.ruleFormula 0 grammarMap 6 5 6 18

def partialQuery (K : Nat) (J : Type v) :=
  (ofConstructibleDeltaZero K J matrix).ex.ex.ex

def query (K : Nat) (J : Type v) :=
  ScopedExistentialBlock.bind 16 18 (partialQuery K J)

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query K J) :=
  ScopedExistentialBlock.isSigmaOne_bind 16 18 _
    (.ex (.ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero K J matrix)))))

theorem realize_partialQuery {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 34 → ZFCarrier V) :
    OneYTruth.realize N (partialQuery K J) Empty.elim p ↔
      RestChecks (fun i => (p i).val) ∧
        OneYTruth.realize N (syntaxQueryAt K J) Empty.elim p := by
  have hc (F H B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero K J matrix) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc p F) H) B) ↔
      RestChecks (fun i => (p i).val) ∧
        OneYTruth.realize N (ofConstructibleDeltaZero K J grammarMatrix) Empty.elim
          (Fin.snoc (Fin.snoc (Fin.snoc p F) H) B) := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem,
      realize_ofConstructibleDeltaZero_absolute hV N hmem]
    change (Satisfies ZFMem (rest.rename (Fin.castAdd 3)) _ ∧
      Satisfies ZFMem grammarMatrix _) ↔ _
    rw [satisfies_rename]
    have hp : (fun i => (Constructible.Delta0Formula.val
        (Fin.snoc (Fin.snoc (Fin.snoc p F) H) B)) (Fin.castAdd 3 i)) =
        (fun i => (p i).val) := by
      funext i
      change ((Fin.snoc (Fin.snoc (Fin.snoc p F) H) B : Fin 37 → ZFCarrier V)
        i.castSucc.castSucc.castSucc).val = (p i).val
      simp only [Fin.snoc_castSucc]
    rw [hp,satisfies_rest]
  change OneYTruth.realize N (ofConstructibleDeltaZero K J matrix).ex.ex.ex Empty.elim p ↔ _
  simp only [realize_scoped_ex, hc]
  change (∃ F H B, RestChecks (fun i => (p i).val) ∧
    OneYTruth.realize N (ofConstructibleDeltaZero K J grammarMatrix) Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc p F) H) B)) ↔
    RestChecks (fun i => (p i).val) ∧
      OneYTruth.realize N (ofConstructibleDeltaZero K J grammarMatrix).ex.ex.ex Empty.elim p
  simp only [realize_scoped_ex]
  constructor
  · rintro ⟨F,H,B,hR,hG⟩
    exact ⟨hR,F,H,B,hG⟩
  · rintro ⟨hR,F,H,B,hG⟩
    exact ⟨F,H,B,hR,hG⟩

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 16 → ZFCarrier V) :
    OneYTruth.realize N (query K J) Empty.elim p ↔
      ∃ w : Fin 18 → ZFCarrier V,
        RestChecks (fun i => (Fin.append p w i).val) ∧
          OneYTruth.realize N (syntaxQueryAt K J) Empty.elim (Fin.append p w) := by
  rw [query,ScopedExistentialBlock.realize_bind]
  exact exists_congr (fun _ => realize_partialQuery hV N hmem _)

end OneYTruth.GraphStepSigma
