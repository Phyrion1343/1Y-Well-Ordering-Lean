import OneYTruth.DeltaSyntaxCodes

/-! # The actual finite existential-prefix grammar -/

namespace OneYTruth.SigmaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FormulaCode FiniteCodeFormula BoundedEvaluation

universe u v

theorem formulaCode_ex {k : Nat} {I : Type v} {n : Nat}
    (indexCode : I → ZFSet.{u}) (φ : (language k I).BoundedFormula Empty (n+1)) :
    formulaCode indexCode φ.ex = sequenceCode [natCode 5,
      sequenceCode [natCode 6, sequenceCode [natCode 5, formulaCode indexCode φ,
        sequenceCode [natCode 0] ] ], sequenceCode [natCode 0] ] := rfl

def exRule (B W S n f : ZFSet.{u}) : Prop :=
  ∃ g ∈ B, ∃ j ∈ W, ∃ a ∈ B, ∃ b ∈ B,
    j = insert n n ∧ a = sequenceCode [natCode 5, g, sequenceCode [natCode 0] ] ∧
      b = sequenceCode [natCode 6, a] ∧ f = sequenceCode [natCode 5, b, sequenceCode [natCode 0] ] ∧
        ZFSet.pair j g ∈ S

/-- B,omega,zero,falsum,tag5,tag6,two,three,state,p,n,f,g,j,a,b. -/
def exBody : Delta0Formula 16 :=
  .conj (kuratowskiPairEqAt 9 10 11)
    (.conj (Delta0Formula.successorAt 13 10)
      (.conj (sequenceEqAt 3 ![4, 12, 3] 14 7 2)
        (.conj (sequenceEqAt 2 ![5, 14] 15 6 2)
          (.conj (sequenceEqAt 3 ![4, 15, 3] 11 7 2) (pairMemAt 8 13 12)))))

theorem satisfies_exBody (B W S p n f g j a b : ZFSet.{u}) :
    Satisfies ZFMem exBody
      ![B, W, ∅, sequenceCode [natCode 0], natCode 5, natCode 6, natCode 2, natCode 3,
        S, p, n, f, g, j, a, b] ↔
      p = ZFSet.pair n f ∧ j = insert n n ∧
        a = sequenceCode [natCode 5, g, sequenceCode [natCode 0] ] ∧
        b = sequenceCode [natCode 6, a] ∧ f = sequenceCode [natCode 5, b, sequenceCode [natCode 0] ] ∧
          ZFSet.pair j g ∈ S := by
  simp only [exBody, Satisfies, satisfies_kuratowskiPairEqAt, Delta0Formula.satisfies_successorAt,
    satisfies_sequenceEqAt_chain, satisfies_pairMemAt]
  simp [chainCode_empty, List.ofFn_succ, sequenceCode]

attribute [irreducible] exBody

def ruleFormula : Delta0Formula 10 :=
  .disj (.mem 9 8) (.boundedEx 1 (.boundedEx 0 (.boundedEx 0
    (.boundedEx 1 (.boundedEx 0 (.boundedEx 0 exBody))))))

noncomputable def parameters (B W S p : ZFSet.{u}) : Tuple ZFSet.{u} 10 :=
  ![B, W, ∅, sequenceCode [natCode 0], natCode 5, natCode 6, natCode 2, natCode 3, S, p]

set_option maxHeartbeats 800000 in
theorem satisfies_ruleFormula (B W S p : ZFSet.{u}) :
    Satisfies ZFMem ruleFormula (parameters B W S p) ↔
      p ∈ S ∨ ∃ n ∈ W, ∃ f ∈ B, p = ZFSet.pair n f ∧ exRule B W S n f := by
  have ht (n f g j a b : ZFSet.{u}) : snoc (snoc (snoc (snoc (snoc (snoc
      (parameters B W S p) n) f) g) j) a) b =
      ![B, W, ∅, sequenceCode [natCode 0], natCode 5, natCode 6, natCode 2, natCode 3,
        S, p, n, f, g, j, a, b] := by
    simp only [constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  simp only [ruleFormula, satisfies_disj, Satisfies, ht, satisfies_exBody, exRule]
  simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
  change (p ∈ S ∨ ∃ n ∈ W, ∃ f ∈ B, ∃ g ∈ B, ∃ j ∈ W, ∃ a ∈ B, ∃ b ∈ B,
    p = ZFSet.pair n f ∧ j = insert n n ∧ a = sequenceCode [natCode 5, g, sequenceCode [natCode 0] ] ∧
      b = sequenceCode [natCode 6, a] ∧ f = sequenceCode [natCode 5, b, sequenceCode [natCode 0] ] ∧
        ZFSet.pair j g ∈ S) ↔ _
  simp only [← exists_and_left, ← and_assoc]
  simp only [and_assoc, and_left_comm, and_comm]

end OneYTruth.SigmaSyntaxGrammar

#print axioms OneYTruth.SigmaSyntaxGrammar.satisfies_ruleFormula
