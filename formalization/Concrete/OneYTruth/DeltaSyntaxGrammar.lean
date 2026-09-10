import OneYTruth.SigmaNodeConstruction

/-! # A literal bounded grammar for genuine Delta-zero formulas

Bounded universal syntax is the actual tree all(imp(mem(last,old),body)),
not an unrestricted all node. The intermediate raw codes are bounded by
the fixed, pair-closed code universe.
-/

namespace OneYTruth.DeltaSyntaxGrammar

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FormulaCode SyntaxConstructorFormula FiniteCodeFormula
open BoundedEvaluation

universe u v

theorem formulaCode_boundedAll {k : Nat} {I : Type v} {n : Nat}
    (indexCode : I → ZFSet.{u}) (t : (language k I).Term (Empty ⊕ Fin n))
    (φ : (language k I).BoundedFormula Empty (n+1)) :
    formulaCode indexCode (OneYTruth.boundedAll t φ) =
      sequenceCode [natCode 6, sequenceCode [natCode 5,
        sequenceCode [natCode 2, natCode n, natCode (termIndex t).val], formulaCode indexCode φ] ] := by
  cases t with
  | var a => cases a with
    | inl e => nomatch e
    | inr i => rfl
  | func e => nomatch e

def boundedAllBody : Delta0Formula 20 :=
  .conj (Delta0Formula.successorAt 17 13)
    (.conj (sequenceEqAt 3 ![6, 13, 15] 18 7 4)
      (.conj (sequenceEqAt 3 ![9, 18, 16] 19 7 4)
        (.conj (sequenceEqAt 2 ![10, 19] 14 6 4) (pairMemAt 11 17 16))))

def boundedAllFormula : Delta0Formula 15 :=
  .boundedEx 13 (.boundedEx 0 (.boundedEx 2 (.boundedEx 0 (.boundedEx 0 boundedAllBody))))

def boundedAllRule (B W S n f : ZFSet.{u}) : Prop :=
  ∃ i ∈ n, ∃ g ∈ B, ∃ j ∈ W, ∃ a ∈ B, ∃ b ∈ B,
    j = insert n n ∧ a = sequenceCode [natCode 2, n, i] ∧
      b = sequenceCode [natCode 5, a, g] ∧ f = sequenceCode [natCode 6, b] ∧
        ZFSet.pair j g ∈ S

theorem satisfies_boundedAllBody (B A W K S p n f i g j a b : ZFSet.{u}) :
    Satisfies ZFMem boundedAllBody
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f, i, g, j, a, b] ↔
      j = insert n n ∧ a = sequenceCode [natCode 2, n, i] ∧
        b = sequenceCode [natCode 5, a, g] ∧ f = sequenceCode [natCode 6, b] ∧ ZFSet.pair j g ∈ S := by
  simp only [boundedAllBody, Satisfies, Delta0Formula.satisfies_successorAt,
    satisfies_sequenceEqAt_chain, satisfies_pairMemAt]
  simp [chainCode_empty, List.ofFn_succ, sequenceCode]

attribute [irreducible] boundedAllBody

set_option maxHeartbeats 800000 in
theorem satisfies_boundedAllFormula (B A W K S p n f : ZFSet.{u}) :
    Satisfies ZFMem boundedAllFormula
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f] ↔ boundedAllRule B W S n f := by
  have ht (i g j a b : ZFSet.{u}) : snoc (snoc (snoc (snoc (snoc
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f] i) g) j) a) b =
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f, i, g, j, a, b] := by
    simp only [constructible_snoc_eq]
    funext l
    fin_cases l <;> rfl
  simp only [boundedAllFormula, Satisfies, ht, satisfies_boundedAllBody, boundedAllRule]
  simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
  rfl

def RawRule (B A W K S n f : ZFSet.{u}) : Prop :=
  f = sequenceCode [natCode 0] ∨
  (∃ i ∈ n, ∃ j ∈ n, f = sequenceCode [natCode 1, i, j]) ∨
  (∃ i ∈ n, ∃ j ∈ n, f = sequenceCode [natCode 2, i, j]) ∨
  (∃ j ∈ K, ∃ ξ ∈ n, ∃ e ∈ n, ∃ a ∈ n,
    f = sequenceCode [natCode 3, j, ξ, e, a]) ∨
  (∃ ξ ∈ A, ∃ e ∈ n, ∃ a ∈ n, f = sequenceCode [natCode 4, ξ, e, a]) ∨
  (∃ g ∈ B, ∃ h ∈ B, f = sequenceCode [natCode 5, g, h] ∧
    ZFSet.pair n g ∈ S ∧ ZFSet.pair n h ∈ S) ∨ boundedAllRule B W S n f

def ruleBody : Delta0Formula 15 :=
  .conj (kuratowskiPairEqAt 12 13 14)
    (.disj (sequenceEqAt 1 ![4] 14 5 4)
      (.disj (binaryAtomAt 5 13 14 7 4)
        (.disj (binaryAtomAt 6 13 14 7 4)
          (.disj (diagonalAtomAt 7 3 13 14 9 4)
            (.disj (namedAtomAt 8 1 13 14 8 4)
              (.disj (implicationAt 9 0 11 13 14 7 4) boundedAllFormula))))))

theorem satisfies_ruleBody (B A W K S p n f : ZFSet.{u}) :
    Satisfies ZFMem ruleBody
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f] ↔
      p = ZFSet.pair n f ∧ RawRule B A W K S n f := by
  simp only [ruleBody, Satisfies, satisfies_kuratowskiPairEqAt, satisfies_disj]
  rw [satisfies_sequenceEqAt_chain,
    satisfies_binaryAtomAt _ _ _ _ _ _ rfl rfl,
    satisfies_binaryAtomAt _ _ _ _ _ _ rfl rfl,
    satisfies_diagonalAtomAt _ _ _ _ _ _ _ rfl rfl,
    satisfies_namedAtomAt _ _ _ _ _ _ _ rfl rfl,
    satisfies_implicationAt _ _ _ _ _ _ _ _ rfl rfl,
    satisfies_boundedAllFormula]
  simp [RawRule, chainCode_empty, List.ofFn_succ, sequenceCode, natCode]

attribute [irreducible] ruleBody

/-- Old members are retained, making this bounded construction cumulative. -/
def ruleFormula : Delta0Formula 13 :=
  .disj (.mem 12 11) (.boundedEx 2 (.boundedEx 0 ruleBody))

theorem satisfies_ruleFormula (B A W K S p : ZFSet.{u}) :
    Satisfies ZFMem ruleFormula (SyntaxGrammar.parameters B A W K S p) ↔
      p ∈ S ∨ ∃ n ∈ W, ∃ f ∈ B, p = ZFSet.pair n f ∧ RawRule B A W K S n f := by
  simp only [ruleFormula, satisfies_disj, Satisfies]
  change (p ∈ S ∨ ∃ n ∈ W, ∃ f ∈ B,
    Satisfies ZFMem ruleBody (snoc (snoc (SyntaxGrammar.parameters B A W K S p) n) f)) ↔ _
  have ht (n f : ZFSet.{u}) : snoc (snoc (SyntaxGrammar.parameters B A W K S p) n) f =
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f] := by
    simp only [constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  simp only [ht, satisfies_ruleBody]

end OneYTruth.DeltaSyntaxGrammar

#print axioms OneYTruth.DeltaSyntaxGrammar.satisfies_ruleFormula
