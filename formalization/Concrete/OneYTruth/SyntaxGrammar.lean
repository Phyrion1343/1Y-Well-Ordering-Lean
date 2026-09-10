import OneYTruth.SyntaxConstructorFormula

/-!
# The actual finite grammar underlying all scoped mixed formulas

The parameters are a code bound, alphabet, omega, diagonal bound, the seven
fixed tags, and a previous stage. A displayed Delta-zero formula recognizes
one grammar step, including exact child-scope matching.
-/

namespace OneYTruth.SyntaxGrammar

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FiniteCodeFormula SyntaxConstructorFormula

universe u

def RawRule (B A W K S n f : ZFSet.{u}) : Prop :=
  f = sequenceCode [natCode 0] ∨
  (∃ i ∈ n, ∃ j ∈ n, f = sequenceCode [natCode 1, i, j]) ∨
  (∃ i ∈ n, ∃ j ∈ n, f = sequenceCode [natCode 2, i, j]) ∨
  (∃ j ∈ K, ∃ ξ ∈ n, ∃ e ∈ n, ∃ a ∈ n,
    f = sequenceCode [natCode 3, j, ξ, e, a]) ∨
  (∃ ξ ∈ A, ∃ e ∈ n, ∃ a ∈ n, f = sequenceCode [natCode 4, ξ, e, a]) ∨
  (∃ g ∈ B, ∃ h ∈ B, f = sequenceCode [natCode 5, g, h] ∧
    ZFSet.pair n g ∈ S ∧ ZFSet.pair n h ∈ S) ∨
  (∃ g ∈ B, ∃ j ∈ W, j = insert n n ∧ f = sequenceCode [natCode 6, g] ∧
    ZFSet.pair j g ∈ S)

def ruleBody : Delta0Formula 15 :=
  .conj (kuratowskiPairEqAt 12 13 14)
    (.disj (sequenceEqAt 1 ![4] 14 5 4)
      (.disj (binaryAtomAt 5 13 14 7 4)
        (.disj (binaryAtomAt 6 13 14 7 4)
          (.disj (diagonalAtomAt 7 3 13 14 9 4)
            (.disj (namedAtomAt 8 1 13 14 8 4)
              (.disj (implicationAt 9 0 11 13 14 7 4)
                (allAt 10 0 2 11 13 14 6 4)))))))

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
    satisfies_allAt _ _ _ _ _ _ _ _ _ rfl rfl]
  simp [RawRule, chainCode_empty, List.ofFn_succ, sequenceCode, natCode]

attribute [irreducible] ruleBody

def ruleFormula : Delta0Formula 13 := .boundedEx 2 (.boundedEx 0 ruleBody)

noncomputable def parameters (B A W K S p : ZFSet.{u}) : Tuple ZFSet.{u} 13 :=
  ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
    natCode 4, natCode 5, natCode 6, S, p]

theorem satisfies_ruleFormula (B A W K S p : ZFSet.{u}) :
    Satisfies ZFMem ruleFormula (parameters B A W K S p) ↔
      ∃ n ∈ W, ∃ f ∈ B, p = ZFSet.pair n f ∧ RawRule B A W K S n f := by
  simp only [ruleFormula, Satisfies]
  change (∃ n ∈ W, ∃ f ∈ B,
    Satisfies ZFMem ruleBody (snoc (snoc (parameters B A W K S p) n) f)) ↔ _
  have htuple (n f : ZFSet.{u}) : snoc (snoc (parameters B A W K S p) n) f =
      ![B, A, W, K, ∅, natCode 1, natCode 2, natCode 3,
        natCode 4, natCode 5, natCode 6, S, p, n, f] := by
    rw [constructible_snoc_eq, constructible_snoc_eq]
    funext i
    fin_cases i <;> rfl
  simp only [htuple, satisfies_ruleBody]

end OneYTruth.SyntaxGrammar
