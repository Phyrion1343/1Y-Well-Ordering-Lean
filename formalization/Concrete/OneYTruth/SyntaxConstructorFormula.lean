import OneYTruth.FiniteCodeFormula

/-!
# Literal formulas for the seven scoped syntax constructors

The atom formulas bound variable indices by the current arity, diagonal
indices by k, and named labels by the given alphabet. Implication and all
check actual packed child codes in the previous grammar stage.
-/

namespace OneYTruth.SyntaxConstructorFormula

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open FiniteCodeFormula BoundedEvaluation

universe u

def binaryAtomAt {n : Nat} (tag arity raw three zero : Fin n) : Delta0Formula n :=
  .boundedEx arity (.boundedEx arity.castSucc
    (sequenceEqAt 3 ![tag.castSucc.castSucc, (Fin.last n).castSucc, Fin.last (n + 1)]
      raw.castSucc.castSucc three.castSucc.castSucc zero.castSucc.castSucc))

theorem satisfies_binaryAtomAt {n : Nat} (tag arity raw three zero : Fin n)
    (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) (hthree : s three = natCode 3) :
    Satisfies ZFMem (binaryAtomAt tag arity raw three zero) s ↔
      ∃ i ∈ s arity, ∃ j ∈ s arity, s raw = sequenceCode [s tag, i, j] := by
  simp only [binaryAtomAt, Satisfies, satisfies_sequenceEqAt_chain, snoc_castSucc,
    hzero, hthree, chainCode_empty]
  simp [List.ofFn_succ, sequenceCode]

def namedAtomAt {n : Nat} (tag alphabet arity raw four zero : Fin n) : Delta0Formula n :=
  .boundedEx alphabet (.boundedEx arity.castSucc (.boundedEx arity.castSucc.castSucc
    (sequenceEqAt 4 ![tag.castSucc.castSucc.castSucc, (Fin.last n).castSucc.castSucc,
      (Fin.last (n + 1)).castSucc, Fin.last (n + 2)] raw.castSucc.castSucc.castSucc
      four.castSucc.castSucc.castSucc zero.castSucc.castSucc.castSucc)))

theorem satisfies_namedAtomAt {n : Nat} (tag alphabet arity raw four zero : Fin n)
    (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) (hfour : s four = natCode 4) :
    Satisfies ZFMem (namedAtomAt tag alphabet arity raw four zero) s ↔
      ∃ ξ ∈ s alphabet, ∃ e ∈ s arity, ∃ a ∈ s arity,
        s raw = sequenceCode [s tag, ξ, e, a] := by
  simp only [namedAtomAt, Satisfies, satisfies_sequenceEqAt_chain, snoc_castSucc,
    hzero, hfour, chainCode_empty]
  simp [List.ofFn_succ, sequenceCode]

def diagonalAtomAt {n : Nat} (tag k arity raw five zero : Fin n) : Delta0Formula n :=
  .boundedEx k (.boundedEx arity.castSucc (.boundedEx arity.castSucc.castSucc
    (.boundedEx arity.castSucc.castSucc.castSucc
      (sequenceEqAt 5 ![tag.castSucc.castSucc.castSucc.castSucc,
        (Fin.last n).castSucc.castSucc.castSucc, (Fin.last (n + 1)).castSucc.castSucc,
        (Fin.last (n + 2)).castSucc, Fin.last (n + 3)] raw.castSucc.castSucc.castSucc.castSucc
        five.castSucc.castSucc.castSucc.castSucc zero.castSucc.castSucc.castSucc.castSucc))))

theorem satisfies_diagonalAtomAt {n : Nat} (tag k arity raw five zero : Fin n)
    (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) (hfive : s five = natCode 5) :
    Satisfies ZFMem (diagonalAtomAt tag k arity raw five zero) s ↔
      ∃ j ∈ s k, ∃ ξ ∈ s arity, ∃ e ∈ s arity, ∃ a ∈ s arity,
        s raw = sequenceCode [s tag, j, ξ, e, a] := by
  simp only [diagonalAtomAt, Satisfies, satisfies_sequenceEqAt_chain, snoc_castSucc,
    hzero, hfive, chainCode_empty]
  simp [List.ofFn_succ, sequenceCode]

def implicationAt {n : Nat} (tag bound state arity raw three zero : Fin n) : Delta0Formula n :=
  .boundedEx bound (.boundedEx bound.castSucc
    (.conj (sequenceEqAt 3 ![tag.castSucc.castSucc, (Fin.last n).castSucc, Fin.last (n + 1)]
      raw.castSucc.castSucc three.castSucc.castSucc zero.castSucc.castSucc)
      (.conj (pairMemAt state.castSucc.castSucc arity.castSucc.castSucc (Fin.last n).castSucc)
        (pairMemAt state.castSucc.castSucc arity.castSucc.castSucc (Fin.last (n + 1))))))

theorem satisfies_implicationAt {n : Nat} (tag bound state arity raw three zero : Fin n)
    (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) (hthree : s three = natCode 3) :
    Satisfies ZFMem (implicationAt tag bound state arity raw three zero) s ↔
      ∃ f ∈ s bound, ∃ g ∈ s bound, s raw = sequenceCode [s tag, f, g] ∧
        ZFSet.pair (s arity) f ∈ s state ∧ ZFSet.pair (s arity) g ∈ s state := by
  simp only [implicationAt, Satisfies, satisfies_sequenceEqAt_chain, satisfies_pairMemAt,
    snoc_last, snoc_castSucc, hzero, hthree, chainCode_empty]
  simp [List.ofFn_succ, sequenceCode]

def allAt {n : Nat} (tag bound omega state arity raw two zero : Fin n) : Delta0Formula n :=
  .boundedEx bound (.boundedEx omega.castSucc
    (.conj (Delta0Formula.successorAt (Fin.last (n + 1)) arity.castSucc.castSucc)
      (.conj (sequenceEqAt 2 ![tag.castSucc.castSucc, (Fin.last n).castSucc]
        raw.castSucc.castSucc two.castSucc.castSucc zero.castSucc.castSucc)
        (pairMemAt state.castSucc.castSucc (Fin.last (n + 1)) (Fin.last n).castSucc))))

theorem satisfies_allAt {n : Nat} (tag bound omega state arity raw two zero : Fin n)
    (s : Tuple ZFSet.{u} n) (hzero : s zero = ∅) (htwo : s two = natCode 2) :
    Satisfies ZFMem (allAt tag bound omega state arity raw two zero) s ↔
      ∃ f ∈ s bound, ∃ j ∈ s omega, j = insert (s arity) (s arity) ∧
        s raw = sequenceCode [s tag, f] ∧ ZFSet.pair j f ∈ s state := by
  simp only [allAt, Satisfies, Delta0Formula.satisfies_successorAt, satisfies_sequenceEqAt_chain,
    satisfies_pairMemAt, snoc_last, snoc_castSucc, hzero, htwo, chainCode_empty]
  simp [List.ofFn_succ, sequenceCode]

end OneYTruth.SyntaxConstructorFormula
