import OneYTruth.AtomicArgumentLookup

/-! An actual bounded truth test on the genuine atomic-node source set. -/

namespace OneYTruth.AtomicTruthFormula

open Constructible Constructible.Delta0Formula Constructible.Godel
open AtomicArgumentLookup AtomicRelationGraphs CodedPaths BoundedEvaluation

universe u

structure Inputs (n : Nat) where
  domain : Fin n
  lookup : Fin n
  assignments : Fin n
  omega : Fin n
  alphabet : Fin n
  named : Fin n
  diagonal : Fin n
  node : Fin n

def Inputs.lift {n : Nat} (d : Inputs n) : Inputs (n + 1) where
  domain := d.domain.castSucc
  lookup := d.lookup.castSucc
  assignments := d.assignments.castSucc
  omega := d.omega.castSucc
  alphabet := d.alphabet.castSucc
  named := d.named.castSucc
  diagonal := d.diagonal.castSucc
  node := d.node.castSucc

def arg {n : Nat} (d : Inputs n) (field : Nat) (x : Fin n) : Delta0Formula n :=
  argumentAt (argumentPath field) d.lookup d.assignments d.omega d.node x

def equalityAt {n : Nat} (d : Inputs n) : Delta0Formula n :=
  .boundedEx d.domain (.conj (arg d.lift 1 (Fin.last n)) (arg d.lift 2 (Fin.last n)))

def membershipAt {n : Nat} (d : Inputs n) : Delta0Formula n :=
  .boundedEx d.domain (.boundedEx d.lift.domain
    (.conj (arg d.lift.lift 1 (Fin.last n).castSucc)
      (.conj (arg d.lift.lift 2 (Fin.last (n + 1))) (.mem (Fin.last n).castSucc (Fin.last (n + 1))))))

def namedAt {n : Nat} (d : Inputs n) : Delta0Formula n :=
  .boundedEx d.alphabet (.boundedEx d.lift.domain (.boundedEx d.lift.lift.domain
    (.conj (pathEqAt (argumentPath 1) d.lift.lift.lift.node (Fin.last n).castSucc.castSucc)
      (.conj (arg d.lift.lift.lift 2 (Fin.last (n + 1)).castSucc)
        (.conj (arg d.lift.lift.lift 3 (Fin.last (n + 2)))
          (tripleMemAt d.lift.lift.lift.named (Fin.last n).castSucc.castSucc
            (Fin.last (n + 1)).castSucc (Fin.last (n + 2))))))))

def diagonalAt {n : Nat} (d : Inputs n) : Delta0Formula n :=
  .boundedEx d.omega (.boundedEx d.lift.domain (.boundedEx d.lift.lift.domain
    (.boundedEx d.lift.lift.lift.domain
      (.conj (pathEqAt (argumentPath 1) d.lift.lift.lift.lift.node
        (Fin.last n).castSucc.castSucc.castSucc)
        (.conj (arg d.lift.lift.lift.lift 2 (Fin.last (n + 1)).castSucc.castSucc)
          (.conj (arg d.lift.lift.lift.lift 3 (Fin.last (n + 2)).castSucc)
            (.conj (arg d.lift.lift.lift.lift 4 (Fin.last (n + 3)))
              (quadMemAt d.lift.lift.lift.lift.diagonal (Fin.last n).castSucc.castSucc.castSucc
                (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 2)).castSucc (Fin.last (n + 3))))))))))

def Query (d : Inputs 12) (s : Tuple ZFSet.{u} 12) (field : Nat) (x : ZFSet.{u}) : Prop :=
  Argument (argumentPath field) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) x

theorem satisfies_equalityAt {n : Nat} (d : Inputs n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (equalityAt d) s ↔ ∃ x ∈ s d.domain,
      Argument (argumentPath 1) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) x ∧
      Argument (argumentPath 2) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) x := by
  simp only [equalityAt, arg, Satisfies, satisfies_argumentAt, Inputs.lift, snoc_last, snoc_castSucc, ZFMem]

theorem satisfies_membershipAt {n : Nat} (d : Inputs n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (membershipAt d) s ↔ ∃ x ∈ s d.domain, ∃ y ∈ s d.domain,
      Argument (argumentPath 1) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) x ∧
      Argument (argumentPath 2) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) y ∧ x ∈ y := by
  simp only [membershipAt, arg, Satisfies, satisfies_argumentAt, Inputs.lift,
    snoc_last, snoc_castSucc, ZFMem]

theorem satisfies_namedAt {n : Nat} (d : Inputs n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (namedAt d) s ↔ ∃ ξ ∈ s d.alphabet, ∃ e ∈ s d.domain, ∃ a ∈ s d.domain,
      Follows (argumentPath 1) (s d.node) ξ ∧
      Argument (argumentPath 2) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) e ∧
      Argument (argumentPath 3) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) a ∧
      triple ξ e a ∈ s d.named := by
  simp only [namedAt, arg, Satisfies, satisfies_argumentAt, satisfies_pathEqAt,
    satisfies_tripleMemAt, Inputs.lift, snoc_last, snoc_castSucc, ZFMem]

theorem satisfies_diagonalAt {n : Nat} (d : Inputs n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (diagonalAt d) s ↔ ∃ j ∈ s d.omega, ∃ ξ ∈ s d.domain,
      ∃ e ∈ s d.domain, ∃ a ∈ s d.domain, Follows (argumentPath 1) (s d.node) j ∧
      Argument (argumentPath 2) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) ξ ∧
      Argument (argumentPath 3) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) e ∧
      Argument (argumentPath 4) (s d.lookup) (s d.assignments) (s d.omega) (s d.node) a ∧
      quad j ξ e a ∈ s d.diagonal := by
  simp only [diagonalAt, arg, Satisfies, satisfies_argumentAt, satisfies_pathEqAt,
    satisfies_quadMemAt, Inputs.lift, snoc_last, snoc_castSucc, ZFMem]

def inputs : Inputs 12 := ⟨0, 1, 2, 3, 4, 5, 6, 11⟩

def formula : Delta0Formula 12 :=
  .disj (.conj (pathEqAt (argumentPath 0) 11 7) (equalityAt inputs))
    (.disj (.conj (pathEqAt (argumentPath 0) 11 8) (membershipAt inputs))
      (.disj (.conj (pathEqAt (argumentPath 0) 11 9) (diagonalAt inputs))
        (.conj (pathEqAt (argumentPath 0) 11 10) (namedAt inputs))))

end OneYTruth.AtomicTruthFormula
