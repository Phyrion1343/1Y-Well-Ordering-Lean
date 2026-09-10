import OneYTruth.DeltaZeroBridge
import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel

/-!
# An actual bounded formula for solving a set-coded evaluation diagram

The six diagram sets and a candidate truth set are parameters. Checking
the candidate uses an explicit `Delta0Formula`, compiled into the mixed
language with proved complexity and semantics. Constructing the canonical
diagram of all syntax and proving it belongs to an intended constructible
level remain separate tasks; no such existence is assumed as a theorem.
-/

namespace OneYTruth.BoundedEvaluation

open Constructible Constructible.Delta0Formula

universe u v

/-- A finite tuple of actual sets describes the local evaluation rules. -/
structure Diagram where
  nodes : ZFSet.{u}
  atoms : ZFSet.{u}
  trueAtoms : ZFSet.{u}
  implications : ZFSet.{u}
  quantified : ZFSet.{u}
  children : ZFSet.{u}

/-- Solving the diagram, expressed directly with bounded set membership. -/
def IsSolution (D : Diagram.{u}) (S : ZFSet.{u}) : Prop :=
  S ⊆ D.nodes ∧
  (∀ p ∈ D.atoms, p ∈ S ↔ p ∈ D.trueAtoms) ∧
  (∀ p ∈ D.nodes, ∀ a ∈ D.nodes, ∀ b ∈ D.nodes,
    Godel.triple p a b ∈ D.implications → (p ∈ S ↔ (a ∈ S → b ∈ S))) ∧
  (∀ p ∈ D.quantified, p ∈ S ↔
    ∀ q ∈ D.nodes, ZFSet.pair p q ∈ D.children → q ∈ S)

/-- The ordered pair of two coordinates belongs to a given relation. -/
def pairMemAt {n : Nat} (r x y : Fin n) : Delta0Formula n :=
  .boundedEx r (kuratowskiPairEqAt (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_pairMemAt {n : Nat} (r x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (pairMemAt r x y) s ↔ ZFSet.pair (s x) (s y) ∈ s r := by
  simp only [pairMemAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  exact ⟨fun ⟨p, hp, heq⟩ => heq ▸ hp, fun h => ⟨_, h, rfl⟩⟩

def tripleMemAt {n : Nat} (r x y z : Fin n) : Delta0Formula n :=
  .boundedEx r (tripleEqAt (Fin.last n) x.castSucc y.castSucc z.castSucc)

@[simp]
theorem satisfies_tripleMemAt {n : Nat} (r x y z : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (tripleMemAt r x y z) s ↔ Godel.triple (s x) (s y) (s z) ∈ s r := by
  simp only [tripleMemAt, Satisfies, satisfies_tripleEqAt,
    snoc_last, snoc_castSucc]
  exact ⟨fun ⟨p, hp, heq⟩ => heq ▸ hp, fun h => ⟨_, h, rfl⟩⟩

def atomicClauseAt {n : Nat} (S atoms truths : Fin n) : Delta0Formula n :=
  .boundedAll atoms (.biimp (.mem (Fin.last n) S.castSucc)
    (.mem (Fin.last n) truths.castSucc))

@[simp]
theorem satisfies_atomicClauseAt {n : Nat} (S atoms truths : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (atomicClauseAt S atoms truths) s ↔
      ∀ p ∈ s atoms, p ∈ s S ↔ p ∈ s truths := by
  simp only [atomicClauseAt, satisfies_boundedAll, satisfies_biimp, Satisfies,
    snoc_last, snoc_castSucc]

def implicationClauseAt {n : Nat} (S nodes implications : Fin n) : Delta0Formula n :=
  .boundedAll nodes (.boundedAll nodes.castSucc (.boundedAll nodes.castSucc.castSucc
    (.imp (tripleMemAt implications.castSucc.castSucc.castSucc
      (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc (Fin.last (n + 2)))
      (.biimp (.mem (Fin.last n).castSucc.castSucc S.castSucc.castSucc.castSucc)
        (.imp (.mem (Fin.last (n + 1)).castSucc S.castSucc.castSucc.castSucc)
          (.mem (Fin.last (n + 2)) S.castSucc.castSucc.castSucc))))))

@[simp]
theorem satisfies_implicationClauseAt {n : Nat} (S nodes implications : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (implicationClauseAt S nodes implications) s ↔
      ∀ p ∈ s nodes, ∀ a ∈ s nodes, ∀ b ∈ s nodes,
        Godel.triple p a b ∈ s implications → (p ∈ s S ↔ (a ∈ s S → b ∈ s S)) := by
  simp only [implicationClauseAt, satisfies_boundedAll, satisfies_imp,
    satisfies_biimp, satisfies_tripleMemAt, Satisfies, snoc_last, snoc_castSucc]

def universalClauseAt {n : Nat} (S nodes quantified children : Fin n) : Delta0Formula n :=
  .boundedAll quantified (.biimp (.mem (Fin.last n) S.castSucc)
    (.boundedAll nodes.castSucc
      (.imp (pairMemAt children.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1)))
        (.mem (Fin.last (n + 1)) S.castSucc.castSucc))))

@[simp]
theorem satisfies_universalClauseAt {n : Nat} (S nodes quantified children : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (universalClauseAt S nodes quantified children) s ↔
      ∀ p ∈ s quantified, p ∈ s S ↔
        ∀ q ∈ s nodes, ZFSet.pair p q ∈ s children → q ∈ s S := by
  simp only [universalClauseAt, satisfies_boundedAll, satisfies_biimp,
    satisfies_imp, satisfies_pairMemAt, Satisfies, snoc_last, snoc_castSucc]

/-- Coordinates: candidate, nodes, atoms, true atoms, implications, quantified, children. -/
def solutionFormula : Delta0Formula 7 :=
  .conj (subsetAt 0 1)
    (.conj (atomicClauseAt 0 2 3)
      (.conj (implicationClauseAt 0 1 4) (universalClauseAt 0 1 5 6)))

def parameters (D : Diagram.{u}) (S : ZFSet.{u}) : Tuple ZFSet.{u} 7 :=
  ![S, D.nodes, D.atoms, D.trueAtoms, D.implications, D.quantified, D.children]

/-- Correctness of the explicit pure bounded formula on its seven actual set parameters. -/
theorem satisfies_solutionFormula (D : Diagram.{u}) (S : ZFSet.{u}) :
    Satisfies ZFMem solutionFormula (parameters D S) ↔ IsSolution D S := by
  simp only [solutionFormula, Satisfies, satisfies_subsetAt, satisfies_atomicClauseAt,
    satisfies_implicationClauseAt, satisfies_universalClauseAt]
  rfl

/-- The same bounded formula in any mixed truth language. -/
def mixedSolutionFormula (k : Nat) (I : Type u) :=
  ofConstructibleDeltaZero k I solutionFormula

theorem mixedSolutionFormula_isDeltaZero (k : Nat) (I : Type u) :
    IsDeltaZero (mixedSolutionFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I solutionFormula

/-- An actual internal evaluation agrees with the external diagram test in a transitive set. -/
theorem realize_mixedSolutionFormula {k : Nat} {I : Type u} {U : ZFSet.{v}}
    (hU : U.IsTransitive) (M : Interpretation k I (ZFCarrier U))
    (hmem : M.mem = Constructible.zfCarrierMem U) (D : Diagram.{v}) (S : ZFSet.{v})
    (p : Fin 7 → ZFCarrier U)
    (hp : ∀ i, (p i).val = parameters D S i) :
    OneYTruth.realize M (mixedSolutionFormula k I) Empty.elim p ↔ IsSolution D S := by
  rw [mixedSolutionFormula, realize_ofConstructibleDeltaZero_absolute hU M hmem]
  have heq : Constructible.Delta0Formula.val p = parameters D S := funext hp
  rw [heq]
  exact satisfies_solutionFormula D S

end OneYTruth.BoundedEvaluation
