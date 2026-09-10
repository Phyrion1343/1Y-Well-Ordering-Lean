import OneYTruth.DiagramCertificate

/-!
# Explicit Sigma-one truth and falsity queries with the diagram supplied

The formula existentially quantifies a candidate solution of the bounded
evaluation diagram. Both positive and negative truth queries are Sigma-one.
Their correctness inside a transitive ambient set requires that the actual
diagram parameters and canonical satisfaction set belong to that ambient
set. This is a precise conditional interface, not a proof of that missing
internal-existence requirement.
-/

namespace OneYTruth.LocalTruthQuery

open FirstOrder FirstOrder.Language Constructible Constructible.Delta0Formula
open BoundedEvaluation SyntaxDiagram

universe u v w

def bit (b : Bool) (P : Prop) : Prop := match b with
  | false => ¬ P
  | true => P

/-- Six diagram parameters, followed by a formula code and assignment code. -/
def queryParameters (D : Diagram.{u}) (e a : ZFSet.{u}) : Tuple ZFSet.{u} 8 :=
  ![D.nodes, D.atoms, D.trueAtoms, D.implications, D.quantified, D.children, e, a]

def solutionAtLast : Delta0Formula 9 :=
  Delta0Formula.rename ![8, 0, 1, 2, 3, 4, 5] solutionFormula

def matrix : Bool → Delta0Formula 9
  | false => .conj solutionAtLast (.neg (pairMemAt 8 6 7))
  | true => .conj solutionAtLast (pairMemAt 8 6 7)

theorem satisfies_matrix (b : Bool) (D : Diagram.{u}) (e a S : ZFSet.{u}) :
    Satisfies ZFMem (matrix b) (Constructible.snoc (queryParameters D e a) S) ↔
      IsSolution D S ∧ bit b (ZFSet.pair e a ∈ S) := by
  have hs : Satisfies ZFMem solutionAtLast (Constructible.snoc (queryParameters D e a) S) ↔
      IsSolution D S := by
    rw [solutionAtLast, Delta0Formula.satisfies_rename]
    have heq : (fun i : Fin 7 => Constructible.snoc (queryParameters D e a) S
        (![8, 0, 1, 2, 3, 4, 5] i)) = parameters D S := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact satisfies_solutionFormula D S
  have hp : Satisfies ZFMem (pairMemAt 8 6 7)
      (Constructible.snoc (queryParameters D e a) S) ↔ ZFSet.pair e a ∈ S := by
    rw [satisfies_pairMemAt]
    rfl
  cases b <;> simp only [matrix, Satisfies, hs, hp, bit]

/-- The only unbounded quantifier is the initial existential candidate set. -/
def formula (k : Nat) (I : Type u) (b : Bool) : (language k I).BoundedFormula Empty 8 :=
  (ofConstructibleDeltaZero k I (matrix b)).ex

theorem formula_isSigmaOne (k : Nat) (I : Type u) (b : Bool) :
    IsSigmaOne (formula k I b) :=
  .ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero k I (matrix b)))

/-- Semantics of the existential query, before assuming its canonical witness is internal. -/
theorem realize_formula_iff {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (b : Bool)
    (D : Diagram.{u}) (e a : ZFSet.{u}) (p : Fin 8 → ZFCarrier V)
    (hp : ∀ i, (p i).val = queryParameters D e a i) :
    OneYTruth.realize N (formula k I b) Empty.elim p ↔
      ∃ S : ZFCarrier V, IsSolution D S.val ∧ bit b (ZFSet.pair e a ∈ S.val) := by
  have hc (S : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero k I (matrix b)) Empty.elim (Fin.snoc p S) ↔
        IsSolution D S.val ∧ bit b (ZFSet.pair e a ∈ S.val) := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    have heq : Constructible.Delta0Formula.val (Fin.snoc p S) =
        Constructible.snoc (queryParameters D e a) S.val := by
      rw [constructible_snoc_eq]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Constructible.Delta0Formula.val, Fin.snoc_last]
      · simpa only [Constructible.Delta0Formula.val, Fin.snoc_castSucc] using hp j
    rw [heq]
    exact satisfies_matrix b D e a S.val
  letI := N.structure
  change (ofConstructibleDeltaZero k I (matrix b)).ex.Realize Empty.elim p ↔ _
  rw [BoundedFormula.realize_ex]
  exact exists_congr hc

/-- Both signs give the intended truth value when the canonical set is an internal witness. -/
theorem realize_formula_iff_canonical {k K : Nat} {I : Type v} {J : Type w}
    [Small.{u} I] {U V : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hi : Function.Injective indexCode) (M : Interpretation k I (ZFCarrier U))
    (hSat : satisfactionSet indexCode M ∈ V)
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V) (b : Bool)
    (e a : ZFSet.{u}) (p : Fin 8 → ZFCarrier V)
    (hp : ∀ i, (p i).val = queryParameters (diagram indexCode M) e a i) :
    OneYTruth.realize N (formula K J b) Empty.elim p ↔
      bit b (ZFSet.pair e a ∈ satisfactionSet indexCode M) := by
  rw [realize_formula_iff hV N hmem b _ e a p hp]
  constructor
  · rintro ⟨S, hS, hb⟩
    have heq := (isSolution_iff_eq_satisfactionSet hi M S.val).mp hS
    simpa only [heq] using hb
  · intro hb
    exact ⟨⟨satisfactionSet indexCode M, hSat⟩,
      (isSolution_iff_eq_satisfactionSet hi M _).mpr rfl, hb⟩

end OneYTruth.LocalTruthQuery
