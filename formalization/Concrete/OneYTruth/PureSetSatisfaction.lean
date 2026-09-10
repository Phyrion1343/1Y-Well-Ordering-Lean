import OneYTruth.PureSatisfactionMatrix
import OneYTruth.ConstructibleAtomicTruth
import OneYTruth.DirectSchemaCorrect

/-! Set-domain satisfaction and a single fixed bounded separation query.

The object formula is data in `packedCode`; it is never supplied as the
formula of a Separation call over the proper class L.
-/
namespace OneYTruth.PureSetSatisfaction

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open Constructible.Delta0Formula (ZFMem)
open FormulaCode InternalNodes ConstructibleAssignmentCodes
open ConstructibleBoundedIteration DirectSchema

universe u

theorem satisfaction_mem_L {D : ZFSet.{u}} (hD : D ∈ L) :
    satisfactionSet (Empty.elim : Empty → ZFSet.{u})
      (PureSatisfactionMatrix.interpretation D) ∈ L := by
  apply ConstructibleDiagramSources.satisfactionSet_mem_L_of_relation_graphs
    (fun e => e.elim) (PureSatisfactionMatrix.interpretation D)
    (fun _ _ => Iff.rfl) hD
  · rw [PureSatisfactionMatrix.empty_range]
    exact empty_mem_L
  · rw [PureSatisfactionMatrix.namedGraph_eq_empty]
    exact empty_mem_L
  · rw [PureSatisfactionMatrix.diagonalGraph_eq_empty]
    exact empty_mem_L

/-- The same fixed five-slot formula handles every input formula code. -/
def queryFormula : Delta0Formula 5 := extendedHoldsAt 0 1 2 3 4

theorem exists_separation {D : ZFSet.{u}} (hD : D ∈ L) {n : Nat}
    (φ : (language 0 Empty).BoundedFormula Empty (n + 1))
    (xs : Fin n → ZFCarrier D) (a : LCarrier.{u}) :
    ∃ b : LCarrier.{u}, b.val ⊆ a.val ∧ ∀ x : ZFCarrier D,
      x.val ∈ b.val ↔ x.val ∈ a.val ∧
        realize (PureSatisfactionMatrix.interpretation D) φ Empty.elim (Fin.snoc xs x) := by
  let A := assignmentCodes D
  have hA : A ∈ L := assignmentCodes_mem_L hD
  let S := satisfactionSet (Empty.elim : Empty → ZFSet.{u})
    (PureSatisfactionMatrix.interpretation D)
  have hS : S ∈ L := satisfaction_mem_L hD
  let e := packedCode (Empty.elim : Empty → ZFSet.{u}) ⟨n + 1, φ⟩
  have he : e ∈ L := packedCode_mem_L (fun i => i.elim) _
  have hp : assignmentCode xs ∈ L := mem_L_of_mem
    (ZFSet.mem_range_self (f := fun w : PackedAssignment D => assignmentCode w.2) ⟨n, xs⟩) hA
  let ps : Tuple LCarrier.{u} 4 := ![⟨A, hA⟩, ⟨S, hS⟩, ⟨e, he⟩, ⟨assignmentCode xs, hp⟩]
  let b := deltaSep queryFormula (fun i => (ps i).val) a.val
  have hbL : b ∈ L := deltaSep_mem_L queryFormula ps a
  have hb (z : ZFSet.{u}) : z ∈ b ↔ z ∈ a.val ∧
      ExtendedHolds A S e (assignmentCode xs) z := by
    change z ∈ ZFSet.sep _ a.val ↔ _
    rw [ZFSet.mem_sep]
    apply and_congr_right
    intro _
    change Delta0Formula.Satisfies ZFMem (extendedHoldsAt 0 1 2 3 4)
      (snoc (fun i => (ps i).val) z) ↔ _
    rw [satisfies_extendedHoldsAt]
    rfl
  refine ⟨⟨b, hbL⟩, (fun z hz => ((hb z).mp hz).1), fun x => ?_⟩
  exact (hb x.val).trans (and_congr Iff.rfl
    (extendedHolds_satisfaction (Empty.elim : Empty → ZFSet.{u}) (fun i => i.elim)
      (PureSatisfactionMatrix.interpretation D) φ xs x))

end OneYTruth.PureSetSatisfaction
