import OneYTruth.TowerSigmaFormula
import OneYTruth.GraphStepMatrixSemantics

/-! Exact semantics of the bounded whole-tower matrix and its local records. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula CodedPaths BoundedFilterGraph

universe u v

theorem val_snoc {n : Nat} {V : ZFSet.{u}} (p : Fin n → ZFCarrier V) (a : ZFCarrier V) :
    val (Fin.snoc p a) = snoc (val p) a.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [val]

theorem entryMap_assignment (p : Tuple ZFSet.{u} 14) (D C B e : ZFSet.{u}) :
    (fun i => snoc (snoc (snoc (snoc p D) C) B) e (entryMap i)) =
      snoc (snoc p e) B := by
  funext i
  fin_cases i <;> simp [entryMap, constructible_snoc_eq, Fin.snoc, Fin.castLT]

def EntryChecks (p : Tuple ZFSet.{u} 39) : Prop :=
  p 14 = ZFSet.pair (p 15) (p 16) ∧
    p 17 = TowerRestriction.restrict (p 15) (p 13) ∧
    Satisfies ZFMem GraphStepSigma.matrix (fun i => p (localMap i))

theorem satisfies_entryMatrix (p : Tuple ZFSet.{u} 39) :
    Satisfies ZFMem entryMatrix p ↔ EntryChecks p := by
  simp only [entryMatrix,Satisfies,satisfies_kuratowskiPairEqAt,satisfies_rename]
  have he : (fun i => p (![15,13,17] i)) = ![p 15,p 13,p 17] := by
    funext i
    fin_cases i <;> rfl
  rw [he,TowerRestriction.satisfies_certificate]
  rfl

theorem satisfies_entryCertificate (p : Tuple ZFSet.{u} 15) (B : ZFSet.{u}) :
    Satisfies ZFMem entryCertificate (snoc p B) ↔
      ∃ w : Tuple ZFSet.{u} 24, (∀ i, w i ∈ B) ∧ EntryChecks (Fin.append p w) := by
  rw [entryCertificate,BoundedExistentialBlock.satisfies_certificate]
  exact exists_congr (fun _ => and_congr_right (fun _ => satisfies_entryMatrix _))

def Checks (p : Tuple ZFSet.{u} 14) (D C B : ZFSet.{u}) : Prop :=
  C = insert (p 1) (p 1) ∧ D = InternalProducts.pairProduct (p 5) C ∧
    ((∀ x ∈ D, ∃ e ∈ p 13, Component false e x) ∧
      (∀ e ∈ p 13, ∃ x ∈ D, Component false e x)) ∧
    ∀ e ∈ p 13, Satisfies ZFMem entryCertificate (snoc (snoc p e) B)

theorem satisfies_matrix (p : Tuple ZFSet.{u} 14) (D C B : ZFSet.{u}) :
    Satisfies ZFMem matrix (snoc (snoc (snoc p D) C) B) ↔ Checks p D C B := by
  simp only [matrix,Satisfies,satisfies_successorAt,satisfies_productAt,satisfies_coversAt,
    satisfies_boundedAll,satisfies_rename,snoc_last,snoc_castSucc]
  simp only [entryMap_assignment]
  simp [Checks,constructible_snoc_eq,Fin.snoc,Fin.castLT,ZFMem]

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 14 → ZFCarrier V) :
    OneYTruth.realize N (query K J) Empty.elim p ↔
      ∃ D C B : ZFCarrier V, Checks (fun i => (p i).val) D.val C.val B.val := by
  have hc (D C B : ZFCarrier V) :
      OneYTruth.realize N (ofConstructibleDeltaZero K J matrix) Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc p D) C) B) ↔
        Checks (fun i => (p i).val) D.val C.val B.val := by
    rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
    rw [val_snoc,val_snoc,val_snoc,satisfies_matrix]
    rfl
  simp only [query,realize_scoped_ex,hc]

end OneYTruth.TowerSigma
