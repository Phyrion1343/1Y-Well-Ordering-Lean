import OneYTruth.ConstructibleGraphInput
import OneYTruth.BoundedFilterGraph

/-! Complete bounded certificates for the two relations read from a graph. -/

namespace OneYTruth.PredecessorGraph

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Godel Constructible.Model Constructible.IndexedSequenceZF
open AtomicRelationGraphs ConstructibleDiagramSources InternalProducts BoundedFilterGraph

universe u v

theorem range_fin_natCode (k : Nat) :
    ZFSet.range (fun j : Fin k => (natCode j.val : ZFSet.{u})) = natCode k := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, mem_natCode_iff_exists_lt]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j.val,j.isLt,hj.symm⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨⟨j,hj⟩,he.symm⟩

theorem namedSource_range {I : Type v} [Small.{u} I] (U : ZFSet.{u}) (c : I → ZFSet.{u}) :
    ZFSet.range (fun z : I × ZFCarrier U × ZFCarrier U => triple (c z.1) z.2.1.val z.2.2.val) =
      pairProduct (ZFSet.range c) (pairProduct U U) := by
  change ZFSet.range (fun z : I × ZFCarrier U × ZFCarrier U =>
    ZFSet.pair (c z.1) (ZFSet.pair z.2.1.val z.2.2.val)) = _
  rw [range_pair_eq_product c (fun z : ZFCarrier U × ZFCarrier U => ZFSet.pair z.1.val z.2.val)]
  rw [range_pair_eq_product (Subtype.val : ZFCarrier U → ZFSet.{u})
    (Subtype.val : ZFCarrier U → ZFSet.{u}), range_carrier_val_eq]

theorem diagonalSource_range (k : Nat) (U : ZFSet.{u}) :
    ZFSet.range (fun z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U =>
      quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val) =
      pairProduct (natCode k) (pairProduct U (pairProduct U U)) := by
  change ZFSet.range (fun z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U =>
    ZFSet.pair (natCode z.1.val) (triple z.2.1.val z.2.2.1.val z.2.2.2.val)) = _
  rw [range_pair_eq_product (fun j : Fin k => (natCode j.val : ZFSet.{u}))
    (fun z : ZFCarrier U × ZFCarrier U × ZFCarrier U => triple z.1.val z.2.1.val z.2.2.val)]
  rw [range_fin_natCode, namedSource_range, range_carrier_val_eq]

theorem namedGraph_eq_sep {k : Nat} {I : Type v} [Small.{u} I]
    (U κ q : ZFSet.{u}) (c : I → ZFSet.{u}) :
    namedGraph c (interpretation k U c κ q) =
      ZFSet.sep (fun x => Satisfies ZFMem namedFormula (snoc ![q,natCode k,ZFSet.range c,U] x))
        (pairProduct (ZFSet.range c) (pairProduct U U)) := by
  have he := filtered_range_eq_sep
    (fun z : I × ZFCarrier U × ZFCarrier U => triple (c z.1) z.2.1.val z.2.2.val)
    (fun z => (interpretation k U c κ q).named z.1 z.2.1 z.2.2)
    namedFormula ![q,natCode k,ZFSet.range c,U] (fun z => ?_)
  · rw [namedSource_range] at he
    exact he
  · have hp : snoc ![q,natCode k,ZFSet.range c,U] (triple (c z.1) z.2.1.val z.2.2.val) =
        ![q,natCode k,ZFSet.range c,U,triple (c z.1) z.2.1.val z.2.2.val] := by
      funext i; fin_cases i <;> rfl
    rw [hp]
    exact satisfies_namedFormula_triple q (natCode k) _ U _ _ _
      (ZFSet.mem_range_self z.1) z.2.1.property z.2.2.property

theorem diagonalGraph_eq_sep {k : Nat} {I : Type v}
    (U κ q : ZFSet.{u}) (c : I → ZFSet.{u}) :
    diagonalGraph (interpretation k U c κ q) =
      ZFSet.sep (fun x => Satisfies ZFMem diagonalFormula (snoc ![q,κ,natCode k,U] x))
        (pairProduct (natCode k) (pairProduct U (pairProduct U U))) := by
  have he := filtered_range_eq_sep
    (fun z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U =>
      quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val)
    (fun z => (interpretation k U c κ q).diagonal z.1 z.2.1 z.2.2.1 z.2.2.2)
    diagonalFormula ![q,κ,natCode k,U] (fun z => ?_)
  · rw [diagonalSource_range] at he
    exact he
  · have hp : snoc ![q,κ,natCode k,U] (quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val) =
        ![q,κ,natCode k,U,quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val] := by
      funext i; fin_cases i <;> rfl
    rw [hp]
    exact satisfies_diagonalFormula_quad q κ _ U _ _ _ _
      ((natCode_mem_natCode_iff _ _).mpr z.1.isLt)
      z.2.1.property z.2.2.1.property z.2.2.2.property

/-- q,block,alphabet,U,kappa,UU,UUU,namedSource,diagonalSource,named,diagonal. -/
def relationCertificate : Delta0Formula 11 :=
  .conj (productAt 5 3 3)
    (.conj (productAt 6 3 5)
      (.conj (productAt 7 2 5)
        (.conj (productAt 8 1 6)
          (.conj (filterAt namedFormula ![0,1,2,3] 7 9)
            (filterAt diagonalFormula ![0,4,1,3] 8 10)))))

def RelationChecks (p : Tuple ZFSet.{u} 11) : Prop :=
  p 5 = pairProduct (p 3) (p 3) ∧ p 6 = pairProduct (p 3) (p 5) ∧
    p 7 = pairProduct (p 2) (p 5) ∧ p 8 = pairProduct (p 1) (p 6) ∧
    p 9 = ZFSet.sep (fun x => Satisfies ZFMem namedFormula (snoc ![p 0,p 1,p 2,p 3] x)) (p 7) ∧
    p 10 = ZFSet.sep (fun x => Satisfies ZFMem diagonalFormula (snoc ![p 0,p 4,p 1,p 3] x)) (p 8)

theorem satisfies_relationCertificate (p : Tuple ZFSet.{u} 11) :
    Satisfies ZFMem relationCertificate p ↔ RelationChecks p := by
  simp only [relationCertificate, Satisfies, satisfies_productAt, satisfies_filterAt, RelationChecks]
  rfl

attribute [irreducible] relationCertificate

theorem relationCertificate_canonical {k : Nat} {I : Type v} [Small.{u} I]
    (U κ q : ZFSet.{u}) (c : I → ZFSet.{u}) (X Y A B N D : ZFSet.{u}) :
    Satisfies ZFMem relationCertificate ![q,natCode k,ZFSet.range c,U,κ,X,Y,A,B,N,D] ↔
      X = pairProduct U U ∧ Y = pairProduct U (pairProduct U U) ∧
      A = pairProduct (ZFSet.range c) (pairProduct U U) ∧
      B = pairProduct (natCode k) (pairProduct U (pairProduct U U)) ∧
      N = namedGraph c (interpretation k U c κ q) ∧ D = diagonalGraph (interpretation k U c κ q) := by
  rw [satisfies_relationCertificate]
  change (X = pairProduct U U ∧ Y = pairProduct U X ∧ A = pairProduct (ZFSet.range c) X ∧
    B = pairProduct (natCode k) Y ∧
    N = ZFSet.sep (fun x => Satisfies ZFMem namedFormula (snoc ![q,natCode k,ZFSet.range c,U] x)) A ∧
    D = ZFSet.sep (fun x => Satisfies ZFMem diagonalFormula (snoc ![q,κ,natCode k,U] x)) B) ↔ _
  constructor
  · rintro ⟨rfl,rfl,rfl,rfl,hN,hD⟩
    rw [← namedGraph_eq_sep U κ q c] at hN
    rw [← diagonalGraph_eq_sep U κ q c] at hD
    exact ⟨rfl,rfl,rfl,rfl,hN,hD⟩
  · rintro ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    exact ⟨rfl,rfl,rfl,rfl,namedGraph_eq_sep U κ q c,diagonalGraph_eq_sep U κ q c⟩

end OneYTruth.PredecessorGraph
