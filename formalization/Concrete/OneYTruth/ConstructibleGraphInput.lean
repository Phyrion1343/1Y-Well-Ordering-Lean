import OneYTruth.GraphInputFormula

/-!
# The actual graph-input satisfaction operator preserves constructibility

The input q may be any constructible set. Its two literal relation graphs
are actual bounded filters, so the proved full satisfaction construction
applies without presupposing that q already is a correct tower.
-/

namespace OneYTruth.PredecessorGraph

open Constructible Constructible.Model Constructible.Godel Constructible.FiniteSequenceZF
open Constructible.Delta0Formula
open AtomicRelationGraphs ConstructibleDiagramSources InternalProducts

universe u v

set_option maxHeartbeats 200000


theorem namedGraph_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U κ q : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hU : U ∈ L) (hA : ZFSet.range indexCode ∈ L) (hq : q ∈ L) :
    namedGraph indexCode (interpretation k U indexCode κ q) ∈ L := by
  have hval : ZFSet.range (Subtype.val : ZFCarrier U → ZFSet.{u}) ∈ L := by
    rw [range_carrier_val_eq]
    exact hU

  have hsource : ZFSet.range (fun z : I × ZFCarrier U × ZFCarrier U =>
      triple (indexCode z.1) z.2.1.val z.2.2.val) ∈ L :=
    range_pair_mem_L (f := indexCode)
      (g := fun z : ZFCarrier U × ZFCarrier U => ZFSet.pair z.1.val z.2.val) hA
      (range_pair_mem_L (f := (Subtype.val : ZFCarrier U → ZFSet.{u}))
        (g := (Subtype.val : ZFCarrier U → ZFSet.{u})) hval hval)

  let ps : Tuple LCarrier.{u} 4 := ![⟨q,hq⟩, natLCarrier k,
    ⟨ZFSet.range indexCode,hA⟩, ⟨U,hU⟩]
  apply filtered_range_mem_L namedFormula ps
    (fun z : I × ZFCarrier U × ZFCarrier U => triple (indexCode z.1) z.2.1.val z.2.2.val)
    (fun z => (interpretation k U indexCode κ q).named z.1 z.2.1 z.2.2) hsource

  rintro ⟨i,e,a⟩
  have hp : snoc (fun i => (ps i).val) (triple (indexCode i) e.val a.val) =
      ![q,natCode k,ZFSet.range indexCode,U,triple (indexCode i) e.val a.val] := by
    funext i; fin_cases i <;> rfl
  rw [hp]
  exact satisfies_namedFormula_triple q (natCode k) _ U _ _ _
    (ZFSet.mem_range_self i) e.property a.property
theorem diagonalGraph_mem_L {k : Nat} {I : Type v}
    {U κ q : ZFSet.{u}} (indexCode : I → ZFSet.{u})
    (hU : U ∈ L) (hκ : κ ∈ L) (hq : q ∈ L) :
    diagonalGraph (interpretation k U indexCode κ q) ∈ L := by
  have hval : ZFSet.range (Subtype.val : ZFCarrier U → ZFSet.{u}) ∈ L := by
    rw [range_carrier_val_eq]
    exact hU

  have hB : ZFSet.range (fun j : Fin k => (natCode j.val : ZFSet.{u})) ∈ L :=
    finiteRange_mem_L (fun j : Fin k => (natCode j.val : ZFSet.{u})) (fun _ => natCode_mem_L _)
  have hsource : ZFSet.range (fun z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U =>
      quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val) ∈ L :=
    range_pair_mem_L (f := fun j : Fin k => (natCode j.val : ZFSet.{u}))
      (g := fun z : ZFCarrier U × ZFCarrier U × ZFCarrier U => triple z.1.val z.2.1.val z.2.2.val)
      hB (range_pair_mem_L (f := (Subtype.val : ZFCarrier U → ZFSet.{u}))
        (g := fun z : ZFCarrier U × ZFCarrier U => ZFSet.pair z.1.val z.2.val) hval
        (range_pair_mem_L (f := (Subtype.val : ZFCarrier U → ZFSet.{u}))
          (g := (Subtype.val : ZFCarrier U → ZFSet.{u})) hval hval))

  let ps : Tuple LCarrier.{u} 4 := ![⟨q,hq⟩, ⟨κ,hκ⟩,
    ⟨ZFSet.range (fun j : Fin k => natCode j.val),hB⟩, ⟨U,hU⟩]
  apply filtered_range_mem_L diagonalFormula ps
    (fun z : Fin k × ZFCarrier U × ZFCarrier U × ZFCarrier U =>
      quad (natCode z.1.val) z.2.1.val z.2.2.1.val z.2.2.2.val)
    (fun z => (interpretation k U indexCode κ q).diagonal z.1 z.2.1 z.2.2.1 z.2.2.2) hsource

  rintro ⟨j,ξ,e,a⟩
  have hp : snoc (fun i => (ps i).val) (quad (natCode j.val) ξ.val e.val a.val) =
      ![q,κ,ZFSet.range (fun j : Fin k => natCode j.val),U,quad (natCode j.val) ξ.val e.val a.val] := by
    funext i; fin_cases i <;> rfl
  rw [hp]
  exact satisfies_diagonalFormula_quad q κ _ U _ _ _ _
    (ZFSet.mem_range_self (f := fun j : Fin k => (natCode j.val : ZFSet.{u})) j) ξ.property e.property a.property
noncomputable def step (k : Nat) {I : Type v} [Small.{u} I]
    (U : ZFSet.{u}) (indexCode : I → ZFSet.{u}) (κ q : ZFSet.{u}) : ZFSet.{u} :=
  satisfactionSet indexCode (interpretation k U indexCode κ q)

theorem step_mem_L {k : Nat} {I : Type v} [Small.{u} I]
    {U κ q : ZFSet.{u}} {indexCode : I → ZFSet.{u}}
    (hi : Function.Injective indexCode) (hU : U ∈ L) (hA : ZFSet.range indexCode ∈ L)
    (hκ : κ ∈ L) (hq : q ∈ L) : step k U indexCode κ q ∈ L :=
  satisfactionSet_mem_L_of_relation_graphs hi _ (fun _ _ => Iff.rfl) hU hA
    (namedGraph_mem_L hU hA hq) (diagonalGraph_mem_L indexCode hU hκ hq)

end OneYTruth.PredecessorGraph







