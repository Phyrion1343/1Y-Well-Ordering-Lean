import OneYTruth.PredecessorGraphQuery

/-! Whole product ranges, including finite literal block-code sets, in L. -/

namespace OneYTruth.ConstructibleDiagramSources

open Constructible Constructible.Model Constructible.Godel InternalProducts

universe u v w

theorem range_pair_eq_product {A : Type v} {B : Type w} [Small.{u} A] [Small.{u} B]
    (f : A → ZFSet.{u}) (g : B → ZFSet.{u}) :
    ZFSet.range (fun z : A × B => ZFSet.pair (f z.1) (g z.2)) =
      pairProduct (ZFSet.range f) (ZFSet.range g) := by
  apply ZFSet.ext
  intro z
  rw [pairProduct_eq_F2, mem_F2_iff]
  constructor
  · intro hz
    obtain ⟨⟨a, b⟩, rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨f a, ZFSet.mem_range_self a, g b, ZFSet.mem_range_self b, rfl⟩
  · rintro ⟨x, hx, y, hy, he⟩
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hx
    obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hy
    exact ZFSet.mem_range.mpr ⟨(a, b), he.symm⟩

theorem range_pair_mem_L {A : Type v} {B : Type w} [Small.{u} A] [Small.{u} B]
    {f : A → ZFSet.{u}} {g : B → ZFSet.{u}}
    (hf : ZFSet.range f ∈ L) (hg : ZFSet.range g ∈ L) :
    ZFSet.range (fun z : A × B => ZFSet.pair (f z.1) (g z.2)) ∈ L := by
  rw [range_pair_eq_product]
  exact pairProduct_mem_L hf hg

theorem finiteRange_mem_L {n : Nat} (f : Fin n → ZFSet.{u}) (hf : ∀ i, f i ∈ L) :
    ZFSet.range f ∈ L := by
  induction n with
  | zero =>
    have he : ZFSet.range f = ∅ := by ext x; simp [ZFSet.mem_range]
    rw [he]
    exact empty_mem_L
  | succ n ih =>
    rw [range_fin_succ, ZFSet.insert_eq]
    exact union_mem_L (singleton_mem_L (hf 0)) (ih (fun i => f i.succ) (fun i => hf i.succ))

end OneYTruth.ConstructibleDiagramSources
