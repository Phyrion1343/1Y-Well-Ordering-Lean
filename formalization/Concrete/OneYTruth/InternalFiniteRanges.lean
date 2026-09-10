import OneYTruth.InternalProducts

/-! Finite ranges follow from elementary set closure, independently of Replacement. -/

namespace OneYTruth.InternalProducts

open Constructible

universe u

theorem unorderedPair_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    {a b : ZFSet.{u}} (ha : a ∈ V) (hb : b ∈ V) : ({a, b} : ZFSet.{u}) ∈ V :=
  hV.mem_trans (by simp [ZFSet.pair]) (hpair a ha b hb)

theorem singleton_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    {a : ZFSet.{u}} (ha : a ∈ V) : ({a} : ZFSet.{u}) ∈ V :=
  hV.mem_trans (by simp [ZFSet.pair]) (hpair a ha a ha)

theorem binaryUnion_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {a b : ZFSet.{u}} (ha : a ∈ V) (hb : b ∈ V) : a ∪ b ∈ V := by
  have h : ZFSet.sUnion ({a, b} : ZFSet.{u}) = a ∪ b := by
    apply ZFSet.ext
    intro x
    simp
  rw [← h]
  exact hUnion _ (unorderedPair_mem hV hpair ha hb)

theorem insert_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {a b : ZFSet.{u}} (ha : a ∈ V) (hb : b ∈ V) : insert a b ∈ V := by
  rw [ZFSet.insert_eq]
  exact binaryUnion_mem hV hpair hUnion (singleton_mem hV hpair ha) hb

theorem range_fin_succ {n : Nat} (f : Fin (n + 1) → ZFSet.{u}) :
    ZFSet.range f = insert (f 0) (ZFSet.range (fun i : Fin n => f i.succ)) := by
  apply ZFSet.ext
  intro x
  simp [ZFSet.mem_range, Fin.exists_fin_succ, eq_comm]

theorem finiteRange_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {n : Nat} (f : Fin n → ZFSet.{u}) (hf : ∀ i, f i ∈ V) : ZFSet.range f ∈ V := by
  induction n with
  | zero =>
    have h : ZFSet.range f = ∅ := by
      apply ZFSet.ext
      intro x
      simp [ZFSet.mem_range]
    exact h.symm ▸ hempty
  | succ n ih =>
    rw [range_fin_succ]
    exact insert_mem hV hpair hUnion (hf 0) (ih (fun i => f i.succ) (fun i => hf i.succ))

end OneYTruth.InternalProducts
