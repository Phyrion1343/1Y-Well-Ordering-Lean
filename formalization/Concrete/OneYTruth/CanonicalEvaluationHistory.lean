import OneYTruth.EvaluationHistory
import OneYTruth.InternalFiniteRanges

/-! Real finite history witnesses, including their internal set existence. -/

namespace OneYTruth.BoundedEvaluation

open Constructible Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF
open InternalProducts InternalClosure

universe u v

noncomputable def finiteHistory (D : Diagram.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n + 1) => ZFSet.pair (natCode i.val) (iterate D i.val))

noncomputable def historyContainer (D : Diagram.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n + 1) => natCode i.val) ∪
    ZFSet.range (fun i : Fin (n + 1) => iterate D i.val)

theorem index_mem_historyContainer (D : Diagram.{u}) (n : Nat) (i : Fin (n + 1)) :
    natCode i.val ∈ historyContainer D n :=
  ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_range_self
    (f := fun j : Fin (n + 1) => (natCode j.val : ZFSet.{u})) i))

theorem value_mem_historyContainer (D : Diagram.{u}) (n : Nat) (i : Fin (n + 1)) :
    iterate D i.val ∈ historyContainer D n :=
  ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_range_self
    (f := fun j : Fin (n + 1) => iterate D j.val) i))

theorem finiteHistory_isHistory (D : Diagram.{u}) (n : Nat) :
    IsHistory D (finiteHistory D n) (historyContainer D n) := by
  intro p hp
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
  refine ⟨natCode i.val, index_mem_historyContainer D n i,
    iterate D i.val, value_mem_historyContainer D n i, rfl,
    (mem_omega_iff_exists_natCode _).mpr ⟨i.val, rfl⟩, ?_⟩
  cases hv : i.val with
  | zero =>
    exact Or.inl ⟨by simp [natCode], rfl⟩
  | succ m =>
    have hm : m < n + 1 := by have hi := i.isLt; omega
    refine Or.inr ⟨natCode m, index_mem_historyContainer D n ⟨m, hm⟩,
      iterate D m, value_mem_historyContainer D n ⟨m, hm⟩,
      ZFSet.mem_range_self (f := fun j : Fin (n + 1) =>
        ZFSet.pair (natCode j.val) (iterate D j.val)) ⟨m, hm⟩,
      (isSuccessor_natCode_iff (m + 1) m).mpr rfl, rfl⟩

theorem last_mem_finiteHistory (D : Diagram.{u}) (n : Nat) :
    ZFSet.pair (natCode n) (iterate D n) ∈ finiteHistory D n :=
  ZFSet.mem_range_self (f := fun i : Fin (n + 1) =>
    ZFSet.pair (natCode i.val) (iterate D i.val)) (Fin.last n)

theorem finiteHistory_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedStepFormula k I))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (hempty : (∅ : ZFSet.{u}) ∈ V) (hNat : ∀ n : Nat, (natCode n : ZFSet.{u}) ∈ V)
    (D : Diagram.{u}) (hD : ∀ i, parameters D ∅ i ∈ V) (n : Nat) : finiteHistory D n ∈ V := by
  exact finiteRange_mem hV hpair hUnion hempty _ (fun i =>
    hpair _ (hNat i.val) _ (iterate_mem hV N hmem hSep hempty D hD i.val))

theorem historyContainer_mem {k : Nat} {I : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation k I (ZFCarrier V))
    (hmem : N.mem = Constructible.zfCarrierMem V)
    (hSep : SeparationInstance N (mixedStepFormula k I))
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (hempty : (∅ : ZFSet.{u}) ∈ V) (hNat : ∀ n : Nat, (natCode n : ZFSet.{u}) ∈ V)
    (D : Diagram.{u}) (hD : ∀ i, parameters D ∅ i ∈ V) (n : Nat) : historyContainer D n ∈ V := by
  exact binaryUnion_mem hV hpair hUnion
    (finiteRange_mem hV hpair hUnion hempty _ (fun i => hNat i.val))
    (finiteRange_mem hV hpair hUnion hempty _
      (fun i => iterate_mem hV N hmem hSep hempty D hD i.val))

end OneYTruth.BoundedEvaluation
