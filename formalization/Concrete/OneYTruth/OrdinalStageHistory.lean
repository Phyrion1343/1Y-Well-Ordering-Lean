import OneYTruth.InternalGraphRestrictions
import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistoryGlobal

/-! # Actual ordinal histories and a Def-step-independent uniqueness theorem

The library supplies the actual canonical history's sharp local bound.
The semantic checker below is intentionally separate from any syntax class:
its later bounded implementation must supply a real Def certificate, not
reuse an unrestricted first-order formula as if it were Sigma-one.
-/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model

universe u

def Entry (g : ZFSet.{u}) (i : Ordinal.{u}) (U : ZFSet.{u}) : Prop :=
  ZFSet.pair i.toZFSet U ∈ g

/-- Ordinary stage recursion with a displayed successor-step predicate.
No uniqueness field is assumed; it follows from the recursion clauses. -/
structure Checks (step : ZFSet.{u} → ZFSet.{u} → Prop)
    (a : Ordinal.{u}) (g : ZFSet.{u}) : Prop where
  total : ∀ i ≤ a, ∃ U, Entry g i U
  noJunk : ∀ p ∈ g, ∃ i ≤ a, ∃ U, p = ZFSet.pair i.toZFSet U
  zero : ∀ U, Entry g 0 U → U = ∅
  successor : ∀ i, Order.succ i ≤ a → ∀ U D,
    Entry g i U → Entry g (Order.succ i) D → step U D
  limit : ∀ i, Order.IsSuccLimit i → i ≤ a → ∀ U, Entry g i U →
    ∀ z, z ∈ U ↔ ∃ j < i, ∃ T, Entry g j T ∧ z ∈ T

/-- Soundness only on stored successor pairs suffices. In the application
it follows from bounded Def certificates on the internal stage values. -/
def StepSound (step : ZFSet.{u} → ZFSet.{u} → Prop) (g : ZFSet.{u}) : Prop :=
  ∀ i U D, Entry g i U → Entry g (Order.succ i) D → step U D → D = DefZF U

theorem Checks.entry_eq {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {a : Ordinal.{u}} {g : ZFSet.{u}} (h : Checks step a g) (hstep : StepSound step g)
    (i : Ordinal.{u}) : ∀ U, i ≤ a → Entry g i U → U = LStageZF i := by
  induction i using Ordinal.limitRecOn with
  | zero =>
      intro U _ hU
      exact (h.zero U hU).trans LStageZF_zero.symm
  | add_one i ih =>
      rw [← Order.succ_eq_add_one]
      intro D hia hD
      obtain ⟨U, hU⟩ := h.total i ((Order.le_succ i).trans hia)
      have hUEq := ih U ((Order.le_succ i).trans hia) hU
      calc
        D = DefZF U := hstep i U D hU hD (h.successor i hia U D hU hD)
        _ = DefZF (LStageZF i) := congrArg DefZF hUEq
        _ = LStageZF (Order.succ i) := (LStageZF_succ i).symm
  | limit i hi ih =>
      intro U hia hU
      apply ZFSet.ext
      intro z
      rw [h.limit i hi hia U hU z, mem_LStageZF_limit_iff hi]
      constructor
      · rintro ⟨j, hji, T, hT, hz⟩
        exact ⟨j, hji, (ih j hji T (hji.le.trans hia) hT) ▸ hz⟩
      · rintro ⟨j, hji, hz⟩
        obtain ⟨T, hT⟩ := h.total j (hji.le.trans hia)
        exact ⟨j, hji, T, hT, (ih j hji T (hji.le.trans hia) hT).symm ▸ hz⟩

theorem Checks.eq_canonical {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {a : Ordinal.{u}} {g : ZFSet.{u}} (h : Checks step a g) (hstep : StepSound step g) :
    g = canonicalBareHistory a := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, hia, U, rfl⟩ := h.noJunk p hp
    exact pair_mem_canonicalBareHistory_iff.mpr ⟨i, hia, rfl, h.entry_eq hstep i U hia hp⟩
  · intro hp
    obtain ⟨i, hia, he⟩ := mem_canonicalBareHistory_iff.mp hp
    obtain ⟨U, hU⟩ := h.total i hia
    have hUEq := h.entry_eq hstep i U hia hU
    rw [← he, canonicalBareHistoryPair, ← hUEq]
    exact hU

theorem canonical_checks {step : ZFSet.{u} → ZFSet.{u} → Prop} (a : Ordinal.{u})
    (hstep : ∀ i, Order.succ i ≤ a → step (LStageZF i) (LStageZF (Order.succ i))) :
    Checks step a (canonicalBareHistory a) where
  total i hia := ⟨LStageZF i, pair_mem_canonicalBareHistory_iff.mpr ⟨i, hia, rfl, rfl⟩⟩
  noJunk p hp := by
    obtain ⟨i, hia, he⟩ := mem_canonicalBareHistory_iff.mp hp
    exact ⟨i, hia, LStageZF i, he.symm⟩
  zero U hU := by
    obtain ⟨i, _, hi, hU⟩ := pair_mem_canonicalBareHistory_iff.mp hU
    have hi0 : i = 0 := (Ordinal.toZFSet_injective hi).symm
    exact hU.trans (hi0 ▸ LStageZF_zero)
  successor i hia U D hU hD := by
    obtain ⟨j, _, hj, hU⟩ := pair_mem_canonicalBareHistory_iff.mp hU
    obtain ⟨k, _, hk, hD⟩ := pair_mem_canonicalBareHistory_iff.mp hD
    have hjEq : i = j := Ordinal.toZFSet_injective hj
    have hkEq : Order.succ i = k := Ordinal.toZFSet_injective hk
    rw [hU, hD, ← hjEq, ← hkEq]
    exact hstep i hia
  limit i hi hia U hU z := by
    obtain ⟨j, _, hj, hU⟩ := pair_mem_canonicalBareHistory_iff.mp hU
    have hij : i = j := Ordinal.toZFSet_injective hj
    rw [hU, ← hij, mem_LStageZF_limit_iff hi]
    constructor
    · rintro ⟨j, hji, hz⟩
      exact ⟨j, hji, LStageZF j,
        pair_mem_canonicalBareHistory_iff.mpr ⟨j, hji.le.trans hia, rfl, rfl⟩, hz⟩
    · rintro ⟨j, hji, T, hT, hz⟩
      obtain ⟨k, _, hjk, hT⟩ := pair_mem_canonicalBareHistory_iff.mp hT
      have hjkEq : j = k := Ordinal.toZFSet_injective hjk
      exact ⟨j, hji, (hT.trans (congrArg LStageZF hjkEq.symm)) ▸ hz⟩

/-- The actual history belongs to every limit stage above its top index.
This is stronger than the Adequate instance: no schema assumption is used. -/
theorem canonical_mem_of_limit {a β : Ordinal.{u}} (hβ : Order.IsSuccLimit β)
    (ha : a < β) : canonicalBareHistory a ∈ LStageZF β :=
  LStageZF_mono (add_omega_le_of_lt_isSuccLimit hβ ha)
    (canonicalBareHistory_mem_LStageZF_add_omega a)

theorem canonical_mem_of_adequate {a β : Ordinal.{u}} (hβ : RootSemantics.Adequate β)
    (ha : a < β) : canonicalBareHistory a ∈ LStageZF β := canonical_mem_of_limit hβ.2.1 ha

theorem entry_values_mem {V g : ZFSet.{u}} (hV : V.IsTransitive) (hg : g ∈ V)
    {i : Ordinal.{u}} {U : ZFSet.{u}} (h : Entry g i U) : U ∈ V := by
  have hp : ZFSet.pair i.toZFSet U ∈ V := hV.mem_trans h hg
  exact hV.mem_trans (by simp : U ∈ ({i.toZFSet, U} : ZFSet.{u}))
    (hV.mem_trans (by simp [ZFSet.pair] : ({i.toZFSet, U} : ZFSet.{u}) ∈ ZFSet.pair i.toZFSet U) hp)

theorem stepSound_of_internal {step : ZFSet.{u} → ZFSet.{u} → Prop} {V g : ZFSet.{u}}
    (hV : V.IsTransitive) (hg : g ∈ V)
    (hstep : ∀ U ∈ V, ∀ D ∈ V, step U D → D = DefZF U) : StepSound step g := by
  intro i U D hU hD hUD
  exact hstep U (entry_values_mem hV hg hU) D (entry_values_mem hV hg hD) hUD

/-- A checked internal history identifies its top domain with the actual
L_a, once the real local Def certificate is sound on internal sets. -/
theorem top_eq_of_internal {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {a : Ordinal.{u}} {V g U : ZFSet.{u}} (hV : V.IsTransitive) (hg : g ∈ V)
    (hstep : ∀ S ∈ V, ∀ D ∈ V, step S D → D = DefZF S)
    (h : Checks step a g) (hU : Entry g a U) : U = LStageZF a :=
  h.entry_eq (stepSound_of_internal hV hg hstep) a U le_rfl hU

/-- Actual internal witness existence with only the displayed Def-step
completeness interface remaining. History membership is already supplied. -/
theorem exists_internal_history {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {a β : Ordinal.{u}} (hβ : Order.IsSuccLimit β) (ha : a < β)
    (hstep : ∀ i, Order.succ i ≤ a → step (LStageZF i) (LStageZF (Order.succ i))) :
    ∃ g ∈ LStageZF β, Checks step a g ∧ Entry g a (LStageZF a) := by
  exact ⟨canonicalBareHistory a, canonical_mem_of_limit hβ ha, canonical_checks a hstep,
    canonicalBareHistory_top_mem a⟩

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.Checks.eq_canonical
#print axioms OneYTruth.OrdinalStageHistory.canonical_mem_of_adequate
