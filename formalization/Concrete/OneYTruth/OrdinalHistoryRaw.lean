import OneYTruth.OrdinalStageHistory

/-! # The bounded set-coordinate form of ordinal history clauses -/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model Constructible.Godel

universe u

def RawLimit (i : ZFSet.{u}) : Prop := i ≠ ∅ ∧ ∀ j ∈ i, i ≠ insert j j

theorem rawLimit_code (i : Ordinal.{u}) : RawLimit i.toZFSet ↔ Order.IsSuccLimit i := by
  constructor
  · rintro ⟨hzero, hsucc⟩
    rcases Ordinal.zero_or_succ_or_isSuccLimit i with hi | ⟨j, hj⟩ | hi
    · exact False.elim (hzero (hi ▸ Ordinal.toZFSet_zero))
    · subst i
      exact False.elim (hsucc j.toZFSet
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ j))
        ((ordinalToZFSet_successor_predecessor_iff j j.toZFSet).mpr rfl))
    · exact hi
  · intro hi
    refine ⟨?_, fun j _ he => ordinalToZFSet_limit_no_predecessor hi ⟨j, he⟩⟩
    intro he
    exact hi.ne_bot (Ordinal.toZFSet_injective (he.trans Ordinal.toZFSet_zero.symm))

structure RawChecks (step : ZFSet.{u} → ZFSet.{u} → Prop)
    (I g B : ZFSet.{u}) : Prop where
  total : ∀ i ∈ I, ∃ U ∈ B, ZFSet.pair i U ∈ g
  noJunk : ∀ p ∈ g, ∃ i ∈ I, ∃ U ∈ B, p = ZFSet.pair i U
  zero : ∀ U ∈ B, ZFSet.pair ∅ U ∈ g → U = ∅
  successor : ∀ i ∈ I, ∀ j ∈ I, j = insert i i → ∀ U ∈ B, ∀ D ∈ B,
    ZFSet.pair i U ∈ g → ZFSet.pair j D ∈ g → step U D
  limit : ∀ i ∈ I, RawLimit i → ∀ U ∈ B, ZFSet.pair i U ∈ g →
    ∀ z, z ∈ U ↔ ∃ j ∈ i, ∃ T ∈ B, ZFSet.pair j T ∈ g ∧ z ∈ T

theorem RawChecks.value_mem {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {I g B i U : ZFSet.{u}} (h : RawChecks step I g B) (he : ZFSet.pair i U ∈ g) : U ∈ B := by
  obtain ⟨j, _, T, hT, hjT⟩ := h.noJunk _ he
  exact (ZFSet.pair_inj.mp hjT).2.symm ▸ hT

theorem RawChecks.toChecks {step : ZFSet.{u} → ZFSet.{u} → Prop}
    {a : Ordinal.{u}} {g B : ZFSet.{u}} (h : RawChecks step (Order.succ a).toZFSet g B) :
    Checks step a g where
  total i hi := by
    obtain ⟨U, _, hU⟩ := h.total i.toZFSet
      (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr hi))
    exact ⟨U, hU⟩
  noJunk p hp := by
    obtain ⟨index, hi, U, _, he⟩ := h.noJunk p hp
    obtain ⟨i, hia, hi⟩ := Ordinal.mem_toZFSet_iff.mp hi
    exact ⟨i, Order.lt_succ_iff.mp hia, U, hi ▸ he⟩
  zero U hU := h.zero U (h.value_mem hU) (by simpa only [Entry, Ordinal.toZFSet_zero] using hU)
  successor i hi U D hU hD := by
    apply h.successor i.toZFSet
      (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr ((Order.le_succ i).trans hi)))
      (Order.succ i).toZFSet
      (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr hi))
      ((ordinalToZFSet_successor_predecessor_iff i i.toZFSet).mpr rfl)
      U (h.value_mem hU) D (h.value_mem hD) hU hD
  limit i hi hia U hU z := by
    rw [h.limit i.toZFSet
      (Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr hia))
      ((rawLimit_code i).mpr hi) U (h.value_mem hU) hU z]
    constructor
    · rintro ⟨index, hj, T, _, hT, hz⟩
      obtain ⟨j, hji, hj⟩ := Ordinal.mem_toZFSet_iff.mp hj
      exact ⟨j, hji, T, by simpa only [Entry, hj] using hT, hz⟩
    · rintro ⟨j, hji, T, hT, hz⟩
      exact ⟨j.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr hji,
        T, h.value_mem hT, hT, hz⟩

theorem canonical_rawChecks {step : ZFSet.{u} → ZFSet.{u} → Prop}
    (a : Ordinal.{u}) {B : ZFSet.{u}}
    (hB : ∀ i ≤ a, LStageZF i ∈ B)
    (hstep : ∀ i, Order.succ i ≤ a → step (LStageZF i) (LStageZF (Order.succ i))) :
    RawChecks step (Order.succ a).toZFSet (canonicalBareHistory a) B where
  total index hi := by
    obtain ⟨i, hilt, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hi
    exact ⟨LStageZF i, hB i (Order.lt_succ_iff.mp hilt),
      pair_mem_canonicalBareHistory_iff.mpr ⟨i, Order.lt_succ_iff.mp hilt, rfl, rfl⟩⟩
  noJunk p hp := by
    obtain ⟨i, hi, he⟩ := mem_canonicalBareHistory_iff.mp hp
    exact ⟨i.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr hi),
      LStageZF i, hB i hi, he.symm⟩
  zero U _ hU := (canonical_checks a hstep).zero U (by simpa only [Entry, Ordinal.toZFSet_zero] using hU)
  successor index hi next hj hs U _ D _ hU hD := by
    obtain ⟨i, hilt, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hi
    have hn : next = (Order.succ i).toZFSet :=
      hs.trans ((ordinalToZFSet_successor_predecessor_iff i i.toZFSet).mpr rfl).symm
    rw [hn] at hj hD
    exact (canonical_checks a hstep).successor i
      (Order.lt_succ_iff.mp (Ordinal.toZFSet_mem_toZFSet_iff.mp hj)) U D hU hD
  limit index hi hl U _ hU z := by
    obtain ⟨i, hilt, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hi
    have hia := Order.lt_succ_iff.mp hilt
    rw [(canonical_checks a hstep).limit i ((rawLimit_code i).mp hl) hia U hU z]
    constructor
    · rintro ⟨j, hji, T, hT, hz⟩
      obtain ⟨k, hk, hjk, hT⟩ := pair_mem_canonicalBareHistory_iff.mp hT
      exact ⟨j.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr hji, T,
        hT.symm ▸ hB k hk, pair_mem_canonicalBareHistory_iff.mpr ⟨k, hk, hjk, hT⟩, hz⟩
    · rintro ⟨index, hj, T, _, hT, hz⟩
      obtain ⟨j, hji, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hj
      exact ⟨j, hji, T, hT, hz⟩

theorem history_field_mem_of_limit {a β : Ordinal.{u}} (hβ : Order.IsSuccLimit β)
    (ha : a < β) : pairField (canonicalBareHistory a) ∈ LStageZF β :=
  sUnion_mem_LStageZF_of_isSuccLimit hβ
    (sUnion_mem_LStageZF_of_isSuccLimit hβ (canonical_mem_of_limit hβ ha))

theorem canonical_stage_mem_field (a i : Ordinal.{u}) (hi : i ≤ a) :
    LStageZF i ∈ pairField (canonicalBareHistory a) :=
  pair_right_mem_pairField (pair_mem_canonicalBareHistory_iff.mpr ⟨i, hi, rfl, rfl⟩)

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.RawChecks.toChecks
