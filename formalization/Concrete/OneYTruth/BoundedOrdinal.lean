import OneYTruth.SchemaBundle

/-! Actual bounded syntax for ordinal and nonzero limit requirements. -/

namespace OneYTruth.BoundedOrdinal

open Constructible Constructible.Delta0Formula

universe u v

def transitiveAt {n : Nat} (a : Fin n) : Delta0Formula n :=
  .boundedAll a (.boundedAll (Fin.last n) (.mem (Fin.last (n + 1)) a.castSucc.castSucc))

theorem satisfies_transitiveAt {n : Nat} (a : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (transitiveAt a) s ↔ (s a).IsTransitive := by
  simp only [transitiveAt, satisfies_boundedAll, Satisfies, snoc_last, snoc_castSucc]
  rfl

def ordinalAt {n : Nat} (a : Fin n) : Delta0Formula n :=
  .conj (transitiveAt a) (.boundedAll a (transitiveAt (Fin.last n)))

theorem satisfies_ordinalAt {n : Nat} (a : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (ordinalAt a) s ↔ (s a).IsOrdinal := by
  simp only [ordinalAt, Satisfies, satisfies_transitiveAt, satisfies_boundedAll, snoc_last]
  exact ZFSet.isOrdinal_iff_forall_mem_isTransitive.symm

def noLastAt {n : Nat} (a : Fin n) : Delta0Formula n :=
  .boundedAll a (.boundedEx a.castSucc (.mem (Fin.last n).castSucc (Fin.last (n + 1))))

theorem satisfies_noLastAt {n : Nat} (a : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (noLastAt a) s ↔ ∀ x ∈ s a, ∃ y ∈ s a, x ∈ y := by
  simp only [noLastAt, satisfies_boundedAll, Satisfies, snoc_last, snoc_castSucc]

theorem noLast_ordinal_iff (a : Ordinal.{u}) :
    (∀ x ∈ a.toZFSet, ∃ y ∈ a.toZFSet, x ∈ y) ↔ Order.IsSuccPrelimit a := by
  rw [Order.isSuccPrelimit_iff_succ_lt]
  constructor
  · intro h b hb
    obtain ⟨y, hy, hby⟩ := h b.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hb)
    obtain ⟨c, hca, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
    exact (Order.succ_le_iff.mpr (Ordinal.toZFSet_mem_toZFSet_iff.mp hby)).trans_lt hca
  · intro h x hx
    obtain ⟨b, hba, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    exact ⟨(Order.succ b).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (h b hba),
      Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ b)⟩

/-- Coordinates are the actual omega code and the candidate ordinal code. -/
def aboveOmegaLimitFormula : Delta0Formula 2 :=
  .conj (ordinalAt 1) (.conj (.mem 0 1) (noLastAt 1))

theorem satisfies_aboveOmegaLimitFormula (a : Ordinal.{u}) :
    Satisfies ZFMem aboveOmegaLimitFormula ![Ordinal.omega0.toZFSet, a.toZFSet] ↔
      Ordinal.omega0 < a ∧ Order.IsSuccLimit a := by
  simp only [aboveOmegaLimitFormula, Satisfies, satisfies_ordinalAt, satisfies_noLastAt]
  change (a.toZFSet.IsOrdinal ∧ Ordinal.omega0.toZFSet ∈ a.toZFSet ∧
    (∀ x ∈ a.toZFSet, ∃ y ∈ a.toZFSet, x ∈ y)) ↔ _
  rw [noLast_ordinal_iff, Ordinal.toZFSet_mem_toZFSet_iff]
  simp only [ZFSet.isOrdinal_toZFSet, true_and, Ordinal.isSuccLimit_iff]
  constructor
  · rintro ⟨hω, h⟩
    exact ⟨hω, ne_of_gt (Ordinal.omega0_pos.trans hω), h⟩
  · rintro ⟨hω, _, h⟩
    exact ⟨hω, h⟩

theorem satisfies_aboveOmegaLimitFormula_iff_exists (x : ZFSet.{u}) :
    Satisfies ZFMem aboveOmegaLimitFormula ![Ordinal.omega0.toZFSet, x] ↔
      ∃ a : Ordinal.{u}, a.toZFSet = x ∧ Ordinal.omega0 < a ∧ Order.IsSuccLimit a := by
  constructor
  · intro h
    have hx : x.IsOrdinal := (satisfies_ordinalAt 1 ![Ordinal.omega0.toZFSet, x]).mp h.1
    obtain ⟨a, rfl⟩ := ZFSet.isOrdinal_iff_mem_range_toZFSet.mp hx
    exact ⟨a, rfl, (satisfies_aboveOmegaLimitFormula a).mp h⟩
  · rintro ⟨a, rfl, h⟩
    exact (satisfies_aboveOmegaLimitFormula a).mpr h

end OneYTruth.BoundedOrdinal
