import OneYTruth.InternalIterationFamily

/-! # A bounded certificate that a candidate is the entire genuine iterate family

A single history covers every natural index. Its bounded clauses certify
both inclusions between its range and the candidate family. Completeness
is checked explicitly, independently of whether the candidate is internal.
-/

namespace OneYTruth.InternalIteration

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF

universe u

noncomputable def fullHistory (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n : Nat => ZFSet.pair (natCode n) (iterate step initial n))

def IsFamilyCertificate (step : ZFSet.{u} → ZFSet.{u}) (initial F H B : ZFSet.{u}) : Prop :=
  IsHistory step initial H B ∧
    (∀ i ∈ Ordinal.omega0.toZFSet, ∃ S ∈ F, ZFSet.pair i S ∈ H) ∧
    (∀ S ∈ F, ∃ i ∈ Ordinal.omega0.toZFSet, ZFSet.pair i S ∈ H)

theorem IsFamilyCertificate.family_eq {step : ZFSet.{u} → ZFSet.{u}}
    {initial F H B : ZFSet.{u}} (h : IsFamilyCertificate step initial F H B) : F = family step initial := by
  apply ZFSet.ext
  intro S
  constructor
  · intro hS
    obtain ⟨i, hi, hpair⟩ := h.2.2 S hS
    obtain ⟨n, rfl⟩ := (mem_omega_iff_exists_natCode i).mp hi
    exact ZFSet.mem_range.mpr ⟨n, (h.1.value_eq_iterate n hpair).symm⟩
  · intro hS
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hS
    obtain ⟨S, hS, hn⟩ := h.2.1 (natCode n) ((mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩)
    exact (h.1.value_eq_iterate n hn) ▸ hS

theorem fullHistory_isHistory (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) :
    IsHistory step initial (fullHistory step initial) (Ordinal.omega0.toZFSet ∪ family step initial) := by
  have hi (n : Nat) : (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet ∪ family step initial :=
    ZFSet.mem_union.mpr (Or.inl ((mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩))
  have hv (n : Nat) : iterate step initial n ∈ Ordinal.omega0.toZFSet ∪ family step initial :=
    ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_range_self (f := iterate step initial) n))
  intro p hp
  obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
  refine ⟨natCode n, hi n, iterate step initial n, hv n, rfl,
    (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩, ?_⟩
  cases n with
  | zero => exact Or.inl ⟨by simp [natCode], rfl⟩
  | succ n => exact Or.inr ⟨natCode n, hi n, iterate step initial n, hv n,
      ZFSet.mem_range_self (f := fun j => ZFSet.pair (natCode j) (iterate step initial j)) n,
      (BoundedEvaluation.isSuccessor_natCode_iff (n+1) n).mpr rfl, rfl⟩

theorem fullHistory_isFamilyCertificate (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) :
    IsFamilyCertificate step initial (family step initial) (fullHistory step initial)
      (Ordinal.omega0.toZFSet ∪ family step initial) := by
  refine ⟨fullHistory_isHistory step initial, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, rfl⟩ := (mem_omega_iff_exists_natCode i).mp hi
    exact ⟨iterate step initial n, ZFSet.mem_range_self (f := iterate step initial) n,
      ZFSet.mem_range_self (f := fun j => ZFSet.pair (natCode j) (iterate step initial j)) n⟩
  · intro S hS
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hS
    exact ⟨natCode n, (mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩,
      ZFSet.mem_range_self (f := fun j => ZFSet.pair (natCode j) (iterate step initial j)) n⟩

def familyCertificateAt {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (initial omega zero F H B : Fin n) : Delta0Formula n :=
  .conj (historyAt φ params initial omega zero H B)
    (.conj (.boundedAll omega (.boundedEx F.castSucc
      (BoundedEvaluation.pairMemAt H.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))))
      (.boundedAll F (.boundedEx omega.castSucc
        (BoundedEvaluation.pairMemAt H.castSucc.castSucc (Fin.last (n+1)) (Fin.last n).castSucc))))

theorem satisfies_familyCertificateAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero F H B : Fin n)
    (s : Tuple ZFSet.{u} n) (hOmega : s omega = Ordinal.omega0.toZFSet) (hZero : s zero = ∅)
    (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun a => s (params a)) S) T) ↔ T = step S) :
    Satisfies ZFMem (familyCertificateAt φ params initial omega zero F H B) s ↔
      IsFamilyCertificate step (s initial) (s F) (s H) (s B) := by
  change (Satisfies ZFMem (historyAt φ _ _ _ _ _ _) _ ∧ _) ↔ _
  rw [satisfies_historyAt _ _ _ _ _ _ _ _ hOmega hZero step hStep]
  simp only [Satisfies, satisfies_boundedAll, BoundedEvaluation.satisfies_pairMemAt,
    snoc_last, snoc_castSucc, hOmega]
  rfl

end OneYTruth.InternalIteration

#print axioms OneYTruth.InternalIteration.IsFamilyCertificate.family_eq
#print axioms OneYTruth.InternalIteration.satisfies_familyCertificateAt
