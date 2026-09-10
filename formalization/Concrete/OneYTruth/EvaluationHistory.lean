import OneYTruth.EvaluationStep
import OneYTruth.AtomicCodeFormula
import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity

/-!
# Bounded certificates for finite evaluation histories

Histories may have extra entries, but each entry has a standard natural
index and a correct immediate predecessor. Natural-number induction proves
that every accepted value is the actual finite iterate. A container bounds
all entry components; it is a certificate witness, not a power set.
-/

namespace OneYTruth.BoundedEvaluation

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF

universe u v

def IsSuccessor (i j : ZFSet.{u}) : Prop := j ∈ i ∧ ∀ x ∈ i, x ∈ j ∨ x = j

def successorAt {n : Nat} (i j : Fin n) : Delta0Formula n :=
  .conj (.mem j i) (.boundedAll i (.disj (.mem (Fin.last n) j.castSucc)
    (.eq (Fin.last n) j.castSucc)))

theorem satisfies_successorAt {n : Nat} (i j : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (successorAt i j) s ↔ IsSuccessor (s i) (s j) := by
  simp only [successorAt, Satisfies, satisfies_boundedAll, satisfies_disj,
    snoc_last, snoc_castSucc]
  rfl

theorem isSuccessor_natCode_iff (n m : Nat) :
    IsSuccessor (natCode n : ZFSet.{u}) (natCode m) ↔ n = m + 1 := by
  constructor
  · rintro ⟨hm, hmax⟩
    have hmn := (natCode_mem_natCode_iff m n).mp hm
    have hle : n ≤ m + 1 := by
      by_contra h
      have hs : m + 1 < n := by omega
      have hx := hmax (natCode (m + 1)) ((natCode_mem_natCode_iff (m + 1) n).mpr hs)
      rcases hx with hx | hx
      · have := (natCode_mem_natCode_iff (m + 1) m).mp hx
        omega
      · have := natCode_injective hx
        omega
    omega
  · intro h
    subst n
    refine ⟨(natCode_mem_natCode_iff m (m + 1)).mpr (by omega), ?_⟩
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (mem_natCode_iff_exists_lt x (m + 1)).mp hx
    by_cases hlt : r < m
    · exact Or.inl ((natCode_mem_natCode_iff r m).mpr hlt)
    · have : r = m := by omega
      exact Or.inr (congrArg natCode this)

def IsHistory (D : Diagram.{u}) (H B : ZFSet.{u}) : Prop :=
  ∀ p ∈ H, ∃ i ∈ B, ∃ S ∈ B, p = ZFSet.pair i S ∧ i ∈ Ordinal.omega0.toZFSet ∧
    ((i = ∅ ∧ S = ∅) ∨ ∃ j ∈ B, ∃ T ∈ B,
      ZFSet.pair j T ∈ H ∧ IsSuccessor i j ∧ S = stepSet D T)

theorem IsHistory.index_nat {D : Diagram.{u}} {H B i S : ZFSet.{u}}
    (h : IsHistory D H B) (hp : ZFSet.pair i S ∈ H) : ∃ n : Nat, i = natCode n := by
  obtain ⟨j, _, T, _, hpj, hj, _⟩ := h _ hp
  have hij := (ZFSet.pair_inj.mp hpj).1
  exact (mem_omega_iff_exists_natCode i).mp (hij.symm ▸ hj)

theorem IsHistory.value_eq_iterate {D : Diagram.{u}} {H B : ZFSet.{u}}
    (h : IsHistory D H B) (n : Nat) {S : ZFSet.{u}} (hp : ZFSet.pair (natCode n) S ∈ H) :
    S = iterate D n := by
  induction n generalizing S with
  | zero =>
    obtain ⟨i, _, T, _, heq, _, hstep⟩ := h _ hp
    obtain ⟨hi, hS⟩ := ZFSet.pair_inj.mp heq
    subst i
    subst T
    rcases hstep with ⟨_, hS⟩ | ⟨j, _, T, _, _, hj, _⟩
    · exact hS
    · have he : j ∈ (∅ : ZFSet.{u}) := by simpa [natCode] using hj.1
      exact False.elim (ZFSet.notMem_empty j he)
  | succ n ih =>
    obtain ⟨i, _, T, _, heq, _, hstep⟩ := h _ hp
    obtain ⟨hi, hS⟩ := ZFSet.pair_inj.mp heq
    subst i
    subst T
    rcases hstep with ⟨hi, _⟩ | ⟨j, _, T, _, hjT, hsucc, hS⟩
    · have hz : (natCode (n + 1) : ZFSet.{u}) = natCode 0 := by simpa [natCode] using hi
      have := natCode_injective hz
      omega
    · obtain ⟨m, rfl⟩ := h.index_nat hjT
      have hnm := (isSuccessor_natCode_iff (n + 1) m).mp hsucc
      have hm : m = n := by omega
      subst m
      rw [hS, ih hjT]
      rfl

def historyStepFormula : Delta0Formula 15 :=
  .conj (pairMemAt 8 13 14)
    (.conj (successorAt 11 13)
      (Delta0Formula.rename ![14, 0, 1, 2, 3, 4, 5, 12] stepGraphFormula))

theorem satisfies_historyStepFormula (s : Tuple ZFSet.{u} 15) :
    Satisfies ZFMem historyStepFormula s ↔
      ZFSet.pair (s 13) (s 14) ∈ s 8 ∧ IsSuccessor (s 11) (s 13) ∧
        s 12 = stepSet ⟨s 0, s 1, s 2, s 3, s 4, s 5⟩ (s 14) := by
  change (Satisfies ZFMem (pairMemAt 8 13 14) s ∧
    Satisfies ZFMem (successorAt 11 13) s ∧
    Satisfies ZFMem (Delta0Formula.rename ![14, 0, 1, 2, 3, 4, 5, 12] stepGraphFormula) s) ↔ _
  rw [satisfies_pairMemAt, satisfies_successorAt, satisfies_rename,
    satisfies_stepGraphFormula_tuple]
  rfl

attribute [irreducible] historyStepFormula

/-- Coordinates: nodes,atoms,trueAtoms,implications,quantified,children,omega,zero,H,B. -/
def historyFormula : Delta0Formula 10 :=
  .boundedAll 8 (.boundedEx 9 (.boundedEx 9
    (.conj (kuratowskiPairEqAt 10 11 12)
      (.conj (.mem 11 6)
        (.disj (.conj (.eq 11 7) (.eq 12 7))
          (.boundedEx 9 (.boundedEx 9 historyStepFormula)))))))

noncomputable def historyParameters (D : Diagram.{u}) (H B : ZFSet.{u}) : Tuple ZFSet.{u} 10 :=
  ![D.nodes, D.atoms, D.trueAtoms, D.implications, D.quantified, D.children,
    Ordinal.omega0.toZFSet, ∅, H, B]

attribute [local irreducible] kuratowskiPairEqAt

set_option maxHeartbeats 800000 in
theorem satisfies_historyFormula (D : Diagram.{u}) (H B : ZFSet.{u}) :
    Satisfies ZFMem historyFormula (historyParameters D H B) ↔ IsHistory D H B := by
  simp only [historyFormula, satisfies_historyStepFormula, satisfies_boundedAll,
    Satisfies, satisfies_kuratowskiPairEqAt, satisfies_disj]
  simp [historyParameters, constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT,
    ZFMem, IsHistory]

def mixedHistoryFormula (k : Nat) (I : Type v) := ofConstructibleDeltaZero k I historyFormula

theorem mixedHistoryFormula_isDeltaZero (k : Nat) (I : Type v) :
    IsDeltaZero (mixedHistoryFormula k I) :=
  ofConstructibleDeltaZero_isDeltaZero k I historyFormula

end OneYTruth.BoundedEvaluation
