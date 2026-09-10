import OneYTruth.InternalEvaluationFamily

/-! # Bounded certificates for an arbitrary displayed deterministic iteration

The history predicate is parameterized by an actual bounded step graph.
The canonical finite witnesses and their uniqueness are proved here; no
iteration-history or range-existence field is assumed.
-/

namespace OneYTruth.InternalIteration

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.IndexedSequenceZF InternalProducts InternalClosure

universe u v

noncomputable def iterate (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => initial
  | n + 1 => step (iterate step initial n)

def IsHistory (step : ZFSet.{u} → ZFSet.{u}) (initial H B : ZFSet.{u}) : Prop :=
  ∀ p ∈ H, ∃ i ∈ B, ∃ S ∈ B, p = ZFSet.pair i S ∧ i ∈ Ordinal.omega0.toZFSet ∧
    ((i = ∅ ∧ S = initial) ∨ ∃ j ∈ B, ∃ T ∈ B,
      ZFSet.pair j T ∈ H ∧ BoundedEvaluation.IsSuccessor i j ∧ S = step T)

theorem IsHistory.index_nat {step : ZFSet.{u} → ZFSet.{u}} {initial H B i S : ZFSet.{u}}
    (h : IsHistory step initial H B) (hp : ZFSet.pair i S ∈ H) : ∃ n : Nat, i = natCode n := by
  obtain ⟨j, _, T, _, hpj, hj, _⟩ := h _ hp
  have hij := (ZFSet.pair_inj.mp hpj).1
  exact (mem_omega_iff_exists_natCode i).mp (hij.symm ▸ hj)

theorem IsHistory.value_eq_iterate {step : ZFSet.{u} → ZFSet.{u}} {initial H B : ZFSet.{u}}
    (h : IsHistory step initial H B) (n : Nat) {S : ZFSet.{u}}
    (hp : ZFSet.pair (natCode n) S ∈ H) : S = iterate step initial n := by
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
        have hnm := (BoundedEvaluation.isSuccessor_natCode_iff (n + 1) m).mp hsucc
        have hm : m = n := by omega
        subst m
        rw [hS, ih hjT]
        rfl

noncomputable def finiteHistory (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u})
    (n : Nat) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n + 1) => ZFSet.pair (natCode i.val) (iterate step initial i.val))

noncomputable def historyContainer (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u})
    (n : Nat) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n + 1) => natCode i.val) ∪
    ZFSet.range (fun i : Fin (n + 1) => iterate step initial i.val)

theorem finiteHistory_isHistory (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) (n : Nat) :
    IsHistory step initial (finiteHistory step initial n) (historyContainer step initial n) := by
  have hi (i : Fin (n+1)) : natCode i.val ∈ historyContainer step initial n :=
    ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_range_self
      (f := fun j : Fin (n+1) => (natCode j.val : ZFSet.{u})) i))
  have hv (i : Fin (n+1)) : iterate step initial i.val ∈ historyContainer step initial n :=
    ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_range_self
      (f := fun j : Fin (n+1) => iterate step initial j.val) i))
  intro p hp
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
  refine ⟨natCode i.val, hi i, iterate step initial i.val, hv i, rfl,
    (mem_omega_iff_exists_natCode _).mpr ⟨i.val, rfl⟩, ?_⟩
  cases he : i.val with
  | zero => exact Or.inl ⟨by simp [natCode], rfl⟩
  | succ m =>
      have hm : m < n+1 := by have := i.isLt; omega
      exact Or.inr ⟨natCode m, hi ⟨m, hm⟩, iterate step initial m, hv ⟨m, hm⟩,
        ZFSet.mem_range_self (f := fun j : Fin (n+1) =>
          ZFSet.pair (natCode j.val) (iterate step initial j.val)) ⟨m, hm⟩,
        (BoundedEvaluation.isSuccessor_natCode_iff (m+1) m).mpr rfl, rfl⟩

theorem last_mem_finiteHistory (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u}) (n : Nat) :
    ZFSet.pair (natCode n) (iterate step initial n) ∈ finiteHistory step initial n :=
  ZFSet.mem_range_self (f := fun i : Fin (n+1) =>
    ZFSet.pair (natCode i.val) (iterate step initial i.val)) (Fin.last n)

theorem finite_witnesses_mem {V : ZFSet.{u}} (hV : V.IsTransitive)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hNat : ∀ n : Nat, (natCode n : ZFSet.{u}) ∈ V)
    (step : ZFSet.{u} → ZFSet.{u}) (initial : ZFSet.{u})
    (hIter : ∀ n, iterate step initial n ∈ V) (n : Nat) :
    finiteHistory step initial n ∈ V ∧ historyContainer step initial n ∈ V := by
  exact ⟨finiteRange_mem hV hpair hUnion hempty _
      (fun i => hpair _ (hNat i.val) _ (hIter i.val)),
    binaryUnion_mem hV hpair hUnion
      (finiteRange_mem hV hpair hUnion hempty _ (fun i => hNat i.val))
      (finiteRange_mem hV hpair hUnion hempty _ (fun i => hIter i.val))⟩

def stepAt {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (current next : Fin n) : Delta0Formula n :=
  φ.rename (Fin.lastCases next (Fin.lastCases current params))

theorem satisfies_stepAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (current next : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (stepAt φ params current next) s ↔
      Satisfies ZFMem φ (snoc (snoc (fun i => s (params i)) (s current)) (s next)) := by
  rw [stepAt, satisfies_rename]
  have he : (fun i => s (Fin.lastCases next (Fin.lastCases current params) i)) =
      snoc (snoc (fun i => s (params i)) (s current)) (s next) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
  rw [he]

def predecessorAt {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (H B i S : Fin n) : Delta0Formula n :=
  .boundedEx B (.boundedEx B.castSucc
    (.conj (BoundedEvaluation.pairMemAt H.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))
      (.conj (BoundedEvaluation.successorAt i.castSucc.castSucc (Fin.last n).castSucc)
        (stepAt φ (fun j => (params j).castSucc.castSucc) (Fin.last (n+1)) S.castSucc.castSucc))))

theorem satisfies_predecessorAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (H B i S : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (predecessorAt φ params H B i S) s ↔
      ∃ j ∈ s B, ∃ T ∈ s B, ZFSet.pair j T ∈ s H ∧ BoundedEvaluation.IsSuccessor (s i) j ∧
        Satisfies ZFMem φ (snoc (snoc (fun a => s (params a)) T) (s S)) := by
  simp only [predecessorAt, Satisfies, BoundedEvaluation.satisfies_pairMemAt,
    BoundedEvaluation.satisfies_successorAt, satisfies_stepAt, snoc_last, snoc_castSucc]

attribute [irreducible] predecessorAt

def historyAt {p n : Nat} (φ : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (initial omega zero H B : Fin n) : Delta0Formula n :=
  .boundedAll H (.boundedEx B.castSucc (.boundedEx B.castSucc.castSucc
    (.conj (kuratowskiPairEqAt (Fin.last n).castSucc.castSucc
        (Fin.last (n+1)).castSucc (Fin.last (n+2)))
      (.conj (.mem (Fin.last (n+1)).castSucc omega.castSucc.castSucc.castSucc)
        (.disj (.conj (.eq (Fin.last (n+1)).castSucc zero.castSucc.castSucc.castSucc)
          (.eq (Fin.last (n+2)) initial.castSucc.castSucc.castSucc))
          (predecessorAt φ (fun j => (params j).castSucc.castSucc.castSucc)
            H.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc
            (Fin.last (n+1)).castSucc (Fin.last (n+2))))))))

theorem satisfies_historyAt {p n : Nat} (φ : Delta0Formula (p+2))
    (params : Fin p → Fin n) (initial omega zero H B : Fin n) (s : Tuple ZFSet.{u} n)
    (hOmega : s omega = Ordinal.omega0.toZFSet) (hZero : s zero = ∅)
    (step : ZFSet.{u} → ZFSet.{u})
    (hStep : ∀ S T, Satisfies ZFMem φ (snoc (snoc (fun a => s (params a)) S) T) ↔ T = step S) :
    Satisfies ZFMem (historyAt φ params initial omega zero H B) s ↔
      IsHistory step (s initial) (s H) (s B) := by
  simp only [historyAt, satisfies_boundedAll, Satisfies, satisfies_kuratowskiPairEqAt,
    satisfies_disj, satisfies_predecessorAt, snoc_last, snoc_castSucc, hOmega, hZero, hStep]
  rfl

end OneYTruth.InternalIteration

#print axioms OneYTruth.InternalIteration.IsHistory.value_eq_iterate
#print axioms OneYTruth.InternalIteration.satisfies_historyAt
