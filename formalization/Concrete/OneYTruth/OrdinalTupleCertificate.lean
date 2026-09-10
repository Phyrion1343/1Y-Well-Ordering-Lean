import OneYTruth.BoundedOrdinal

/-! A literal finite bounded check for an increasing ordinal tuple.
This is the order component of the still-to-be-assembled diagram matrix. -/

namespace OneYTruth.OrdinalTupleCertificate

open Constructible Constructible.Delta0Formula BoundedOrdinal

universe u v

def conjunction {n : Nat} (anchor : Fin n) : List (Delta0Formula n) → Delta0Formula n
  | [] => .eq anchor anchor
  | φ :: Γ => .conj φ (conjunction anchor Γ)

theorem satisfies_conjunction {n : Nat} (anchor : Fin n) (Γ : List (Delta0Formula n)) (p : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (conjunction anchor Γ) p ↔ ∀ φ ∈ Γ, Satisfies ZFMem φ p := by
  induction Γ with
  | nil => simp [conjunction, Satisfies]
  | cons φ Γ ih => simp only [conjunction, Satisfies, ih, List.forall_mem_cons]

def finiteAll {n m : Nat} (anchor : Fin n) (f : Fin m → Delta0Formula n) : Delta0Formula n := conjunction anchor (List.ofFn f)

theorem satisfies_finiteAll {n m : Nat} (anchor : Fin n) (f : Fin m → Delta0Formula n) (p : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (finiteAll anchor f) p ↔ ∀ i, Satisfies ZFMem (f i) p := by
  simp [finiteAll, satisfies_conjunction, List.mem_ofFn]

def formula (n : Nat) : Delta0Formula (n+1) :=
  finiteAll (Fin.last n) (fun i : Fin n => .conj (ordinalAt i.castSucc)
    (finiteAll (Fin.last n) (fun j : Fin n => if i < j then .mem i.castSucc j.castSucc
      else .eq (Fin.last n) (Fin.last n))))

theorem satisfies_formula (n : Nat) (p : Tuple ZFSet.{u} (n+1)) :
    Satisfies ZFMem (formula n) p ↔
      (∀ i : Fin n, (p i.castSucc).IsOrdinal) ∧
        ∀ i j : Fin n, i < j → p i.castSucc ∈ p j.castSucc := by
  simp only [formula, satisfies_finiteAll, Satisfies, satisfies_ordinalAt]
  constructor
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    intro i j hij
    have hh := (h i).2 j
    simpa [hij, Satisfies] using hh
  · rintro ⟨ho, hl⟩ i
    refine ⟨ho i, ?_⟩
    intro j
    by_cases hij : i < j
    · simpa [hij, Satisfies] using hl i j hij
    · simp [hij, Satisfies]

theorem satisfies_formula_iff_codes (n : Nat) (p : Tuple ZFSet.{u} (n+1)) :
    Satisfies ZFMem (formula n) p ↔
      ∃ f : Fin n → Ordinal.{u}, (∀ i, (f i).toZFSet = p i.castSucc) ∧ StrictMono f := by
  rw [satisfies_formula]
  constructor
  · rintro ⟨ho, hl⟩
    have hex (i : Fin n) : ∃ a : Ordinal.{u}, a.toZFSet = p i.castSucc :=
      ZFSet.isOrdinal_iff_mem_range_toZFSet.mp (ho i)
    choose f hf using hex
    refine ⟨f, hf, ?_⟩
    intro i j hij
    apply Ordinal.toZFSet_mem_toZFSet_iff.mp
    rw [hf i, hf j]
    exact hl i j hij
  · rintro ⟨f, hf, hm⟩
    refine ⟨fun i => hf i ▸ ZFSet.isOrdinal_toZFSet (f i), ?_⟩
    intro i j hij
    rw [← hf i, ← hf j]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hm hij)

def mixedFormula (k : Nat) (I : Type v) (n : Nat) := ofConstructibleDeltaZero k I (formula n)

theorem mixedFormula_isDeltaZero (k : Nat) (I : Type v) (n : Nat) :
    IsDeltaZero (mixedFormula k I n) := ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_in_stage {k : Nat} {I : Type v} {β : Ordinal.{u}} {n : Nat}
    (N : Interpretation k I (ZFCarrier (LStageZF β))) (hmem : N.mem = zfCarrierMem (LStageZF β))
    (p : Fin (n+1) → ZFCarrier (LStageZF β)) :
    realize N (mixedFormula k I n) Empty.elim p ↔
      ∃ f : Fin n → Ordinal.{u}, (∀ i, (f i).toZFSet = (p i.castSucc).val) ∧
        StrictMono f ∧ ∀ i, f i < β := by
  rw [mixedFormula, realize_ofConstructibleDeltaZero_absolute (LStageZF_isTransitive β) N hmem]
  rw [satisfies_formula_iff_codes]
  constructor
  · rintro ⟨f, hf, hm⟩
    refine ⟨f, hf, hm, ?_⟩
    intro i
    apply MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
    rw [hf i]
    exact (p i.castSucc).property
  · rintro ⟨f, hf, hm, _⟩
    exact ⟨f, hf, hm⟩

end OneYTruth.OrdinalTupleCertificate
