import OneYTruth.ConstructibleAssignmentCodes

/-!
# A constructible universe containing every finite syntax code

This is an actual set in L, closed under ordered pairs and containing zero,
all natural codes, and the specified alphabet. It provides a single bound
for a later internal grammar construction; containment is not confused with
constructibility of an arbitrary subset of the bound.
-/

namespace OneYTruth.ConstructibleCodeUniverse

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel FormulaCode InternalNodes

universe u v

def pairStep (A : ZFSet.{u}) : ZFSet.{u} := insert ∅ (A ∪ F2 A A)

theorem pairStep_mem_L {A : ZFSet.{u}} (hA : A ∈ L) : pairStep A ∈ L := by
  rw [pairStep, ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L empty_mem_L) (union_mem_L hA (op_mem_L (i := 2) hA hA))

/-- Coordinates zero,current,next. -/
def pairStepFormula : Delta0Formula 3 :=
  .conj (.mem 0 2)
    (.conj (.boundedAll 2 (.disj (.eq 3 0) (.disj (.mem 3 1)
      (.boundedEx 1 (.boundedEx 1 (kuratowskiPairEqAt 3 4 5))))))
      (.conj (.boundedAll 1 (.mem 3 2))
        (.boundedAll 1 (.boundedAll 1 (.boundedEx 2 (kuratowskiPairEqAt 5 3 4))))))

theorem satisfies_pairStepFormula (Z A T : ZFSet.{u}) :
    Satisfies ZFMem pairStepFormula ![Z, A, T] ↔ T = insert Z (A ∪ F2 A A) := by
  simp only [pairStepFormula, Satisfies, satisfies_boundedAll, satisfies_disj,
    satisfies_kuratowskiPairEqAt]
  change (Z ∈ T ∧ (∀ p ∈ T, p = Z ∨ p ∈ A ∨ ∃ a ∈ A, ∃ b ∈ A, p = ZFSet.pair a b) ∧
    (∀ p ∈ A, p ∈ T) ∧ ∀ a ∈ A, ∀ b ∈ A, ∃ p ∈ T, p = ZFSet.pair a b) ↔
      T = insert Z (A ∪ F2 A A)
  constructor
  · rintro ⟨hZ, hout, hA, hin⟩
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_insert_iff, ZFSet.mem_union, mem_F2_iff]
    constructor
    · exact hout p
    · rintro (rfl | hp | ⟨a, ha, b, hb, hp⟩)
      · exact hZ
      · exact hA p hp
      · obtain ⟨q, hq, hqab⟩ := hin a ha b hb
        exact (hqab.trans hp.symm) ▸ hq
  · rintro rfl
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro p hp
      simpa only [ZFSet.mem_insert_iff, ZFSet.mem_union, mem_F2_iff] using hp
    · intro p hp
      exact ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl hp)))
    · intro a ha b hb
      exact ⟨ZFSet.pair a b, ZFSet.mem_insert_iff.mpr (Or.inr
        (ZFSet.mem_union.mpr (Or.inr (mem_F2_iff.mpr ⟨a, ha, b, hb, rfl⟩)))), rfl⟩

noncomputable def pairStepL (A : LCarrier.{u}) : LCarrier.{u} :=
  ⟨pairStep A.val, pairStep_mem_L A.property⟩

theorem pairStep_defines :
    DefinesFiniteIterationStep pairStepFormula.toFO ![emptyLCarrier.{u}] pairStepL := by
  intro A T
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute, Delta0Formula.satisfies_toFO]
  have hp : (fun i => (snoc (snoc ![emptyLCarrier] A) T i).val) = ![∅, A.val, T.val] := by
    funext i
    fin_cases i <;> rfl
  rw [hp, satisfies_pairStepFormula]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

noncomputable def seed (A : LCarrier.{u}) : LCarrier.{u} :=
  ⟨A.val ∪ omegaLCarrier.val, union_mem_L A.property omegaLCarrier.property⟩

noncomputable def stages (A : LCarrier.{u}) : Nat → LCarrier.{u} :=
  uniformFiniteIterate pairStepL (seed A)

theorem stages_subset_succ (A : LCarrier.{u}) (n : Nat) :
    (stages A n).val ⊆ (stages A (n + 1)).val := by
  intro p hp
  exact ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl hp)))

theorem stages_mono (A : LCarrier.{u}) {n m : Nat} (h : n ≤ m) :
    (stages A n).val ⊆ (stages A m).val := by
  induction h with
  | refl => exact fun _ h => h
  | @step m h ih => exact fun p hp => stages_subset_succ A m (ih hp)

noncomputable def family (A : LCarrier.{u}) : ParametricUniformOmegaFamilySpec.{u} 2 :=
  uniformFiniteIterationOmegaFamilySpec pairStepFormula.toFO ![emptyLCarrier]
    pairStepL (seed A) pairStep_defines

noncomputable def codeUniverse (A : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion (family A)

theorem mem_codeUniverse_iff (A : LCarrier.{u}) (p : ZFSet.{u}) :
    p ∈ (codeUniverse A).val ↔ ∃ n, p ∈ (stages A n).val := by
  constructor
  · intro hp
    exact (mem_parametricUniformOmegaUnion_iff (family A)
      ⟨p, mem_L_of_mem hp (codeUniverse A).property⟩).mp hp
  · rintro ⟨n, hn⟩
    exact (mem_parametricUniformOmegaUnion_iff (family A)
      ⟨p, mem_L_of_mem hn (stages A n).property⟩).mpr ⟨n, hn⟩

theorem alphabet_mem {A : LCarrier.{u}} {p : ZFSet.{u}} (hp : p ∈ A.val) :
    p ∈ (codeUniverse A).val := by
  apply (mem_codeUniverse_iff A p).mpr
  exact ⟨0, ZFSet.mem_union.mpr (Or.inl hp)⟩

theorem natCode_mem (A : LCarrier.{u}) (n : Nat) : natCode n ∈ (codeUniverse A).val := by
  apply (mem_codeUniverse_iff A _).mpr
  exact ⟨0, ZFSet.mem_union.mpr (Or.inr
    ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩))⟩

theorem empty_mem (A : LCarrier.{u}) : ∅ ∈ (codeUniverse A).val := by
  apply (mem_codeUniverse_iff A _).mpr
  exact ⟨1, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩

theorem pair_mem {A : LCarrier.{u}} {p q : ZFSet.{u}}
    (hp : p ∈ (codeUniverse A).val) (hq : q ∈ (codeUniverse A).val) :
    ZFSet.pair p q ∈ (codeUniverse A).val := by
  obtain ⟨n, hn⟩ := (mem_codeUniverse_iff A p).mp hp
  obtain ⟨m, hm⟩ := (mem_codeUniverse_iff A q).mp hq
  apply (mem_codeUniverse_iff A _).mpr
  refine ⟨max n m + 1, ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr ?_)))⟩
  exact mem_F2_iff.mpr ⟨p, stages_mono A (Nat.le_max_left n m) hn,
    q, stages_mono A (Nat.le_max_right n m) hm, rfl⟩

theorem listCode_mem {A : LCarrier.{u}} {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ (codeUniverse A).val) : listCode xs ∈ (codeUniverse A).val := by
  induction xs with
  | nil => exact empty_mem A
  | cons x xs ih => exact pair_mem (hxs x (by simp)) (ih (fun y hy => hxs y (by simp [hy])))

theorem sequenceCode_mem {A : LCarrier.{u}} {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ (codeUniverse A).val) : sequenceCode xs ∈ (codeUniverse A).val :=
  pair_mem (natCode_mem A xs.length) (listCode_mem hxs)

theorem rawCode_mem {A : LCarrier.{u}} {I : Type v} {indexCode : I → ZFSet.{u}}
    (hi : ∀ i, indexCode i ∈ A.val) (φ : Raw I) : rawCode indexCode φ ∈ (codeUniverse A).val := by
  induction φ <;> simp only [rawCode] <;> apply sequenceCode_mem <;>
    simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp, false_implies,
      forall_const, natCode_mem, alphabet_mem, and_true]

theorem syntaxCodes_subset {A : LCarrier.{u}} {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (hi : ∀ i, indexCode i ∈ A.val) :
    syntaxCodes (k := k) indexCode ⊆ (codeUniverse A).val := by
  intro p hp
  obtain ⟨⟨n, φ⟩, rfl⟩ := ZFSet.mem_range.mp hp
  exact pair_mem (natCode_mem A n) (rawCode_mem hi (toRaw φ))

end OneYTruth.ConstructibleCodeUniverse
