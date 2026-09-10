import OneYTruth.ConstructibleEvaluationFamily

/-! One actual pure first-order formula recognizes eventual Tarski truth in L. -/

namespace OneYTruth.ConstructibleEvaluationFamily

open Constructible Constructible.Delta0Formula Constructible.Model
open Constructible.FiniteSequenceZF Constructible.IndexedSequenceZF BoundedEvaluation

universe u

def eventualMatrix : FOFormula 12 :=
  .imp (.disj (.mem 9 10) (.eq 9 10))
    (.imp (finiteIterationStepFormulaAt stageFormula
      (fun i : Fin 7 => i.castSucc.castSucc.castSucc.castSucc.castSucc) 10 11)
      (.mem 8 11))

theorem satisfies_eventualMatrix (s : Tuple LCarrier.{u} 12) :
    FOFormula.Satisfies lCarrierMem eventualMatrix s ↔
      ((s 9).val ∈ (s 10).val ∨ s 9 = s 10) →
        FOFormula.Satisfies lCarrierMem stageFormula
          (snoc (snoc (fun i : Fin 7 => s i.castSucc.castSucc.castSucc.castSucc.castSucc)
            (s 10)) (s 11)) → (s 8).val ∈ (s 11).val := by
  simp only [eventualMatrix, FOFormula.satisfies_imp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_finiteIterationStepFormulaAt, lCarrierMem]

attribute [irreducible] eventualMatrix

/-- Seven iteration parameters, omega, and a candidate node. -/
def eventualFormula : FOFormula 9 :=
  .ex (.conj (.mem 9 7) (.all (.imp (.mem 10 7) (.all eventualMatrix))))

theorem satisfies_eventualFormula_raw (q : Tuple LCarrier.{u} 7) (z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem eventualFormula (snoc (snoc q omegaLCarrier) z) ↔
      ∃ m : LCarrier.{u}, m.val ∈ omegaLCarrier.val ∧
        ∀ n : LCarrier.{u}, n.val ∈ omegaLCarrier.val → ∀ S : LCarrier.{u},
          (m.val ∈ n.val ∨ m = n) →
            FOFormula.Satisfies lCarrierMem stageFormula (snoc (snoc q n) S) → z.val ∈ S.val := by
  simp only [eventualFormula, FOFormula.Satisfies, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_eventualMatrix]
  simp only [constructible_snoc_eq, Fin.snoc, Fin.castLT]
  rfl

theorem satisfies_eventualFormula (D : Diagram.{u}) (hD : HasConstructibleFields D)
    (z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem eventualFormula (snoc (snoc (family D hD).params omegaLCarrier) z) ↔
      ∃ m : Nat, ∀ n : Nat, m ≤ n → z.val ∈ iterate D n := by
  rw [satisfies_eventualFormula_raw]
  constructor
  · rintro ⟨m, hm, htail⟩
    obtain ⟨a, ha⟩ := (mem_omega_iff_exists_natCode m.val).mp hm
    have hm' : m = natLCarrier a := Subtype.ext ha
    subst m
    refine ⟨a, ?_⟩
    intro b hab
    have hb : (natLCarrier b).val ∈ omegaLCarrier.val :=
      (mem_omega_iff_exists_natCode _).mpr ⟨b, rfl⟩
    have hle : (natLCarrier a).val ∈ (natLCarrier b).val ∨ natLCarrier a = natLCarrier b := by
      rcases Nat.lt_or_eq_of_le hab with h | rfl
      · exact Or.inl ((natCode_mem_natCode_iff _ _).mpr h)
      · exact Or.inr rfl
    have hz := htail (natLCarrier b) hb ((family D hD).value b) hle
      ((realizes_stageFormula D hD b _).mpr (family_value_eq D hD b))
    simpa only [family_value_eq] using hz
  · rintro ⟨a, htail⟩
    refine ⟨natLCarrier a, (mem_omega_iff_exists_natCode _).mpr ⟨a, rfl⟩, ?_⟩
    intro n hn S hle hS
    obtain ⟨b, hb⟩ := (mem_omega_iff_exists_natCode n.val).mp hn
    have hn' : n = natLCarrier b := Subtype.ext hb
    subst n
    have hab : a ≤ b := by
      rcases hle with h | h
      · exact Nat.le_of_lt ((natCode_mem_natCode_iff _ _).mp h)
      · exact Nat.le_of_eq (natCode_injective (congrArg Subtype.val h))
    have hS' := (realizes_stageFormula D hD b S).mp hS
    rw [hS']
    exact htail b hab

end OneYTruth.ConstructibleEvaluationFamily
