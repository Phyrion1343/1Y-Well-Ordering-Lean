import OneYTruth.InternalSatisfactionSources
import ConstructibleUniverse.SetTheory.ZFC.Constructible.UniformFiniteIterationFormula
import Mathlib.Logic.Small.List

/-!
# The complete set of finite structural list codes is constructible

The actual operation A ↦ {empty} ∪ (U × A) has a displayed bounded graph
formula. The library's proved uniform finite-iteration construction supplies
the whole omega family in L, and its union is identified with all genuine
finite list payloads. No arbitrary external countable image is assumed to
be constructible.
-/

namespace OneYTruth.ConstructibleListCodes

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel

universe u

def listStep (U A : ZFSet.{u}) : ZFSet.{u} := insert ∅ (F2 U A)

theorem listStep_mem_L {U A : ZFSet.{u}} (hU : U ∈ L) (hA : A ∈ L) : listStep U A ∈ L := by
  rw [listStep, ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L empty_mem_L) (op_mem_L (i := 2) hU hA)

/-- Coordinates U,zero,current,next. -/
def listStepFormula : Delta0Formula 4 :=
  .conj (.mem 1 3)
    (.conj (.boundedAll 3 (.disj (.eq 4 1)
      (.boundedEx 0 (.boundedEx 2 (kuratowskiPairEqAt 4 5 6)))))
      (.boundedAll 0 (.boundedAll 2 (.boundedEx 3 (kuratowskiPairEqAt 6 4 5)))))

theorem satisfies_listStepFormula (U Z A T : ZFSet.{u}) :
    Satisfies ZFMem listStepFormula ![U, Z, A, T] ↔ T = insert Z (F2 U A) := by
  simp only [listStepFormula, Satisfies, satisfies_boundedAll, satisfies_disj,
    satisfies_kuratowskiPairEqAt]
  change (Z ∈ T ∧ (∀ p ∈ T, p = Z ∨ ∃ a ∈ U, ∃ b ∈ A, p = ZFSet.pair a b) ∧
    ∀ a ∈ U, ∀ b ∈ A, ∃ p ∈ T, p = ZFSet.pair a b) ↔ T = insert Z (F2 U A)
  constructor
  · rintro ⟨hZ, hout, hin⟩
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_insert_iff, mem_F2_iff]
    constructor
    · exact hout p
    · rintro (rfl | ⟨a, ha, b, hb, hp⟩)
      · exact hZ
      · obtain ⟨q, hq, hqab⟩ := hin a ha b hb
        exact (hqab.trans hp.symm) ▸ hq
  · intro h
    subst T
    refine ⟨by simp, ?_, ?_⟩
    · intro p hp
      exact (ZFSet.mem_insert_iff.mp hp).imp_right (fun hp => mem_F2_iff.mp hp)
    · intro a ha b hb
      exact ⟨ZFSet.pair a b, ZFSet.mem_insert_iff.mpr
        (Or.inr (mem_F2_iff.mpr ⟨a, ha, b, hb, rfl⟩)), rfl⟩

noncomputable def listStepL (U A : LCarrier.{u}) : LCarrier.{u} :=
  ⟨listStep U.val A.val, listStep_mem_L U.property A.property⟩

theorem listStep_defines (U : LCarrier.{u}) :
    DefinesFiniteIterationStep listStepFormula.toFO ![U, emptyLCarrier] (listStepL U) := by
  intro A T
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute, Delta0Formula.satisfies_toFO]
  have hp : (fun i => (Constructible.snoc (Constructible.snoc ![U, emptyLCarrier] A) T i).val) =
      ![U.val, ∅, A.val, T.val] := by
    funext i
    fin_cases i <;> rfl
  rw [hp, satisfies_listStepFormula]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

noncomputable def listStages (U : LCarrier.{u}) : Nat → LCarrier.{u} :=
  uniformFiniteIterate (listStepL U) emptyLCarrier

theorem mem_listStages_iff (U : LCarrier.{u}) (n : Nat) (p : ZFSet.{u}) :
    p ∈ (listStages U n).val ↔
      ∃ xs : List (ZFCarrier U.val), xs.length < n ∧ p = listCode (xs.map Subtype.val) := by
  induction n generalizing p with
  | zero => simp [listStages, uniformFiniteIterate, emptyLCarrier]
  | succ n ih =>
    change p ∈ insert ∅ (F2 U.val (listStages U n).val) ↔ _
    rw [ZFSet.mem_insert_iff, mem_F2_iff]
    constructor
    · rintro (hp | ⟨a, ha, b, hb, hp⟩)
      · exact ⟨[], by simp, hp⟩
      · obtain ⟨xs, hx, hb⟩ := (ih b).mp hb
        refine ⟨⟨a, ha⟩ :: xs, by simp; omega, ?_⟩
        simpa only [List.map_cons, listCode_cons, hb] using hp
    · rintro ⟨xs, hx, hp⟩
      cases xs with
      | nil => exact Or.inl hp
      | cons a xs =>
        refine Or.inr ⟨a.val, a.property, listCode (xs.map Subtype.val),
          (ih _).mpr ⟨xs, by simpa using hx, rfl⟩, ?_⟩
        exact hp

noncomputable def listFamilySpec (U : LCarrier.{u}) : ParametricUniformOmegaFamilySpec.{u} 3 :=
  uniformFiniteIterationOmegaFamilySpec listStepFormula.toFO ![U, emptyLCarrier]
    (listStepL U) emptyLCarrier (listStep_defines U)

noncomputable def internalListCodes (U : LCarrier.{u}) : LCarrier.{u} :=
  parametricUniformOmegaUnion (listFamilySpec U)

noncomputable def listCodes (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun xs : List (ZFCarrier U) => listCode (xs.map Subtype.val))

theorem internalListCodes_eq (U : LCarrier.{u}) : (internalListCodes U).val = listCodes U.val := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    have hpL := mem_L_of_mem hp (internalListCodes U).property
    obtain ⟨n, hn⟩ := (mem_parametricUniformOmegaUnion_iff (listFamilySpec U) ⟨p, hpL⟩).mp hp
    obtain ⟨xs, _, hxs⟩ := (mem_listStages_iff U n p).mp hn
    exact ZFSet.mem_range.mpr ⟨xs, hxs.symm⟩
  · intro hp
    obtain ⟨xs, hxs⟩ := ZFSet.mem_range.mp hp
    have hpL : p ∈ L := by
      rw [← hxs]
      apply listCode_mem_L
      intro a ha
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
      exact mem_L_of_mem a.property U.property
    apply (mem_parametricUniformOmegaUnion_iff (listFamilySpec U) ⟨p, hpL⟩).mpr
    exact ⟨xs.length + 1, (mem_listStages_iff U (xs.length + 1) p).mpr
      ⟨xs, Nat.lt_succ_self _, hxs.symm⟩⟩

theorem listCodes_mem_L {U : ZFSet.{u}} (hU : U ∈ L) : listCodes U ∈ L := by
  rw [← internalListCodes_eq ⟨U, hU⟩]
  exact (internalListCodes ⟨U, hU⟩).property

end OneYTruth.ConstructibleListCodes
