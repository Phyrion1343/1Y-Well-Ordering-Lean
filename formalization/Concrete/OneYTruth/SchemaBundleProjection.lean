import OneYTruth.SchemaBundle
import OneYTruth.StageCoding
import OneYTruth.FiniteCodeFormula

/-! The old stage-forgetting schema bundle and its exact field range are
bounded projections of the complete stage-indexed bundle. Both directions
are checked, so no omitted stage or surplus bundle/field is silently allowed.
-/

namespace OneYTruth.SchemaBundleProjection

open Constructible Constructible.Delta0Formula Constructible.Model
open SchemaBundle ExternalTower FiniteCodeFormula BoundedEvaluation

universe u

noncomputable def indexedBundle {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun s : Stage κ => ZFSet.pair (stageCode s) (entry (fields U s)))

theorem entry_injective : Function.Injective (entry : (Fin 4 → ZFSet.{u}) → ZFSet.{u}) := by
  intro F G he
  have h0 := (ZFSet.pair_inj.mp he).1
  have he1 := (ZFSet.pair_inj.mp he).2
  have h1 := (ZFSet.pair_inj.mp he1).1
  have he2 := (ZFSet.pair_inj.mp he1).2
  have h2 := (ZFSet.pair_inj.mp he2).1
  have h3 := (ZFSet.pair_inj.mp he2).2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

def entryAt {n : Nat} (e f a nodes sat : Fin n) : Delta0Formula n :=
  chainEqAt 3 ![f, a, nodes] e sat

theorem satisfies_entryAt {n : Nat} (e f a nodes sat : Fin n) (p : Fin n → ZFSet.{u}) :
    Satisfies ZFMem (entryAt e f a nodes sat) p ↔ p e = entry ![p f, p a, p nodes, p sat] := by
  rw [entryAt, satisfies_chainEqAt]
  simp [List.ofFn_succ, chainCode, entry]

/-- Stages, indexed graph, old bundle, exact field bound. -/
def rangeFormula : Delta0Formula 4 :=
  .conj (.boundedAll 1 (.boundedEx 0 (.boundedEx 2 (kuratowskiPairEqAt 4 5 6))))
    (.boundedAll 2 (.boundedEx 0 (pairMemAt 1 5 4)))

def RangeProjection (stages g B : ZFSet.{u}) : Prop :=
  (∀ r ∈ g, ∃ s ∈ stages, ∃ e ∈ B, r = ZFSet.pair s e) ∧
    ∀ e ∈ B, ∃ s ∈ stages, ZFSet.pair s e ∈ g

theorem satisfies_rangeFormula (S G B C : ZFSet.{u}) :
    Satisfies ZFMem rangeFormula ![S, G, B, C] ↔ RangeProjection S G B := by
  simp only [rangeFormula, Satisfies, satisfies_boundedAll, satisfies_kuratowskiPairEqAt,
    satisfies_pairMemAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem, RangeProjection]

def fieldsFormula : Delta0Formula 4 :=
  .conj (.boundedAll 2 (.boundedEx 3 (.boundedEx 3 (.boundedEx 3 (.boundedEx 3
    (entryAt 4 5 6 7 8))))))
    (.boundedAll 3 (.boundedEx 2 (.boundedEx 3 (.boundedEx 3 (.boundedEx 3 (.boundedEx 3
      (.conj (entryAt 5 6 7 8 9)
        (.disj (.eq 4 6) (.disj (.eq 4 7) (.disj (.eq 4 8) (.eq 4 9)))))))))))

def FieldProjection (B C : ZFSet.{u}) : Prop :=
  (∀ e ∈ B, ∃ f ∈ C, ∃ a ∈ C, ∃ n ∈ C, ∃ t ∈ C, e = entry ![f, a, n, t]) ∧
    ∀ x ∈ C, ∃ e ∈ B, ∃ f ∈ C, ∃ a ∈ C, ∃ n ∈ C, ∃ t ∈ C,
      e = entry ![f, a, n, t] ∧ (x = f ∨ x = a ∨ x = n ∨ x = t)

theorem satisfies_fieldsFormula (S G B C : ZFSet.{u}) :
    Satisfies ZFMem fieldsFormula ![S, G, B, C] ↔ FieldProjection B C := by
  simp only [fieldsFormula, Satisfies, satisfies_boundedAll, satisfies_entryAt, satisfies_disj]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem, FieldProjection]

def formula : Delta0Formula 4 := .conj rangeFormula fieldsFormula

theorem satisfies_formula (S G B C : ZFSet.{u}) :
    Satisfies ZFMem formula ![S, G, B, C] ↔ RangeProjection S G B ∧ FieldProjection B C := by
  exact and_congr (satisfies_rangeFormula _ _ _ _) (satisfies_fieldsFormula _ _ _ _)

theorem rangeProjection_iff {κ : Ordinal.{u}} (U B : ZFSet.{u}) :
    RangeProjection (stageSet κ) (@indexedBundle κ U) B ↔ B = @bundle κ U := by
  constructor
  · rintro ⟨hleft, hright⟩
    apply ZFSet.ext
    intro e
    constructor
    · intro he
      obtain ⟨z, _, hz⟩ := hright e he
      obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hz
      exact ZFSet.mem_range.mpr ⟨s, (ZFSet.pair_inj.mp hs).2⟩
    · intro he
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp he
      obtain ⟨z, _, e, he, hz⟩ := hleft _ (ZFSet.mem_range_self (f := fun t : Stage κ =>
        ZFSet.pair (stageCode t) (entry (fields U t))) s)
      exact (ZFSet.pair_inj.mp hz).2.symm ▸ he
  · rintro rfl
    constructor
    · intro r hr
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hr
      exact ⟨stageCode s, stageCode_mem_stageSet s, entry (fields U s), ZFSet.mem_range_self s, rfl⟩
    · intro e he
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp he
      exact ⟨stageCode s, stageCode_mem_stageSet s, ZFSet.mem_range_self s⟩

theorem fieldProjection_iff {κ : Ordinal.{u}} (U C : ZFSet.{u}) :
    FieldProjection (@bundle κ U) C ↔ C = @fieldBound κ U := by
  constructor
  · rintro ⟨htotal, hjunk⟩
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨e, he, f, _, a, _, n, _, t, _, hentry, hx⟩ := hjunk x hx
      obtain ⟨s, hs⟩ := ZFSet.mem_range.mp he
      have heq : fields U s = ![f, a, n, t] := entry_injective (hs.trans hentry)
      have hm (i : Fin 4) : (![f, a, n, t] : Fin 4 → ZFSet.{u}) i ∈ @fieldBound κ U := by
        rw [← heq]
        exact fields_mem_bound U s i
      rcases hx with rfl | rfl | rfl | rfl
      · exact hm 0
      · exact hm 1
      · exact hm 2
      · exact hm 3
    · intro hx
      obtain ⟨⟨s, i⟩, rfl⟩ := ZFSet.mem_range.mp hx
      obtain ⟨f, hf, a, ha, n, hn, t, ht, he⟩ := htotal (entry (fields U s)) (ZFSet.mem_range_self s)
      have heq := entry_injective he
      rw [heq]
      fin_cases i
      · exact hf
      · exact ha
      · exact hn
      · exact ht
  · rintro rfl
    have htuple (s : Stage κ) : entry (fields U s) =
        entry ![fields U s 0, fields U s 1, fields U s 2, fields U s 3] := by
      apply congrArg entry
      funext i; fin_cases i <;> rfl
    constructor
    · intro e he
      obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp he
      exact ⟨fields U s 0, fields_mem_bound U s 0, fields U s 1, fields_mem_bound U s 1,
        fields U s 2, fields_mem_bound U s 2, fields U s 3, fields_mem_bound U s 3, htuple s⟩
    · intro x hx
      obtain ⟨⟨s, i⟩, rfl⟩ := ZFSet.mem_range.mp hx
      refine ⟨entry (fields U s), ZFSet.mem_range_self s,
        fields U s 0, fields_mem_bound U s 0, fields U s 1, fields_mem_bound U s 1,
        fields U s 2, fields_mem_bound U s 2, fields U s 3, fields_mem_bound U s 3, htuple s, ?_⟩
      fin_cases i <;> simp

theorem satisfies_iff_canonical {κ : Ordinal.{u}} (U B C : ZFSet.{u}) :
    Satisfies ZFMem formula ![stageSet κ, @indexedBundle κ U, B, C] ↔
      B = @bundle κ U ∧ C = @fieldBound κ U := by
  rw [satisfies_formula, rangeProjection_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (fieldProjection_iff U C).mp h⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, (fieldProjection_iff U _).mpr rfl⟩

end OneYTruth.SchemaBundleProjection

#print axioms OneYTruth.SchemaBundleProjection.satisfies_iff_canonical
