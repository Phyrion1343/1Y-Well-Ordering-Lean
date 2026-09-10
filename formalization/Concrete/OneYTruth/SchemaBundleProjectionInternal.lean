import OneYTruth.SchemaBundleUniformBound

/-! The old schema bundle and its exact field set are genuine internal
bounded separations of the uniformly collected certificate bound. -/

namespace OneYTruth.SchemaBundleProjection

open Constructible Constructible.Model Constructible.Delta0Formula
open SchemaBundle ExternalTower InternalNodes InternalProducts BoundedEvaluation
open InternalClosure SchemaBundleZip ConstructibleBoundedIteration

universe u v

def quadFilter : Delta0Formula 3 := .boundedEx 0 (pairMemAt 1 3 2)

theorem satisfies_quadFilter (S G x : ZFSet.{u}) :
    Satisfies ZFMem quadFilter ![S, G, x] ↔ ∃ z ∈ S, ZFSet.pair z x ∈ G := by
  simp only [quadFilter, Satisfies, satisfies_pairMemAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem]

theorem satisfies_quadFilter_canonical {κ : Ordinal.{u}} (U x : ZFSet.{u}) :
    Satisfies ZFMem quadFilter ![stageSet κ, @indexedBundle κ U, x] ↔ x ∈ @bundle κ U := by
  rw [satisfies_quadFilter]
  constructor
  · rintro ⟨z, _, hz⟩
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.mem_range.mpr ⟨s, (ZFSet.pair_inj.mp hs).2⟩
  · intro hx
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hx
    exact ⟨_, stageCode_mem_stageSet s, ZFSet.mem_range_self s⟩

def fieldFilter : Delta0Formula 3 :=
  .boundedEx 0 (.boundedEx 1 (.boundedEx 1 (.boundedEx 1 (.boundedEx 1
    (.conj (entryAt 3 4 5 6 7)
      (.disj (.eq 2 4) (.disj (.eq 2 5) (.disj (.eq 2 6) (.eq 2 7)))))))))

theorem satisfies_fieldFilter (B C x : ZFSet.{u}) :
    Satisfies ZFMem fieldFilter ![B, C, x] ↔
      ∃ e ∈ B, ∃ f ∈ C, ∃ a ∈ C, ∃ n ∈ C, ∃ t ∈ C,
        e = entry ![f, a, n, t] ∧ (x = f ∨ x = a ∨ x = n ∨ x = t) := by
  simp only [fieldFilter, Satisfies, satisfies_entryAt, satisfies_disj]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem]

theorem satisfies_fieldFilter_canonical {κ : Ordinal.{u}} (U C x : ZFSet.{u})
    (hC : ∀ s : Stage κ, ∀ i, fields U s i ∈ C) :
    Satisfies ZFMem fieldFilter ![@bundle κ U, C, x] ↔ x ∈ @fieldBound κ U := by
  rw [satisfies_fieldFilter]
  constructor
  · rintro ⟨e, he, f, _, a, _, n, _, t, _, heq, hx⟩
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp he
    have hfields := entry_injective (hs.trans heq)
    have hm (i : Fin 4) : (![f, a, n, t] : Fin 4 → ZFSet.{u}) i ∈ @fieldBound κ U := by
      rw [← hfields]
      exact fields_mem_bound U s i
    rcases hx with rfl | rfl | rfl | rfl
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · exact hm 3
  · intro hx
    obtain ⟨⟨s, i⟩, rfl⟩ := ZFSet.mem_range.mp hx
    refine ⟨_, ZFSet.mem_range_self s, _, hC s 0, _, hC s 1, _, hC s 2, _, hC s 3, ?_, ?_⟩
    · apply congrArg entry
      funext j; fin_cases j <;> rfl
    · fin_cases i <;> simp

theorem bundle_mem_of_uniform_bound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hSep : HasSeparation N)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hS : stageSet κ ∈ V) (hG : @indexedBundle κ U ∈ V)
    (C : ZFCarrier V) (hC : ∀ s : Stage κ, entry (fields U s) ∈ C.val) :
    @bundle κ U ∈ V := by
  have hm := InternalBoundedIteration.deltaSep_mem hV N hmem hSep quadFilter
    ![⟨stageSet κ, hS⟩, ⟨@indexedBundle κ U, hG⟩] C.property
  have he : deltaSep quadFilter ![stageSet κ, @indexedBundle κ U] C.val = @bundle κ U := by
    apply ZFSet.ext
    intro x
    change (x ∈ ZFSet.sep _ C.val) ↔ _
    rw [ZFSet.mem_sep]
    have ht : snoc ![stageSet κ, @indexedBundle κ U] x = ![stageSet κ, @indexedBundle κ U, x] := by
      funext i; fin_cases i <;> rfl
    rw [ht, satisfies_quadFilter_canonical]
    constructor
    · exact And.right
    · intro hx
      obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hx
      exact ⟨hs ▸ hC s, ZFSet.mem_range.mpr ⟨s, hs⟩⟩
  exact he ▸ hm

theorem fieldBound_mem_of_uniform_bound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hSep : HasSeparation N)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hB : @bundle κ U ∈ V)
    (C : ZFCarrier V) (hC : ∀ s : Stage κ, ∀ i, fields U s i ∈ C.val) :
    @fieldBound κ U ∈ V := by
  have hm := InternalBoundedIteration.deltaSep_mem hV N hmem hSep fieldFilter
    ![⟨@bundle κ U, hB⟩, C] C.property
  have he : deltaSep fieldFilter ![@bundle κ U, C.val] C.val = @fieldBound κ U := by
    apply ZFSet.ext
    intro x
    change (x ∈ ZFSet.sep _ C.val) ↔ _
    rw [ZFSet.mem_sep]
    have ht : snoc ![@bundle κ U, C.val] x = ![@bundle κ U, C.val, x] := by
      funext i; fin_cases i <;> rfl
    rw [ht, satisfies_fieldFilter_canonical U C.val x hC]
    constructor
    · exact And.right
    · intro hx
      obtain ⟨⟨s, i⟩, hs⟩ := ZFSet.mem_range.mp hx
      exact ⟨hs ▸ hC s i, ZFSet.mem_range.mpr ⟨(s, i), hs⟩⟩
  exact he ▸ hm

theorem bundle_and_fieldBound_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hStages : stageSet κ ∈ V) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V) :
    @bundle κ U ∈ V ∧ @fieldBound κ U ∈ V := by
  have hG := indexedBundle_mem hV N hmem hCol hSep hpair hUnion U hStages hA hSG hTG
  obtain ⟨C, hW, _, hF⟩ := exists_uniform_field_bound hV N hmem hCol hSep hpair hUnion hempty
    U hStages hA hSG hTG
  have hB := bundle_mem_of_uniform_bound hV N hmem hSep U hStages hG C (fun s => hW s 4)
  exact ⟨hB, fieldBound_mem_of_uniform_bound hV N hmem hSep U hB C hF⟩

end OneYTruth.SchemaBundleProjection

#print axioms OneYTruth.SchemaBundleProjection.bundle_and_fieldBound_mem
