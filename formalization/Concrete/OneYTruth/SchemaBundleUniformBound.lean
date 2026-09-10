import OneYTruth.SchemaBundleZipFormula

/-! Actual Collection supplies one internal set containing every local
certificate field at every stage, and every indexed record. -/

namespace OneYTruth.SchemaBundleZip

open Constructible Constructible.Model Constructible.Delta0Formula
open SchemaBundle ExternalTower InternalNodes InternalProducts BoundedEvaluation
open InternalClosure SchemaBundleProjection

universe u v

noncomputable def fullWitnessValues {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) : Fin 6 → ZFSet.{u} :=
  ![ZFSet.pair (stageCode s) (entry (fields U s)), fields U s 0, fields U s 3,
    pairProduct (fields U s 0) (fields U s 1), fields U s 2, entry (fields U s)]

theorem exists_uniform_field_bound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hStages : stageSet κ ∈ V) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V) :
    ∃ B : ZFCarrier V, (∀ s : Stage κ, ∀ i, WitnessValues U s i ∈ B.val) ∧
      (∀ s : Stage κ, ZFSet.pair (stageCode s) (entry (fields U s)) ∈ B.val) ∧
      ∀ s : Stage κ, ∀ i, fields U s i ∈ B.val := by
  let params : Fin 3 → ZFCarrier V := ![⟨assignmentCodes U, hA⟩,
    ⟨SchemaSyntaxGraph.graph κ, hSG⟩, ⟨@ExternalTower.graph κ U, hTG⟩]
  have hwmem (s : Stage κ) : ∀ i, fullWitnessValues U s i ∈ V := by
    have hw := witnessValues_mem hV N hmem hCol hSep hpair hUnion U hA hSG hTG s
    intro i
    fin_cases i
    · exact hpair _ (hV.mem_trans (stageCode_mem_stageSet s) hStages) _ (hw 4)
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · exact hw 3
    · exact hw 4
  have hlocal (x : ZFCarrier V) (hx : x.val ∈ stageSet κ) : ∃ w : Fin 6 → ZFCarrier V,
      Satisfies ZFMem matrix (Fin.append (fun i => ((Fin.snoc params x : Fin 4 → ZFCarrier V) i).val)
        (fun i => (w i).val)) := by
    obtain ⟨s, hxs⟩ := ZFSet.mem_range.mp hx
    refine ⟨fun i => ⟨fullWitnessValues U s i, hwmem s i⟩, ?_⟩
    rw [satisfies_matrix]
    change Local (assignmentCodes U) (SchemaSyntaxGraph.graph κ) (@ExternalTower.graph κ U)
      x.val _ _ _ _ _ _
    rw [← hxs]
    exact (local_iff_canonical U s _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨C, hC⟩ := UniformWitnessBound.exists_uniform_bound hV N hmem hCol hpair hUnion hempty
    6 matrix params ⟨stageSet κ, hStages⟩ hlocal
  have hfull (s : Stage κ) : ∀ i, fullWitnessValues U s i ∈ C.val := by
    let x : ZFCarrier V := ⟨stageCode s, hV.mem_trans (stageCode_mem_stageSet s) hStages⟩
    obtain ⟨w, hw, hm⟩ := (UniformWitnessBound.realize_certificate hV N hmem 6 matrix
      (Fin.snoc params x) C).mp (hC x (stageCode_mem_stageSet s))
    rw [satisfies_matrix] at hm
    change Local (assignmentCodes U) (SchemaSyntaxGraph.graph κ) (@ExternalTower.graph κ U)
      (stageCode s) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) at hm
    obtain ⟨hf, ht, hc, hn, hq, ho⟩ := (local_iff_canonical U s _ _ _ _ _ _).mp hm
    have he : w = fullWitnessValues U s := by
      funext i
      fin_cases i
      · exact ho
      · exact hf
      · exact ht
      · exact hc
      · exact hn
      · exact hq
    simpa only [he] using hw
  let B : ZFCarrier V := ⟨insert (assignmentCodes U) C.val, insert_mem hV hpair hUnion hA C.property⟩
  have hin {z : ZFSet.{u}} (hz : z ∈ C.val) : z ∈ B.val := ZFSet.mem_insert_iff.mpr (Or.inr hz)
  have hW (s : Stage κ) : ∀ i, WitnessValues U s i ∈ B.val := by
    intro i
    fin_cases i
    · exact hin (hfull s 1)
    · exact hin (hfull s 2)
    · exact hin (hfull s 3)
    · exact hin (hfull s 4)
    · exact hin (hfull s 5)
  refine ⟨B, hW, (fun s => hin (hfull s 0)), ?_⟩
  intro s i
  fin_cases i
  · exact hW s 0
  · exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  · exact hW s 3
  · exact hW s 1

theorem exists_graphFormula {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hStages : stageSet κ ∈ V) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V) :
    ∃ B : ZFCarrier V, Satisfies ZFMem graphFormula ![assignmentCodes U, SchemaSyntaxGraph.graph κ,
      @ExternalTower.graph κ U, stageSet κ, @indexedBundle κ U, B.val] := by
  obtain ⟨B, hB, _, _⟩ := exists_uniform_field_bound hV N hmem hCol hSep hpair hUnion hempty U hStages hA hSG hTG
  exact ⟨B, (satisfies_graphFormula _ _ _ _ _ _).mpr (graphCondition_complete U B.val hB)⟩

end OneYTruth.SchemaBundleZip

#print axioms OneYTruth.SchemaBundleZip.exists_uniform_field_bound
#print axioms OneYTruth.SchemaBundleZip.exists_graphFormula
