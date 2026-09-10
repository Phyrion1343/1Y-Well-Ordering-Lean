import OneYTruth.SchemaBundleZipInternal

/-! A single bounded matrix checks the entire stage-indexed schema bundle.
It checks totality and absence of additional records, with a common internal
bound for every finite local certificate. -/

namespace OneYTruth.SchemaBundleZip

open Constructible Constructible.Model Constructible.Delta0Formula
open SchemaBundle ExternalTower InternalNodes InternalProducts BoundedEvaluation
open InternalClosure BoundedFilterGraph StructuralSetEquations SchemaBundleProjection

universe u v

def boundedLocalAt {n : Nat} (A SG TG stage out B : Fin n) : Delta0Formula n :=
  (BoundedExistentialBlock.certificate 5 matrix).rename ![A, SG, TG, stage, out, B]

def BoundedLocal (A SG TG stage out B : ZFSet.{u}) : Prop :=
  ∃ w : Fin 5 → ZFSet.{u}, (∀ i, w i ∈ B) ∧ Local A SG TG stage out (w 0) (w 1) (w 2) (w 3) (w 4)

theorem satisfies_boundedLocalAt {n : Nat} (A SG TG stage out B : Fin n) (p : Fin n → ZFSet.{u}) :
    Satisfies ZFMem (boundedLocalAt A SG TG stage out B) p ↔
      BoundedLocal (p A) (p SG) (p TG) (p stage) (p out) (p B) := by
  rw [boundedLocalAt, satisfies_rename]
  have he : (fun i : Fin 6 => p (![A, SG, TG, stage, out, B] i)) =
      snoc ![p A, p SG, p TG, p stage, p out] (p B) := by
    funext i; fin_cases i <;> rfl
  rw [he, BoundedExistentialBlock.satisfies_certificate]
  unfold BoundedLocal
  apply exists_congr; intro w
  rw [satisfies_matrix]
  rfl

/-- Assignments, syntax graph, truth graph, stages, candidate indexed bundle,
common local witness bound. -/
def graphFormula : Delta0Formula 6 :=
  .conj (.boundedAll 3 (.boundedEx 4 (boundedLocalAt 0 1 2 6 7 5)))
    (.boundedAll 4 (.boundedEx 3 (boundedLocalAt 0 1 2 7 6 5)))

def GraphCondition (A SG TG stages G B : ZFSet.{u}) : Prop :=
  (∀ z ∈ stages, ∃ out ∈ G, BoundedLocal A SG TG z out B) ∧
    ∀ out ∈ G, ∃ z ∈ stages, BoundedLocal A SG TG z out B

theorem satisfies_graphFormula (A SG TG stages G B : ZFSet.{u}) :
    Satisfies ZFMem graphFormula ![A, SG, TG, stages, G, B] ↔
      GraphCondition A SG TG stages G B := by
  simp only [graphFormula, Satisfies, satisfies_boundedAll, satisfies_boundedLocalAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem, GraphCondition]

theorem graphCondition_sound {κ : Ordinal.{u}} (U G B : ZFSet.{u})
    (h : GraphCondition (assignmentCodes U) (SchemaSyntaxGraph.graph κ) (@ExternalTower.graph κ U)
      (stageSet κ) G B) : G = @indexedBundle κ U := by
  apply ZFSet.ext
  intro out
  constructor
  · intro hout
    obtain ⟨z, hz, w, _, hw⟩ := h.2 out hout
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hz
    have he := ((local_iff_canonical U s _ _ _ _ _ _).mp hw).2.2.2.2.2
    exact ZFSet.mem_range.mpr ⟨s, he.symm⟩
  · intro hout
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hout
    obtain ⟨out, hout, w, _, hw⟩ := h.1 (stageCode s) (stageCode_mem_stageSet s)
    have he := ((local_iff_canonical U s _ _ _ _ _ _).mp hw).2.2.2.2.2
    exact he ▸ hout

theorem graphCondition_complete {κ : Ordinal.{u}} (U B : ZFSet.{u})
    (hB : ∀ s : Stage κ, ∀ i, WitnessValues U s i ∈ B) :
    GraphCondition (assignmentCodes U) (SchemaSyntaxGraph.graph κ) (@ExternalTower.graph κ U)
      (stageSet κ) (@indexedBundle κ U) B := by
  have hlocal (s : Stage κ) : BoundedLocal (assignmentCodes U) (SchemaSyntaxGraph.graph κ)
      (@ExternalTower.graph κ U) (stageCode s) (ZFSet.pair (stageCode s) (entry (fields U s))) B :=
    ⟨WitnessValues U s, hB s, (local_iff_canonical U s _ _ _ _ _ _).mpr
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  constructor
  · intro z hz
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨_, ZFSet.mem_range_self s, hlocal s⟩
  · intro out hout
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hout
    exact ⟨_, stageCode_mem_stageSet s, hlocal s⟩

theorem satisfies_graphFormula_sound {κ : Ordinal.{u}} (U G B : ZFSet.{u})
    (h : Satisfies ZFMem graphFormula ![assignmentCodes U, SchemaSyntaxGraph.graph κ,
      @ExternalTower.graph κ U, stageSet κ, G, B]) : G = @indexedBundle κ U :=
  graphCondition_sound U G B ((satisfies_graphFormula _ _ _ _ _ _).mp h)

end OneYTruth.SchemaBundleZip

#print axioms OneYTruth.SchemaBundleZip.satisfies_graphFormula_sound
