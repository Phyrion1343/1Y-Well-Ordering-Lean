import OneYTruth.SchemaSyntaxGraph
import OneYTruth.SchemaBundleProjection
import OneYTruth.StructuralSetEquations
import OneYTruth.ScopedExistentialBlock
import OneYTruth.UniformWitnessBound

/-! Literal bounded joining of syntax and truth at the same encoded stage.
Node sets are checked as the exact arity filter on the actual product. The
local matrix determines every field, not merely a purported record label. -/

namespace OneYTruth.SchemaBundleZip

open Constructible Constructible.Model Constructible.Delta0Formula
open SchemaBundle ExternalTower InternalNodes InternalProducts BoundedEvaluation
open BoundedFilterGraph StructuralSetEquations SchemaBundleProjection ScopedExistentialBlock

universe u v

theorem mem_syntaxGraph_iff {κ : Ordinal.{u}} (s : Stage κ) (F : ZFSet.{u}) :
    ZFSet.pair (stageCode s) F ∈ SchemaSyntaxGraph.graph κ ↔ F = SchemaSyntaxGraph.syntaxAt s := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := ZFSet.mem_range.mp h
    obtain ⟨hst, hF⟩ := ZFSet.pair_inj.mp ht
    have hts : t = s := stageCode_injective hst
    subst t
    exact hF.symm
  · rintro rfl
    exact ZFSet.mem_range_self s

/-- Assignments, syntax graph, truth graph, stage, output record;
then syntax, Sat, product, nodes, quadruple. -/
def matrix : Delta0Formula 10 :=
  .conj (pairMemAt 1 3 5) (.conj (pairMemAt 2 3 6)
    (.conj (productAt 7 5 0) (.conj (filterAt matchingArityFormula ![] 7 8)
      (.conj (entryAt 9 5 0 8 6) (kuratowskiPairEqAt 4 3 9)))))

def Local (A SG TG z out f t cross nodes quad : ZFSet.{u}) : Prop :=
  ZFSet.pair z f ∈ SG ∧ ZFSet.pair z t ∈ TG ∧ cross = pairProduct f A ∧
    nodes = ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x]) cross ∧
    quad = entry ![f, A, nodes, t] ∧ out = ZFSet.pair z quad

theorem satisfies_matrix (p : Fin 10 → ZFSet.{u}) :
    Satisfies ZFMem matrix p ↔ Local (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) := by
  have he (x : ZFSet.{u}) : snoc (fun i : Fin 0 => p (![] i)) x = ![x] := by
    funext i; fin_cases i; rfl
  simp only [matrix, Satisfies, satisfies_pairMemAt, satisfies_productAt,
    satisfies_filterAt, satisfies_entryAt, satisfies_kuratowskiPairEqAt, he, Local]

noncomputable def WitnessValues {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) : Fin 5 → ZFSet.{u} :=
  ![fields U s 0, fields U s 3, pairProduct (fields U s 0) (fields U s 1),
    fields U s 2, entry (fields U s)]

theorem local_iff_canonical {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ)
    (out f t cross nodes quad : ZFSet.{u}) :
    Local (assignmentCodes U) (SchemaSyntaxGraph.graph κ) (@ExternalTower.graph κ U)
      (stageCode s) out f t cross nodes quad ↔
      f = fields U s 0 ∧ t = fields U s 3 ∧ cross = pairProduct (fields U s 0) (fields U s 1) ∧
      nodes = fields U s 2 ∧ quad = entry (fields U s) ∧ out = ZFSet.pair (stageCode s) (entry (fields U s)) := by
  unfold Local
  rw [mem_syntaxGraph_iff, mem_graph_iff]
  have hTuple : ![fields U s 0, fields U s 1, fields U s 2, fields U s 3] = fields U s := by
    funext i; fin_cases i <;> rfl
  constructor
  · rintro ⟨hf, ht, hc, hn, hq, hout⟩
    have hn' : nodes = fields U s 2 := by
      rw [hc, hf] at hn
      change nodes = ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x])
        (pairProduct (syntaxCodes (k := s.1) (FormulaCode.ordinalIndexCode (η := s.2.val))) (assignmentCodes U)) at hn
      rw [← scopedPairs_eq_sep] at hn
      exact hn
    have hq' : quad = entry (fields U s) := by
      rw [hf, ht, hn'] at hq
      change quad = entry ![fields U s 0, fields U s 1, fields U s 2, fields U s 3] at hq
      rwa [hTuple] at hq
    have hc' : cross = pairProduct (fields U s 0) (fields U s 1) := by
      rw [hf] at hc
      exact hc
    exact ⟨hf, ht, hc', hn', hq', hout.trans (congrArg (ZFSet.pair (stageCode s)) hq')⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
    · exact scopedPairs_eq_sep _ _
    · exact congrArg entry hTuple.symm

theorem satisfies_canonical_matrix {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :
    Satisfies ZFMem matrix (Fin.append
      ![assignmentCodes U, SchemaSyntaxGraph.graph κ, @ExternalTower.graph κ U,
        stageCode s, ZFSet.pair (stageCode s) (entry (fields U s))] (WitnessValues U s)) := by
  rw [satisfies_matrix]
  exact (local_iff_canonical U s _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def query (K : Nat) (J : Type v) := bind 5 5 (ofConstructibleDeltaZero K J matrix)

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query K J) :=
  isSigmaOne_bind 5 5 _ (.deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _))

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 5 → ZFCarrier V) :
    realize N (query K J) Empty.elim p ↔ ∃ w : Fin 5 → ZFCarrier V,
      Satisfies ZFMem matrix (Fin.append (fun i => (p i).val) (fun i => (w i).val)) := by
  rw [query, realize_bind]
  apply exists_congr
  intro w
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
  rfl

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) (p : Fin 5 → ZFCarrier V)
    (hp0 : (p 0).val = assignmentCodes U) (hp1 : (p 1).val = SchemaSyntaxGraph.graph κ)
    (hp2 : (p 2).val = @ExternalTower.graph κ U) (hp3 : (p 3).val = stageCode s)
    (h : realize N (query K J) Empty.elim p) :
    (p 4).val = ZFSet.pair (stageCode s) (entry (fields U s)) := by
  obtain ⟨w, hw⟩ := (realize_query hV N hmem p).mp h
  rw [satisfies_matrix] at hw
  change Local (p 0).val (p 1).val (p 2).val (p 3).val (p 4).val
    (w 0).val (w 1).val (w 2).val (w 3).val (w 4).val at hw
  rw [hp0, hp1, hp2, hp3, local_iff_canonical] at hw
  exact hw.2.2.2.2.2

end OneYTruth.SchemaBundleZip

#print axioms OneYTruth.SchemaBundleZip.local_iff_canonical
#print axioms OneYTruth.SchemaBundleZip.query_sound
