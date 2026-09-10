import OneYTruth.SchemaBundleZip

/-! Internal existence of the complete indexed schema bundle from the actual
syntax and truth graphs. The local arity filter is obtained by Separation;
the complete graph is then obtained by an actual Replacement instance. -/

namespace OneYTruth.SchemaBundleZip

open Constructible Constructible.Model Constructible.Delta0Formula
open SchemaBundle ExternalTower InternalNodes InternalProducts BoundedEvaluation
open InternalClosure BoundedFilterGraph StructuralSetEquations SchemaBundleProjection

universe u v

theorem entry_mem {V : ZFSet.{u}}
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (F : Fin 4 → ZFSet.{u}) (hF : ∀ i, F i ∈ V) : entry F ∈ V :=
  hpair _ (hF 0) _ (hpair _ (hF 1) _ (hpair _ (hF 2) _ (hF 3)))

theorem fields_mem_of_graphs {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V)
    (s : Stage κ) : ∀ i, fields U s i ∈ V := by
  have hf : fields U s 0 ∈ V := (pair_components_mem hV
    (hV.mem_trans ((mem_syntaxGraph_iff s _).mpr rfl) hSG)).2
  have ht : fields U s 3 ∈ V := (pair_components_mem hV
    (hV.mem_trans ((mem_graph_iff U s _).mpr rfl) hTG)).2
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  have hCross : pairProduct (fields U s 0) (assignmentCodes U) ∈ V :=
    pairProduct_mem hV N hmem (hRep 1 (pairFormula K J))
      (hRep 1 (mixedSliceGraphFormula K J)) hpair hUnion hf hA
  have hn : fields U s 2 ∈ V := by
    have h := InternalBoundedIteration.deltaSep_mem hV N hmem hSep matchingArityFormula ![] hCross
    change ZFSet.sep (fun x => Satisfies ZFMem matchingArityFormula ![x])
      (pairProduct (syntaxCodes (k := s.1) (FormulaCode.ordinalIndexCode (η := s.2.val))) (assignmentCodes U)) ∈ V at h
    rw [← scopedPairs_eq_sep] at h
    exact h
  intro i
  fin_cases i
  · exact hf
  · exact hA
  · exact hn
  · exact ht

theorem witnessValues_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V)
    (s : Stage κ) : ∀ i, WitnessValues U s i ∈ V := by
  have hF := fields_mem_of_graphs hV N hmem hCol hSep hpair hUnion U hA hSG hTG s
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  intro i
  fin_cases i
  · exact hF 0
  · exact hF 3
  · exact pairProduct_mem hV N hmem (hRep 1 (pairFormula K J))
      (hRep 1 (mixedSliceGraphFormula K J)) hpair hUnion (hF 0) (hF 1)
  · exact hF 2
  · exact entry_mem hpair _ hF

theorem query_complete {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) (p : Fin 5 → ZFCarrier V)
    (hp0 : (p 0).val = assignmentCodes U) (hp1 : (p 1).val = SchemaSyntaxGraph.graph κ)
    (hp2 : (p 2).val = @ExternalTower.graph κ U) (hp3 : (p 3).val = stageCode s)
    (hp4 : (p 4).val = ZFSet.pair (stageCode s) (entry (fields U s))) :
    realize N (query K J) Empty.elim p := by
  have hw := witnessValues_mem hV N hmem hCol hSep hpair hUnion U
    (hp0 ▸ (p 0).property) (hp1 ▸ (p 1).property) (hp2 ▸ (p 2).property) s
  apply (realize_query hV N hmem p).mpr
  refine ⟨fun i => ⟨WitnessValues U s i, hw i⟩, ?_⟩
  have hp : (fun i => (p i).val) = ![assignmentCodes U, SchemaSyntaxGraph.graph κ,
      @ExternalTower.graph κ U, stageCode s, ZFSet.pair (stageCode s) (entry (fields U s))] := by
    funext i
    fin_cases i <;> assumption
  rw [hp]
  exact satisfies_canonical_matrix U s

theorem indexedBundle_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    {κ : Ordinal.{u}} (U : ZFSet.{u}) (hStages : stageSet κ ∈ V) (hA : assignmentCodes U ∈ V)
    (hSG : SchemaSyntaxGraph.graph κ ∈ V) (hTG : @ExternalTower.graph κ U ∈ V) :
    @indexedBundle κ U ∈ V := by
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  let params : Fin 3 → ZFCarrier V := ![⟨assignmentCodes U, hA⟩,
    ⟨SchemaSyntaxGraph.graph κ, hSG⟩, ⟨@ExternalTower.graph κ U, hTG⟩]
  apply image_range_mem hV N (query K J) (hRep 3 _) params stageCode
    (fun s : Stage κ => ZFSet.pair (stageCode s) (entry (fields U s))) stageCode_injective hStages
  · intro s
    exact hpair _ (hV.mem_trans (stageCode_mem_stageSet s) hStages) _
      (entry_mem hpair _ (fields_mem_of_graphs hV N hmem hCol hSep hpair hUnion U hA hSG hTG s))
  · intro x y hx
    obtain ⟨s, hxs⟩ := ZFSet.mem_range.mp hx
    constructor
    · intro h
      have hy := query_sound hV N hmem U s (Fin.snoc (Fin.snoc params x) y) rfl rfl rfl hxs.symm h
      exact ⟨s, hxs, hy.symm⟩
    · rintro ⟨t, ht, hty⟩
      exact query_complete hV N hmem hCol hSep hpair hUnion U t
        (Fin.snoc (Fin.snoc params x) y) rfl rfl rfl ht.symm hty.symm

end OneYTruth.SchemaBundleZip

#print axioms OneYTruth.SchemaBundleZip.witnessValues_mem
#print axioms OneYTruth.SchemaBundleZip.indexedBundle_mem
