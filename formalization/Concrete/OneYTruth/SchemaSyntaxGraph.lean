import OneYTruth.SyntaxSourceCertificate
import OneYTruth.StageCoding
import OneYTruth.SourceEndpointRelation
import OneYTruth.SatisfactionTrace

/-! The entire stage-indexed syntax-source graph is a real internal set.
One fixed Sigma-one query reads k and eta from the literal stage code; actual
Replacement then collects all stage sources without an arbitrary subset or
externally chosen family-membership assumption. -/

namespace OneYTruth.SchemaSyntaxGraph

open Constructible Constructible.Model Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FirstOrder FirstOrder.Language CodedPaths
open ExternalTower FormulaCode InternalClosure

universe u v

noncomputable def syntaxAt {κ : Ordinal.{u}} (s : Stage κ) : ZFSet.{u} :=
  InternalNodes.syntaxCodes (k := s.1) (ordinalIndexCode (η := s.2.val))

noncomputable def graph (κ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun s : Stage κ => ZFSet.pair (stageCode s) (syntaxAt s))

def stagePairQuery (K : Nat) (J : Type v) :=
  ofConstructibleDeltaZero K J (kuratowskiPairEqAt (2 : Fin 6) 4 5)

noncomputable def syntaxQuery (K : Nat) (J : Type v) :=
  renameScope ![5, 0, 1, 4, (3 : Fin 6)] (SyntaxSourceCertificate.query.{u, v} .full K J)

theorem stagePairQuery_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (stagePairQuery K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

theorem syntaxQuery_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (syntaxQuery.{u, v} K J) :=
  (SyntaxSourceCertificate.query_isSigmaOne .full K J).renameScope _

/-- Omega, empty, encoded stage, candidate syntax set. -/
noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 4 :=
  (sigmaConjFormula.{v, u} (stagePairQuery K J) (syntaxQuery.{u, v} K J)
    (stagePairQuery_isSigmaOne K J) (syntaxQuery_isSigmaOne K J)).ex.ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u, v} K J) :=
  .ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _))

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 4 → ZFCarrier V) :
    realize N (query.{u+1, v} K J) Empty.elim p ↔
      ∃ k eta : ZFCarrier V, (p 2).val = ZFSet.pair k.val eta.val ∧
        realize N (SyntaxSourceCertificate.query.{u+1, v} .full K J) Empty.elim ![eta, p 0, p 1, k, p 3] := by
  rw [query, realize_scoped_ex]
  apply exists_congr; intro k
  rw [realize_scoped_ex]
  apply exists_congr; intro eta
  rw [realize_sigmaConjFormula, syntaxQuery, realize_renameScope]
  have he : Fin.snoc (Fin.snoc p k) eta ∘ ![5, 0, 1, 4, (3 : Fin 6)] =
      ![eta, p 0, p 1, k, p 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  apply and_congr_left
  intro _
  rw [stagePairQuery, realize_ofConstructibleDeltaZero_absolute hV N hmem, satisfies_kuratowskiPairEqAt]
  rfl

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    {κ : Ordinal.{u}} (s : Stage κ) (p : Fin 4 → ZFCarrier V)
    (hOmega : (p 0).val = Ordinal.omega0.toZFSet) (hZero : (p 1).val = ∅)
    (hstage : (p 2).val = stageCode s) (h : realize N (query.{u+1, v} K J) Empty.elim p) :
    (p 3).val = syntaxAt s := by
  obtain ⟨k, eta, he, hs⟩ := (realize_query hV N hmem p).mp h
  rw [hstage] at he
  have hk := (ZFSet.pair_inj.mp he).1.symm
  have hEta := (ZFSet.pair_inj.mp he).2.symm
  exact SyntaxSourceCertificate.query_sound .full hV N hmem
    (SourceEndpointComparison.ordinalAlphabet s.2.val) (SourceEndpointComparison.ordinalAlphabet_eq_range _)
    ![eta, p 0, p 1, k, p 3] hEta hOmega hZero hk hs

theorem realize_query_iff {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V)
    (hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (s : Stage κ) (p : Fin 4 → ZFCarrier V)
    (hOmega : (p 0).val = Ordinal.omega0.toZFSet) (hZero : (p 1).val = ∅)
    (hstage : (p 2).val = stageCode s) :
    realize N (query.{u+1, v} K J) Empty.elim p ↔ (p 3).val = syntaxAt s := by
  constructor
  · exact query_sound hV N hmem s p hOmega hZero hstage
  · intro hout
    have hc := pair_components_mem hV (hstage ▸ (p 2).property)
    let k : ZFCarrier V := ⟨natCode s.1, hc.1⟩
    let eta : ZFCarrier V := ⟨s.2.val.toZFSet, hc.2⟩
    apply (realize_query hV N hmem p).mpr
    refine ⟨k, eta, hstage, ?_⟩
    exact (SyntaxSourceCertificate.realize_query_iff .full hV N hmem hCol hSep hpair hUnion hempty
      (SourceEndpointComparison.ordinalAlphabet s.2.val) (SourceEndpointComparison.ordinalAlphabet_eq_range _)
      ![eta, p 0, p 1, k, p 3] rfl hOmega hZero rfl).mpr hout

def recordPairQuery (K : Nat) (J : Type v) :=
  ofConstructibleDeltaZero K J (kuratowskiPairEqAt (3 : Fin 5) 2 4)

noncomputable def valueQuery (K : Nat) (J : Type v) :=
  renameScope ![0, 1, 2, (4 : Fin 5)] (query.{u, v} K J)

theorem recordPairQuery_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (recordPairQuery K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

theorem valueQuery_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (valueQuery.{u, v} K J) :=
  (query_isSigmaOne K J).renameScope _

noncomputable def recordQuery (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 4 :=
  (sigmaConjFormula.{v, u} (recordPairQuery K J) (valueQuery.{u, v} K J)
    (recordPairQuery_isSigmaOne K J) (valueQuery_isSigmaOne K J)).ex

theorem realize_recordQuery {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 4 → ZFCarrier V) :
    realize N (recordQuery.{u+1, v} K J) Empty.elim p ↔
      ∃ F : ZFCarrier V, (p 3).val = ZFSet.pair (p 2).val F.val ∧
        realize N (query.{u+1, v} K J) Empty.elim ![p 0, p 1, p 2, F] := by
  rw [recordQuery, realize_scoped_ex]
  apply exists_congr; intro F
  rw [realize_sigmaConjFormula, valueQuery, realize_renameScope]
  have he : Fin.snoc p F ∘ ![0, 1, 2, (4 : Fin 5)] = ![p 0, p 1, p 2, F] := by
    funext i; fin_cases i <;> rfl
  rw [he]
  apply and_congr_left
  intro _
  rw [recordPairQuery, realize_ofConstructibleDeltaZero_absolute hV N hmem, satisfies_kuratowskiPairEqAt]
  rfl

theorem syntaxAt_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V)
    (hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) {κ : Ordinal.{u}} (s : Stage κ) (hs : stageCode s ∈ V) :
    syntaxAt s ∈ V :=
  InternalSyntaxCodes.syntaxCodes_mem (k := s.1) hV N hmem hCol hSep hpair hUnion hempty hOmega
    (SourceEndpointComparison.ordinalAlphabet s.2.val) (SourceEndpointComparison.ordinalAlphabet_eq_range _)
    (pair_components_mem hV hs).2

theorem graph_mem {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V)
    (hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (hOmega : Ordinal.omega0.toZFSet ∈ V) (κ : Ordinal.{u}) (hStages : stageSet κ ∈ V) : graph κ ∈ V := by
  have hRep := hasReplacement_of_collection_separation N hmem hCol hSep
  let W : ZFCarrier V := ⟨Ordinal.omega0.toZFSet, hOmega⟩
  let zero : ZFCarrier V := ⟨∅, hempty⟩
  have hs (s : Stage κ) : stageCode s ∈ V := hV.mem_trans (stageCode_mem_stageSet s) hStages
  have hF (s : Stage κ) : syntaxAt s ∈ V := syntaxAt_mem hV N hmem hCol hSep hpair hUnion hempty hOmega s (hs s)
  apply image_range_mem hV N (recordQuery.{u+1, v} K J) (hRep 2 _) ![W, zero]
    stageCode (fun s : Stage κ => ZFSet.pair (stageCode s) (syntaxAt s)) stageCode_injective hStages
    (fun s => hpair _ (hs s) _ (hF s))
  intro x y hx
  obtain ⟨s, hxs⟩ := ZFSet.mem_range.mp hx
  rw [realize_recordQuery hV N hmem]
  constructor
  · rintro ⟨F, he, hq⟩
    change y.val = ZFSet.pair x.val F.val at he
    have hf : F.val = syntaxAt s := query_sound hV N hmem s ![W, zero, x, F] rfl rfl hxs.symm hq
    exact ⟨s, hxs, by simpa only [hxs, hf] using he.symm⟩
  · rintro ⟨t, ht, he⟩
    have hts : t = s := stageCode_injective (ht.trans hxs.symm)
    subst t
    let F : ZFCarrier V := ⟨syntaxAt s, hF s⟩
    refine ⟨F, ?_, ?_⟩
    · change y.val = ZFSet.pair x.val (syntaxAt s)
      simpa only [hxs] using he.symm
    · exact (realize_query_iff hV N hmem hCol hSep hpair hUnion hempty s ![W, zero, x, F]
        rfl rfl hxs.symm).mpr rfl

end OneYTruth.SchemaSyntaxGraph

#print axioms OneYTruth.SchemaSyntaxGraph.query_sound
#print axioms OneYTruth.SchemaSyntaxGraph.graph_mem
