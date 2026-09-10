import OneYTruth.SchemaSyntaxGraph
import OneYTruth.PureSigmaBounded
import OneYTruth.PureSchemaRestriction
import OneYTruth.UniformWitnessBound

/-! A Sigma-one certificate for the complete stage-indexed syntax graph.
The bounded matrix checks every actual stage and forbids additional records.
Actual Collection supplies one shared bound for all local syntax witnesses. -/

namespace OneYTruth.SchemaSyntaxCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open ExternalTower InternalClosure SchemaSyntaxGraph

universe u v

theorem localQuery_isSigmaOne : IsSigmaOne (recordQuery.{u+1,0} 0 Empty) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

noncomputable def localCertificate : PureSigmaBounded.Certificate.{u} (recordQuery.{u+1,0} 0 Empty) :=
  Classical.choice (PureSigmaBounded.exists_certificate localQuery_isSigmaOne (by decide))

noncomputable def localAt {n : Nat} (W zero stage out B : Fin n) : Delta0Formula n :=
  localCertificate.{u}.formula.rename ![W, zero, stage, out, B]

theorem satisfies_localAt {n : Nat} (W zero stage out B : Fin n) (p : Fin n → ZFSet.{u}) :
    Satisfies ZFMem (localAt.{u} W zero stage out B) p ↔
      Satisfies ZFMem localCertificate.{u}.formula ![p W, p zero, p stage, p out, p B] := by
  rw [localAt, satisfies_rename]
  have he : (fun i : Fin 5 => p (![W, zero, stage, out, B] i)) =
      ![p W, p zero, p stage, p out, p B] := by
    funext i; fin_cases i <;> rfl
  rw [he]

/-- Omega, empty set, stage set, candidate graph, witness bound. -/
noncomputable def matrix : Delta0Formula 5 :=
  .conj (.boundedAll 2 (.boundedEx 3 (localAt.{u} 0 1 5 6 4)))
    (.boundedAll 3 (.boundedEx 2 (localAt.{u} 0 1 6 5 4)))

def Condition (W zero S G B : ZFSet.{u}) : Prop :=
  (∀ z ∈ S, ∃ out ∈ G, Satisfies ZFMem localCertificate.{u}.formula ![W, zero, z, out, B]) ∧
    ∀ out ∈ G, ∃ z ∈ S, Satisfies ZFMem localCertificate.{u}.formula ![W, zero, z, out, B]

theorem satisfies_matrix (W zero S G B : ZFSet.{u}) :
    Satisfies ZFMem matrix.{u} ![W, zero, S, G, B] ↔ Condition W zero S G B := by
  simp only [matrix, Satisfies, satisfies_boundedAll, satisfies_localAt]
  simp [constructible_snoc_eq, Fin.snoc, Fin.castPred, Fin.castLT, ZFMem, Condition]

def pureModel (V : ZFSet.{u}) : Interpretation 0 Empty (ZFCarrier V) :=
  ⟨zfCarrierMem V, Fin.elim0, Empty.elim⟩

theorem local_sound {V : ZFSet.{u}} (hV : V.IsTransitive) {κ : Ordinal.{u}}
    (s : Stage κ) (p : Fin 4 → ZFCarrier V) (B : ZFCarrier V)
    (hW : (p 0).val = Ordinal.omega0.toZFSet) (h0 : (p 1).val = ∅)
    (hs : (p 2).val = stageCode s)
    (h : Satisfies ZFMem localCertificate.{u}.formula ![(p 0).val, (p 1).val, (p 2).val, (p 3).val, B.val]) :
    (p 3).val = ZFSet.pair (stageCode s) (syntaxAt s) := by
  have heval : snoc (fun i => (p i).val) B.val = ![(p 0).val, (p 1).val, (p 2).val, (p 3).val, B.val] := by
    funext i; fin_cases i <;> rfl
  have hq := localCertificate.{u}.sound hV (pureModel V) rfl p B (heval.symm ▸ h)
  obtain ⟨F, he, hf⟩ := (realize_recordQuery hV (pureModel V) rfl p).mp hq
  have hF : F.val = syntaxAt s := SchemaSyntaxGraph.query_sound hV (pureModel V) rfl s ![p 0, p 1, p 2, F] hW h0 hs hf
  simpa only [hs, hF] using he

theorem condition_sound {V : ZFSet.{u}} (hV : V.IsTransitive) {κ : Ordinal.{u}}
    (W zero S G B : ZFCarrier V) (hW : W.val = Ordinal.omega0.toZFSet) (h0 : zero.val = ∅)
    (hS : S.val = stageSet κ) (h : Condition W.val zero.val S.val G.val B.val) :
    G.val = graph κ := by
  have hf (z out : ZFSet.{u}) (hz : z ∈ S.val) (ho : out ∈ G.val)
      (hc : Satisfies ZFMem localCertificate.{u}.formula ![W.val, zero.val, z, out, B.val]) :
      ∃ s : Stage κ, z = stageCode s ∧ out = ZFSet.pair (stageCode s) (syntaxAt s) := by
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hS ▸ hz)
    let zV : ZFCarrier V := ⟨z, hV.mem_trans hz S.property⟩
    let oV : ZFCarrier V := ⟨out, hV.mem_trans ho G.property⟩
    exact ⟨s, hs.symm, local_sound hV s ![W, zero, zV, oV] B hW h0 hs.symm hc⟩
  apply ZFSet.ext
  intro out
  constructor
  · intro ho
    obtain ⟨z, hz, hc⟩ := h.2 out ho
    obtain ⟨s, _, he⟩ := hf z out hz ho hc
    exact ZFSet.mem_range.mpr ⟨s, he.symm⟩
  · intro ho
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp ho
    have hs : stageCode s ∈ S.val := hS ▸ stageCode_mem_stageSet s
    obtain ⟨out, ho, hc⟩ := h.1 (stageCode s) hs
    have he := local_sound hV s ![W, zero, ⟨stageCode s, hV.mem_trans hs S.property⟩,
      ⟨out, hV.mem_trans ho G.property⟩] B hW h0 rfl hc
    exact he ▸ ho

noncomputable def query (K : Nat) (J : Type v) := (ofConstructibleDeltaZero K J matrix.{u}).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _))

theorem realize_query {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 4 → ZFCarrier V) :
    realize N (query.{u,v} K J) Empty.elim p ↔ ∃ B : ZFCarrier V,
      Condition (p 0).val (p 1).val (p 2).val (p 3).val B.val := by
  rw [query, realize_scoped_ex]
  apply exists_congr; intro B
  rw [realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have ht : val (Fin.snoc p B) = ![(p 0).val, (p 1).val, (p 2).val, (p 3).val, B.val] := by
    funext i; fin_cases i <;> rfl
  rw [ht, satisfies_matrix]

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    {κ : Ordinal.{u}} (p : Fin 4 → ZFCarrier V)
    (hW : (p 0).val = Ordinal.omega0.toZFSet) (h0 : (p 1).val = ∅) (hS : (p 2).val = stageSet κ)
    (h : realize N (query.{u,v} K J) Empty.elim p) : (p 3).val = graph κ := by
  obtain ⟨B, hB⟩ := (realize_query hV N hmem p).mp h
  exact condition_sound hV (p 0) (p 1) (p 2) (p 3) B hW h0 hS hB

end OneYTruth.SchemaSyntaxCertificate

#print axioms OneYTruth.SchemaSyntaxCertificate.query_sound

