import OneYTruth.SchemaSyntaxCertificate

/-! Internal completeness of the syntax graph certificate. One real
Collection instance bounds the local pure Sigma-one syntax witnesses. -/

namespace OneYTruth.SchemaSyntaxCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open ExternalTower InternalClosure SchemaSyntaxGraph

universe u v

theorem condition_complete {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (W zero S G : ZFCarrier V)
    (hW : W.val = Ordinal.omega0.toZFSet) (h0 : zero.val = ∅)
    (hS : S.val = stageSet κ) (hG : G.val = graph κ) :
    ∃ B : ZFCarrier V, Condition W.val zero.val S.val G.val B.val := by
  let M := pureModel V
  have hMc : HasCollection M := PureSchemaRestriction.collection N M hmem hCol
  have hMs : HasSeparation M := PureSchemaRestriction.separation N M hmem hSep
  have hlocal (x : ZFCarrier V) (hx : x.val ∈ S.val) : ∃ w : Fin 2 → ZFCarrier V,
      Satisfies ZFMem localCertificate.{u}.formula
        (Fin.append (m := 3) (n := 2) (fun i : Fin 3 => ((Fin.snoc ![W, zero] x : Fin 3 → ZFCarrier V) i).val)
          (fun i : Fin 2 => (w i).val)) := by
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hS ▸ hx)
    have hsmem : stageCode s ∈ V := hs ▸ x.property
    have hF := syntaxAt_mem hV M rfl hMc hMs hpair hUnion hempty (hW ▸ W.property) s hsmem
    let F : ZFCarrier V := ⟨syntaxAt s, hF⟩
    let out : ZFCarrier V := ⟨ZFSet.pair (stageCode s) (syntaxAt s), hpair _ hsmem _ hF⟩
    have hq : realize M (recordQuery.{u+1,0} 0 Empty) Empty.elim ![W, zero, x, out] := by
      apply (realize_recordQuery hV M rfl _).mpr
      refine ⟨F, ?_, ?_⟩
      · change ZFSet.pair (stageCode s) (syntaxAt s) = ZFSet.pair x.val (syntaxAt s)
        rw [hs]
      · exact (SchemaSyntaxGraph.realize_query_iff hV M rfl hMc hMs hpair hUnion hempty s
          ![W, zero, x, F] hW h0 hs.symm).mpr rfl
    obtain ⟨B, hB⟩ := localCertificate.{u}.complete hV hpair hUnion hempty M rfl ![W, zero, x, out] hq
    refine ⟨![out, B], ?_⟩
    convert hB using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨D, hD⟩ := UniformWitnessBound.exists_uniform_bound hV N hmem hCol hpair hUnion hempty
    2 localCertificate.{u}.formula ![W, zero] S hlocal
  let B : ZFCarrier V := ⟨ZFSet.sUnion D.val, hUnion _ D.property⟩
  have htotal (z : ZFSet.{u}) (hz : z ∈ S.val) : ∃ out ∈ G.val,
      Satisfies ZFMem localCertificate.{u}.formula ![W.val, zero.val, z, out, B.val] := by
    let x : ZFCarrier V := ⟨z, hV.mem_trans hz S.property⟩
    obtain ⟨w, hw, hm⟩ := (UniformWitnessBound.realize_certificate hV N hmem 2 localCertificate.{u}.formula
      (Fin.snoc ![W, zero] x) D).mp (hD x hz)
    have heval : Fin.append (fun i : Fin 3 => ((Fin.snoc ![W, zero] x : Fin 3 → ZFCarrier V) i).val) w =
        ![W.val, zero.val, z, w 0, w 1] := by
      funext i; fin_cases i <;> rfl
    have hm' : Satisfies ZFMem localCertificate.{u}.formula ![W.val, zero.val, z, w 0, w 1] := heval ▸ hm
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hS ▸ hz)
    let out : ZFCarrier V := ⟨w 0, hV.mem_trans (hw 0) D.property⟩
    let C : ZFCarrier V := ⟨w 1, hV.mem_trans (hw 1) D.property⟩
    have he := local_sound hV s ![W, zero, x, out] C hW h0 hs.symm hm'
    refine ⟨w 0, ?_, ?_⟩
    · rw [hG]
      exact ZFSet.mem_range.mpr ⟨s, he.symm⟩
    · have heC : snoc ![W.val, zero.val, z, w 0] (w 1) = ![W.val, zero.val, z, w 0, w 1] := by
        funext i; fin_cases i <;> rfl
      have heB : snoc ![W.val, zero.val, z, w 0] B.val = ![W.val, zero.val, z, w 0, B.val] := by
        funext i; fin_cases i <;> rfl
      rw [← heB]
      exact localCertificate.{u}.monotone ![W.val, zero.val, z, w 0]
        (fun _ ht => ZFSet.mem_sUnion.mpr ⟨w 1, hw 1, ht⟩) (heC.symm ▸ hm')
  refine ⟨B, htotal, ?_⟩
  intro out hout
  obtain ⟨s, hs⟩ := ZFSet.mem_range.mp (hG ▸ hout)
  have hsmem : stageCode s ∈ S.val := hS ▸ stageCode_mem_stageSet s
  obtain ⟨q, hq, hc⟩ := htotal (stageCode s) hsmem
  let z : ZFCarrier V := ⟨stageCode s, hV.mem_trans hsmem S.property⟩
  let qV : ZFCarrier V := ⟨q, hV.mem_trans hq G.property⟩
  have he : q = out := (local_sound hV s ![W, zero, z, qV] B hW h0 rfl hc).trans hs
  exact ⟨stageCode s, hsmem, he ▸ hc⟩

theorem realize_query_iff {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {κ : Ordinal.{u}} (p : Fin 4 → ZFCarrier V)
    (hW : (p 0).val = Ordinal.omega0.toZFSet) (h0 : (p 1).val = ∅) (hS : (p 2).val = stageSet κ) :
    realize N (query.{u,v} K J) Empty.elim p ↔ (p 3).val = graph κ := by
  constructor
  · exact query_sound hV N hmem p hW h0 hS
  · intro hG
    apply (realize_query hV N hmem p).mpr
    exact condition_complete hV N hmem hCol hSep hpair hUnion hempty (p 0) (p 1) (p 2) (p 3) hW h0 hS hG

end OneYTruth.SchemaSyntaxCertificate

#print axioms OneYTruth.SchemaSyntaxCertificate.realize_query_iff

