import OneYTruth.ActualAdequacyCertificate

/-! Every witness of the four-input adequacy certificate is supplied inside
an adequate larger stage. No source, truth graph, or schema bundle is assumed
to be a previously normalized candidate. -/

namespace OneYTruth.ActualAdequacyCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open ExternalTower InternalClosure InternalProducts InternalNodes SchemaBundle SchemaBundleProjection

universe u v

theorem query_complete {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (a : Ordinal.{u}) (p : Fin 4 → ZFCarrier (LStageZF β))
    (hU : (p 0).val = LStageZF a) (ha : (p 1).val = a.toZFSet)
    (hW : (p 2).val = Ordinal.omega0.toZFSet) (h0 : (p 3).val = ∅)
    (hAdeq : RootSemantics.Adequate a) : realize N (query.{u,v} K J) Empty.elim p := by
  let V := LStageZF β
  have hV := LStageZF_isTransitive β
  have hab : a < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
    (ha ▸ (p 1).property)
  have hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V :=
    fun _ hx _ hy => orderedPair_mem_LStageZF_of_isSuccLimit hβ.2.1 hx hy
  have hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V :=
    fun _ hx => sUnion_mem_LStageZF_of_isSuccLimit hβ.2.1 hx
  have hzero : (∅ : ZFSet.{u}) ∈ V := h0 ▸ (p 3).property
  have hOmega : Ordinal.omega0.toZFSet ∈ V := hW ▸ (p 2).property
  let U : LCarrier.{u} := ⟨LStageZF a, LStageZF_mem_L a⟩
  have hUV : U.val ∈ V := by
    change LStageZF a ∈ V
    exact hU ▸ (p 0).property
  have hS : stageSet a ∈ V := stageSet_mem_LStage hβ.2.1 hβ.1 hab
  have hSucc : insert a.toZFSet a.toZFSet ∈ V :=
    insert_mem hV hpair hUnion (ha ▸ (p 1).property) (ha ▸ (p 1).property)
  have hA : assignmentCodes (LStageZF a) ∈ V :=
    AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hzero hOmega U hUV
  have hSG : SchemaSyntaxGraph.graph a ∈ V :=
    SchemaSyntaxGraph.graph_mem hV N hmem hCol hSep hpair hUnion hzero hOmega a hS
  have hTG : @ExternalTower.graph a (LStageZF a) ∈ V := graph_mem_of_adequate hβ hab hUV
  have hG := SchemaBundleZip.indexedBundle_mem hV N hmem hCol hSep hpair hUnion (LStageZF a) hS hA hSG hTG
  have hBC := SchemaBundleProjection.bundle_and_fieldBound_mem hV N hmem hCol hSep hpair hUnion hzero
    (LStageZF a) hS hA hSG hTG
  obtain ⟨Z, hZ⟩ := SchemaBundleZip.exists_graphFormula hV N hmem hCol hSep hpair hUnion hzero
    (LStageZF a) hS hA hSG hTG
  let w : Fin 9 → ZFCarrier V := ![⟨stageSet a,hS⟩,⟨insert a.toZFSet a.toZFSet,hSucc⟩,
    ⟨assignmentCodes (LStageZF a),hA⟩,⟨SchemaSyntaxGraph.graph a,hSG⟩,
    ⟨@ExternalTower.graph a (LStageZF a),hTG⟩,⟨@indexedBundle a (LStageZF a),hG⟩,Z,
    ⟨@bundle a (LStageZF a),hBC.1⟩,⟨@fieldBound a (LStageZF a),hBC.2⟩]
  let q : Fin 13 → ZFCarrier V := Fin.append p w
  have hq : val q = ![LStageZF a,a.toZFSet,Ordinal.omega0.toZFSet,∅,stageSet a,
      insert a.toZFSet a.toZFSet,assignmentCodes (LStageZF a),SchemaSyntaxGraph.graph a,
      @ExternalTower.graph a (LStageZF a),@indexedBundle a (LStageZF a),Z.val,
      @bundle a (LStageZF a),@fieldBound a (LStageZF a)] := by
    funext i
    fin_cases i <;> first | exact hU | exact ha | exact hW | exact h0 | rfl
  apply (ScopedExistentialBlock.realize_bind N 4 9 (body.{u,v} K J) p).mpr
  refine ⟨w,(realize_body hV N hmem q).mpr ⟨?_,?_,?_,?_⟩⟩
  · rw [hq,satisfies_structural]
    refine ⟨rfl,?_,hZ,?_,?_⟩
    · change stageSet a = pairProduct Ordinal.omega0.toZFSet (insert a.toZFSet a.toZFSet)
      rw [stageSet_eq_product,Ordinal.toZFSet_succ]
    · exact (SchemaBundleProjection.satisfies_iff_canonical (LStageZF a) _ _).mpr ⟨rfl,rfl⟩
    · exact (DirectAdequacy.satisfies_formula a).mpr hAdeq
  · exact (AssignmentSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hzero U
      (q ∘ ![0,2,3,6]) hU hW h0).mpr rfl
  · exact (SchemaSyntaxCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hzero
      (q ∘ ![2,3,4,7]) hW h0 rfl).mpr rfl
  · exact (ActualTowerQuery.realize_query_iff hβ N hmem hCol hSep U
      (q ∘ ![0,1,2,3,8]) hU ha hW h0).mpr rfl

theorem realize_query_iff {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (a : Ordinal.{u}) (p : Fin 4 → ZFCarrier (LStageZF β))
    (hU : (p 0).val = LStageZF a) (ha : (p 1).val = a.toZFSet)
    (hW : (p 2).val = Ordinal.omega0.toZFSet) (h0 : (p 3).val = ∅) :
    realize N (query.{u,v} K J) Empty.elim p ↔ RootSemantics.Adequate a := by
  constructor
  · exact query_sound (LStageZF_isTransitive β)
      (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)) N hmem a p hU ha hW h0
  · exact query_complete hβ N hmem hCol hSep a p hU ha hW h0

end OneYTruth.ActualAdequacyCertificate

#print axioms OneYTruth.ActualAdequacyCertificate.realize_query_iff
