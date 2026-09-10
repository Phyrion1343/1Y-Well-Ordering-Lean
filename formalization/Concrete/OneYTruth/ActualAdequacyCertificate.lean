import OneYTruth.SchemaSyntaxCertificateInternal
import OneYTruth.SchemaBundleProjectionInternal
import OneYTruth.ActualTowerQuery
import OneYTruth.DirectAdequacy

/-! A genuine Sigma-one adequacy certificate with four primitive inputs:
the domain U, the ordinal a, omega, and the empty set. Every derived source,
the entire truth graph, and both schema-bundle sets are existentially bound
and checked. Canonicality of U is the separate ordinal-history interface. -/

namespace OneYTruth.ActualAdequacyCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open FirstOrder FirstOrder.Language ExternalTower InternalClosure InternalProducts
open BoundedFilterGraph SchemaBundle SchemaBundleProjection

universe u v

/-- U, a, omega, empty; stages, succ(a), assignments, syntax graph, truth graph,
indexed bundle, local witness bound, bundle, exact field set. -/
def structural : Delta0Formula 13 :=
  .conj (TowerSigma.successorAt 5 1) (.conj (productAt 4 2 5)
    (.conj (SchemaBundleZip.graphFormula.rename ![6,7,8,4,9,10])
      (.conj (SchemaBundleProjection.formula.rename ![4,9,11,12])
        (DirectAdequacy.formula.rename ![2,1,0,11,12]))))

theorem satisfies_structural (p : Fin 13 → ZFSet.{u}) :
    Satisfies ZFMem structural p ↔
      p 5 = insert (p 1) (p 1) ∧ p 4 = pairProduct (p 2) (p 5) ∧
      Satisfies ZFMem SchemaBundleZip.graphFormula ![p 6,p 7,p 8,p 4,p 9,p 10] ∧
      Satisfies ZFMem SchemaBundleProjection.formula ![p 4,p 9,p 11,p 12] ∧
      Satisfies ZFMem DirectAdequacy.formula ![p 2,p 1,p 0,p 11,p 12] := by
  have hzip : (fun i : Fin 6 => p (![6,7,8,4,9,10] i)) = ![p 6,p 7,p 8,p 4,p 9,p 10] := by
    funext i; fin_cases i <;> rfl
  have hproj : (fun i : Fin 4 => p (![4,9,11,12] i)) = ![p 4,p 9,p 11,p 12] := by
    funext i; fin_cases i <;> rfl
  have hadeq : (fun i : Fin 5 => p (![2,1,0,11,12] i)) = ![p 2,p 1,p 0,p 11,p 12] := by
    funext i; fin_cases i <;> rfl
  simp only [structural, Satisfies, TowerSigma.satisfies_successorAt, satisfies_productAt,
    satisfies_rename, hzip, hproj, hadeq]

noncomputable def assignmentAt (K : Nat) (J : Type v) :=
  renameScope ![0,2,3,(6 : Fin 13)] (AssignmentSourceCertificate.query.{u+1,v} K J)

noncomputable def syntaxAt (K : Nat) (J : Type v) :=
  renameScope ![2,3,4,(7 : Fin 13)] (SchemaSyntaxCertificate.query.{u,v} K J)

noncomputable def towerAt (K : Nat) (J : Type v) :=
  renameScope ![0,1,2,3,(8 : Fin 13)] (ActualTowerQuery.query.{u+1,v} K J)

theorem assignmentAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (assignmentAt.{u,v} K J) :=
  (AssignmentSourceCertificate.query_isSigmaOne K J).renameScope _

theorem syntaxAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (syntaxAt.{u,v} K J) :=
  (SchemaSyntaxCertificate.query_isSigmaOne K J).renameScope _

theorem towerAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (towerAt.{u,v} K J) :=
  (ActualTowerQuery.query_isSigmaOne K J).renameScope _

noncomputable def sources (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u+1} (assignmentAt.{u,v} K J)
    (sigmaConjFormula.{v,u+1} (syntaxAt.{u,v} K J) (towerAt.{u,v} K J)
      (syntaxAt_isSigmaOne K J) (towerAt_isSigmaOne K J))
    (assignmentAt_isSigmaOne K J) (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem sources_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (sources.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

noncomputable def body (K : Nat) (J : Type v) :=
  sigmaConjFormula.{v,u+1} (ofConstructibleDeltaZero K J structural) (sources.{u,v} K J)
    (.deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)) (sources_isSigmaOne K J)

theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

theorem realize_body {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 13 → ZFCarrier V) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      Satisfies ZFMem structural (val p) ∧
      realize N (AssignmentSourceCertificate.query.{u+1,v} K J) Empty.elim (p ∘ ![0,2,3,6]) ∧
      realize N (SchemaSyntaxCertificate.query.{u,v} K J) Empty.elim (p ∘ ![2,3,4,7]) ∧
      realize N (ActualTowerQuery.query.{u+1,v} K J) Empty.elim (p ∘ ![0,1,2,3,8]) := by
  rw [body, realize_sigmaConjFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem,
    sources, realize_sigmaConjFormula, realize_sigmaConjFormula,
    assignmentAt, syntaxAt, towerAt, realize_renameScope, realize_renameScope, realize_renameScope]

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 4 :=
  ScopedExistentialBlock.bind 4 9 (body.{u,v} K J)

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  ScopedExistentialBlock.isSigmaOne_bind 4 9 _ (body_isSigmaOne K J)

theorem body_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (a : Ordinal.{u}) (p : Fin 13 → ZFCarrier V)
    (hU : (p 0).val = LStageZF a) (ha : (p 1).val = a.toZFSet)
    (hW : (p 2).val = Ordinal.omega0.toZFSet) (h0 : (p 3).val = ∅)
    (h : realize N (body.{u,v} K J) Empty.elim p) : RootSemantics.Adequate a := by
  obtain ⟨hstruct, hAs, hSyn, hTruth⟩ := (realize_body hV N hmem p).mp h
  obtain ⟨hSucc, hStage, hZip, hProjection, hAdeq⟩ := (satisfies_structural (val p)).mp hstruct
  change (p 5).val = insert (p 1).val (p 1).val at hSucc
  change (p 4).val = pairProduct (p 2).val (p 5).val at hStage
  have hS : (p 4).val = stageSet a := by
    rw [hStage, hW, hSucc, ha, stageSet_eq_product, Ordinal.toZFSet_succ]
  let U : LCarrier.{u} := ⟨LStageZF a, LStageZF_mem_L a⟩
  have hA : (p 6).val = InternalNodes.assignmentCodes (LStageZF a) :=
    AssignmentSourceCertificate.query_sound hV N hmem U (p ∘ ![0,2,3,6]) hU hW h0 hAs
  have hSG : (p 7).val = SchemaSyntaxGraph.graph a :=
    SchemaSyntaxCertificate.query_sound hV N hmem (p ∘ ![2,3,4,7]) hW h0 hS hSyn
  have hTG : (p 8).val = @ExternalTower.graph a (LStageZF a) :=
    ActualTowerQuery.query_sound hV hVL N hmem a U (p ∘ ![0,1,2,3,8]) hU ha hW h0 hTruth
  change Satisfies ZFMem SchemaBundleZip.graphFormula
    ![(p 6).val,(p 7).val,(p 8).val,(p 4).val,(p 9).val,(p 10).val] at hZip
  rw [hA, hSG, hTG, hS] at hZip
  have hG := SchemaBundleZip.satisfies_graphFormula_sound (LStageZF a) (p 9).val (p 10).val hZip
  change Satisfies ZFMem SchemaBundleProjection.formula
    ![(p 4).val,(p 9).val,(p 11).val,(p 12).val] at hProjection
  rw [hS, hG, SchemaBundleProjection.satisfies_iff_canonical] at hProjection
  change Satisfies ZFMem DirectAdequacy.formula
    ![(p 2).val,(p 1).val,(p 0).val,(p 11).val,(p 12).val] at hAdeq
  rw [hW, ha, hU, hProjection.1, hProjection.2] at hAdeq
  exact (DirectAdequacy.satisfies_formula a).mp hAdeq

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (a : Ordinal.{u}) (p : Fin 4 → ZFCarrier V)
    (hU : (p 0).val = LStageZF a) (ha : (p 1).val = a.toZFSet)
    (hW : (p 2).val = Ordinal.omega0.toZFSet) (h0 : (p 3).val = ∅)
    (h : realize N (query.{u,v} K J) Empty.elim p) : RootSemantics.Adequate a := by
  obtain ⟨w, hw⟩ := (ScopedExistentialBlock.realize_bind N 4 9 (body.{u,v} K J) p).mp h
  exact body_sound hV hVL N hmem a (Fin.append p w) hU ha hW h0 hw

end OneYTruth.ActualAdequacyCertificate

#print axioms OneYTruth.ActualAdequacyCertificate.query_isSigmaOne
#print axioms OneYTruth.ActualAdequacyCertificate.query_sound
