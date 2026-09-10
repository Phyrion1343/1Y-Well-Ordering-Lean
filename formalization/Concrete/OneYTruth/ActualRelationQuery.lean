import OneYTruth.ActualStageQuery
import OneYTruth.ActualTruthQuery
import OneYTruth.SourcePairComparison
import OneYTruth.FiniteSigmaChecks
import OneYTruth.InternalActualTruth

/-! The actual internal R relation from ordinal codes alone. Canonical
domains and both canonical truth sets are existentially checked. -/

namespace OneYTruth.ActualRelationQuery

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language RootSemantics ExternalTower InternalClosure
open SourceEndpointComparison

universe u v

/-- eta,a,b,omega,zero,k; La,Lb,Sat_a,Sat_b. -/
noncomputable def checks (K : Nat) (J : Type v) :
    Fin 5 → (language K J).BoundedFormula Empty 10 :=
  ![renameScope ![1,3,4,(6 : Fin 10)] (ActualStageQuery.query.{u,v} K J),
    renameScope ![2,3,4,(7 : Fin 10)] (ActualStageQuery.query.{u,v} K J),
    renameScope ![6,1,3,4,5,0,(8 : Fin 10)] (ActualTruthQuery.query.{u+1,v} K J),
    renameScope ![7,2,3,4,5,0,(9 : Fin 10)] (ActualTruthQuery.query.{u+1,v} K J),
    renameScope ![0,6,3,4,5,8,(9 : Fin 10)] (SourcePairComparison.query.{u+1,v} K J)]

theorem checks_isSigmaOne (K : Nat) (J : Type v) : ∀ i, IsSigmaOne (checks.{u,v} K J i) := by
  intro i
  fin_cases i <;> first
    | exact (ActualStageQuery.query_isSigmaOne K J).renameScope _
    | exact (ActualTruthQuery.query_isSigmaOne K J).renameScope _
    | exact (SourcePairComparison.query_isSigmaOne K J).renameScope _

noncomputable def body (K : Nat) (J : Type v) :=
  FiniteSigmaChecks.formula.{v,u+1} (checks.{u,v} K J) (checks_isSigmaOne K J)
theorem body_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (body.{u,v} K J) :=
  FiniteSigmaChecks.formula_isSigmaOne _ _

theorem realize_body {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (p : Fin 10 → ZFCarrier V) :
    realize N (body.{u,v} K J) Empty.elim p ↔
      realize N (ActualStageQuery.query.{u,v} K J) Empty.elim ![p 1,p 3,p 4,p 6] ∧
      realize N (ActualStageQuery.query.{u,v} K J) Empty.elim ![p 2,p 3,p 4,p 7] ∧
      realize N (ActualTruthQuery.query.{u+1,v} K J) Empty.elim ![p 6,p 1,p 3,p 4,p 5,p 0,p 8] ∧
      realize N (ActualTruthQuery.query.{u+1,v} K J) Empty.elim ![p 7,p 2,p 3,p 4,p 5,p 0,p 9] ∧
      realize N (SourcePairComparison.query.{u+1,v} K J) Empty.elim ![p 0,p 6,p 3,p 4,p 5,p 8,p 9] := by
  rw [body,FiniteSigmaChecks.realize_formula]
  have e0 : p ∘ ![1,3,4,(6 : Fin 10)] = ![p 1,p 3,p 4,p 6] := by funext i; fin_cases i <;> rfl
  have e1 : p ∘ ![2,3,4,(7 : Fin 10)] = ![p 2,p 3,p 4,p 7] := by funext i; fin_cases i <;> rfl
  have e2 : p ∘ ![6,1,3,4,5,0,(8 : Fin 10)] = ![p 6,p 1,p 3,p 4,p 5,p 0,p 8] := by
    funext i; fin_cases i <;> rfl
  have e3 : p ∘ ![7,2,3,4,5,0,(9 : Fin 10)] = ![p 7,p 2,p 3,p 4,p 5,p 0,p 9] := by
    funext i; fin_cases i <;> rfl
  have e4 : p ∘ ![0,6,3,4,5,8,(9 : Fin 10)] = ![p 0,p 6,p 3,p 4,p 5,p 8,p 9] := by
    funext i; fin_cases i <;> rfl
  have h0 := realize_renameScope N ![1,3,4,(6 : Fin 10)] (ActualStageQuery.query.{u,v} K J) p
  have h1 := realize_renameScope N ![2,3,4,(7 : Fin 10)] (ActualStageQuery.query.{u,v} K J) p
  have h2 := realize_renameScope N ![6,1,3,4,5,0,(8 : Fin 10)] (ActualTruthQuery.query.{u+1,v} K J) p
  have h3 := realize_renameScope N ![7,2,3,4,5,0,(9 : Fin 10)] (ActualTruthQuery.query.{u+1,v} K J) p
  have h4 := realize_renameScope N ![0,6,3,4,5,8,(9 : Fin 10)] (SourcePairComparison.query.{u+1,v} K J) p
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  constructor
  · intro h
    exact ⟨h0.mp (h 0),h1.mp (h 1),h2.mp (h 2),h3.mp (h 3),h4.mp (h 4)⟩
  · rintro ⟨g0,g1,g2,g3,g4⟩ i
    fin_cases i
    · exact h0.mpr g0
    · exact h1.mpr g1
    · exact h2.mpr g2
    · exact h3.mpr g3
    · exact h4.mpr g4

theorem body_sound {k K : Nat} {J : Type v} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    {V : ZFSet.{u}} (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 10 → ZFCarrier V)
    (hη : (p 0).val = η.toZFSet) (ha : (p 1).val = a.toZFSet) (hb : (p 2).val = b.toZFSet)
    (hOmega : (p 3).val = Ordinal.omega0.toZFSet) (hZero : (p 4).val = ∅)
    (hk : (p 5).val = natCode k) (h : realize N (body.{u,v} K J) Empty.elim p) : R k η a b := by
  obtain ⟨hUa,hUb,hSa,hSb,hR⟩ := (realize_body N p).mp h
  have hA := ActualStageQuery.query_sound hV hVL N hmem a ![p 1,p 3,p 4,p 6] ha hOmega hZero hUa
  have hB := ActualStageQuery.query_sound hV hVL N hmem b ![p 2,p 3,p 4,p 7] hb hOmega hZero hUb
  have hS := ActualTruthQuery.query_sound hV hVL N hmem a (stageDomain a) (k,⟨η,hηa⟩)
    ![p 6,p 1,p 3,p 4,p 5,p 0,p 8] hA ha hOmega hZero hk hη hSa
  have hT := ActualTruthQuery.query_sound hV hVL N hmem b (stageDomain b) (k,⟨η,hηa.trans hab.le⟩)
    ![p 7,p 2,p 3,p 4,p 5,p 0,p 9] hB hb hOmega hZero hk hη hSb
  exact SourcePairComparison.sound_R hηa hab hV N hmem
    ![p 0,p 6,p 3,p 4,p 5,p 8,p 9] hη hA hOmega hZero hk hS hT hR

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 6 :=
  existsSuffix 4 (body.{u,v} K J)
theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  existsSuffix_isSigmaOne _ (body_isSigmaOne K J)

theorem query_sound {k K : Nat} {J : Type v} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    {V : ZFSet.{u}} (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 6 → ZFCarrier V)
    (hη : (p 0).val = η.toZFSet) (ha : (p 1).val = a.toZFSet) (hb : (p 2).val = b.toZFSet)
    (hOmega : (p 3).val = Ordinal.omega0.toZFSet) (hZero : (p 4).val = ∅)
    (hk : (p 5).val = natCode k) (h : realize N (query.{u,v} K J) Empty.elim p) : R k η a b := by
  obtain ⟨w,hw⟩ := (realize_existsSuffix (m := 4) N (body.{u,v} K J) p).mp h
  exact body_sound hηa hab hV hVL N hmem (Fin.append p w) hη ha hb hOmega hZero hk hw

theorem body_complete {k K : Nat} {J : Type v} {η a b β : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    (hβ : Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (p : Fin 10 → ZFCarrier (LStageZF β))
    (hη : (p 0).val = η.toZFSet) (ha : (p 1).val = a.toZFSet) (hb : (p 2).val = b.toZFSet)
    (hOmega : (p 3).val = Ordinal.omega0.toZFSet) (hZero : (p 4).val = ∅)
    (hk : (p 5).val = natCode k) (hUa : (p 6).val = LStageZF a) (hUb : (p 7).val = LStageZF b)
    (hSa : (p 8).val = truth (LStageZF a) (k,⟨η,hηa⟩))
    (hSb : (p 9).val = truth (LStageZF b) (k,⟨η,hηa.trans hab.le⟩))
    (hR : R k η a b) : realize N (body.{u,v} K J) Empty.elim p := by
  apply (realize_body N p).mpr
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (ActualStageQuery.realize_query_iff hβ N hmem a ![p 1,p 3,p 4,p 6] ha hOmega hZero).mpr hUa
  · exact (ActualStageQuery.realize_query_iff hβ N hmem b ![p 2,p 3,p 4,p 7] hb hOmega hZero).mpr hUb
  · exact (ActualTruthQuery.realize_query_iff hβ N hmem hCol hSep (stageDomain a) (k,⟨η,hηa⟩)
      ![p 6,p 1,p 3,p 4,p 5,p 0,p 8] hUa ha hOmega hZero hk hη).mpr hSa
  · exact (ActualTruthQuery.realize_query_iff hβ N hmem hCol hSep (stageDomain b) (k,⟨η,hηa.trans hab.le⟩)
      ![p 7,p 2,p 3,p 4,p 5,p 0,p 9] hUb hb hOmega hZero hk hη).mpr hSb
  · exact (SourcePairComparison.realize_iff_R hηa hab (LStageZF_isTransitive β) N hmem hCol hSep
      (fun _ hx _ hy => orderedPair_mem_LStageZF_of_isSuccLimit hβ.2.1 hx hy)
      (fun _ hx => sUnion_mem_LStageZF_of_isSuccLimit hβ.2.1 hx)
      (hZero ▸ (p 4).property) ![p 0,p 6,p 3,p 4,p 5,p 8,p 9] hη hUa hOmega hZero hk hSa hSb).mpr hR

theorem realize_query_iff {k K : Nat} {J : Type v} {η a b β : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    (hβ : Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (p : Fin 6 → ZFCarrier (LStageZF β))
    (hη : (p 0).val = η.toZFSet) (ha : (p 1).val = a.toZFSet) (hb : (p 2).val = b.toZFSet)
    (hOmega : (p 3).val = Ordinal.omega0.toZFSet) (hZero : (p 4).val = ∅)
    (hk : (p 5).val = natCode k) :
    realize N (query.{u,v} K J) Empty.elim p ↔ R k η a b := by
  constructor
  · exact query_sound hηa hab (LStageZF_isTransitive β)
      (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)) N hmem p hη ha hb hOmega hZero hk
  · intro hR
    have haβ : a < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (ha ▸ (p 1).property)
    have hbβ : b < β := MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF
      (hb ▸ (p 2).property)
    let Ua : ZFCarrier (LStageZF β) := ⟨LStageZF a,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 haβ⟩
    let Ub : ZFCarrier (LStageZF β) := ⟨LStageZF b,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 hbβ⟩
    let Sa : ZFCarrier (LStageZF β) := ⟨truth (LStageZF a) (k,⟨η,hηa⟩),
      truth_LStage_mem_of_adequate hβ haβ (k,⟨η,hηa⟩)⟩
    let Sb : ZFCarrier (LStageZF β) := ⟨truth (LStageZF b) (k,⟨η,hηa.trans hab.le⟩),
      truth_LStage_mem_of_adequate hβ hbβ (k,⟨η,hηa.trans hab.le⟩)⟩
    let w : Fin 4 → ZFCarrier (LStageZF β) := ![Ua,Ub,Sa,Sb]
    apply (realize_existsSuffix (m := 4) N (body.{u,v} K J) p).mpr
    exact ⟨w,body_complete hηa hab hβ N hmem hCol hSep (Fin.append p w)
      hη ha hb hOmega hZero hk rfl rfl rfl rfl hR⟩

end OneYTruth.ActualRelationQuery

#print axioms OneYTruth.ActualRelationQuery.query_isSigmaOne
#print axioms OneYTruth.ActualRelationQuery.query_sound
#print axioms OneYTruth.ActualRelationQuery.realize_query_iff
