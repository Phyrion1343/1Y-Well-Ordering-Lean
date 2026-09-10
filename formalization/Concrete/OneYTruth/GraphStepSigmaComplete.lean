import OneYTruth.GraphStepInternalWitnesses

/-! Completeness supplies every existential witness inside the smaller domain.
In particular it does not transfer the old unrestricted FO formula from L. -/

namespace OneYTruth.GraphStepSigma

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open InternalClosure UniformSyntaxSource GraphStepMatrix FormulaCode

universe u v

theorem query_complete {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (U : LCarrier.{u})
    (p : Fin 16 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet)
    (hS : (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val) :
    OneYTruth.realize N (query K J) Empty.elim p := by
  have hf (i : Fin 13) : (fixedParameters κ U i).val ∈ V := hp i ▸ (p (Fin.castAdd 3 i)).property
  have hU : U.val ∈ V := hf 0
  have hκ : κ.toZFSet ∈ V := hf 1
  have hB : (ordinalBound κ).val ∈ V := hf 2
  have hAssignments : InternalNodes.assignmentCodes U.val ∈ V := hf 3
  have hLookup : AssignmentLookup.lookupSet U.val ∈ V := hf 4
  have hOmega : Ordinal.omega0.toZFSet ∈ V := hf 5
  have hempty : (∅ : ZFSet.{u}) ∈ V := hf 6
  have hηV : η.toZFSet ∈ V := (pair_components_mem hV (hstage ▸ (p 13).property)).2
  have hRaw := canonicalRaw_mem hV N hmem hCol hSep hpair hUnion κ η k U.val
    (p 14).val (p 15).val hU hκ hηV hB (p 14).property (p 15).property hOmega hAssignments hLookup
  let P : Fin 34 → ZFCarrier V := fun i => ⟨canonicalRaw κ η k U.val (p 14).val (p 15).val i,hRaw i⟩
  let w : Fin 18 → ZFCarrier V := fun i => P (Fin.natAdd 16 i)
  have hpref : (fun i : Fin 16 => P (Fin.castAdd 18 i)) = p := by
    funext i
    apply Subtype.ext
    fin_cases i <;> first | exact (hp 0).symm | exact (hp 1).symm | exact (hp 2).symm | exact (hp 3).symm | exact (hp 4).symm | exact (hp 5).symm | exact (hp 6).symm | exact (hp 7).symm | exact (hp 8).symm | exact (hp 9).symm | exact (hp 10).symm | exact (hp 11).symm | exact (hp 12).symm | exact hstage.symm | rfl
  have happ : Fin.append p w = P := by
    rw [← hpref]
    exact Fin.append_castAdd_natAdd
  apply (realize_query hV N hmem p).mpr
  refine ⟨w,?_⟩
  rw [happ]
  constructor
  · let qL : LCarrier.{u} := ⟨(p 14).val,hVL _ (p 14).property⟩
    let SL : LCarrier.{u} := ⟨(p 15).val,hVL _ (p 15).property⟩
    obtain ⟨hpair,_,hrel,hstruct,hatomic,hsol⟩ := canonicalContext_checks κ η hη k U qL SL hS
    exact ⟨hpair,hrel,hstruct,hatomic,hsol⟩
  · have hgr : (fun i => (P (grammarMap i)).val) =
        fun i => (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val := by
      funext i
      fin_cases i <;> rfl
    have hh := InternalBoundedIteration.realize_grammarQueryAt_iff hV N hmem hCol hSep
      hpair hUnion hempty SyntaxGrammar.ruleFormula 0 grammarMap 6 5 6 (18 : Fin 34) P rfl rfl
    have hz : (P 6).val = (∅ : ZFSet.{u}) := rfl
    rw [hgr,hz,GraphStepSyntaxCertificate.ordinal_union_eq κ η hη k] at hh
    exact hh.mpr rfl

theorem realize_query_iff {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (U : LCarrier.{u})
    (p : Fin 16 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet) :
    OneYTruth.realize N (query K J) Empty.elim p ↔
      (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val :=
  ⟨query_sound hV hVL N hmem κ η hη k U p hp hstage,
    query_complete hV hVL N hmem hCol hSep hpair hUnion κ η hη k U p hp hstage⟩

end OneYTruth.GraphStepSigma
