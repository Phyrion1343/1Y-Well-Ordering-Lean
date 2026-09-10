import OneYTruth.GraphStepSigmaFormula

/-! Soundness of the actual Sigma-one whole-step query in any transitive
subdomain of L.  No Collection, Separation, or FO absoluteness is used here. -/

namespace OneYTruth.GraphStepSigma

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open GraphStepMatrix UniformSyntaxSource FormulaCode

universe u v

theorem syntaxQueryAt_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat)
    (p : Fin 34 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (p (grammarMap i)).val =
      (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val)
    (h : OneYTruth.realize N (syntaxQueryAt K J) Empty.elim p) :
    (p 18).val = InternalNodes.syntaxCodes (k := k) (ordinalIndexCode (η := η)) := by
  have hh := InternalBoundedIteration.grammarQueryAt_sound hV N hmem SyntaxGrammar.ruleFormula 0
    grammarMap 6 5 6 (18 : Fin 34) p (hp 2) (hp 4) h
  have hz : (p 6).val = (∅ : ZFSet.{u}) := hp 4
  rw [funext hp,hz,GraphStepSyntaxCertificate.ordinal_union_eq κ η hη k] at hh
  exact hh

theorem checks_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat)
    (U : LCarrier.{u}) (p : Fin 34 → ZFCarrier V) (hL : ∀ i, (p i).val ∈ L)
    (hbase : BaseParameters κ U (fun i => ⟨(p i).val,hL i⟩))
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet)
    (hrest : RestChecks (fun i => (p i).val))
    (hsyntax : OneYTruth.realize N (syntaxQueryAt K J) Empty.elim p) :
    (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val := by
  let pL : Tuple LCarrier.{u} 34 := fun i => ⟨(p i).val,hL i⟩
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := hbase
  obtain ⟨hpair,hrel,hstruct,hatomic,hsol⟩ := hrest
  have hpair' := ZFSet.pair_inj.mp (hpair.symm.trans hstage)
  have h16 : pL 16 = natLCarrier k := Subtype.ext hpair'.1
  have h17 : pL 17 = ordinalCarrier η := Subtype.ext hpair'.2
  have hg : ∀ i : Fin 11, (p (grammarMap i)).val =
      (ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i).val := by
    intro i
    have he : pL (grammarMap i) = ConstructibleSyntaxStages.params (ordinalBound κ) (ordinalCarrier η) k i := by
      fin_cases i <;> first | exact h2 | exact h17 | exact h5 | exact h16 | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12
    exact congrArg (fun x : LCarrier.{u} => x.val) he
  have hs := syntaxQueryAt_sound hV N hmem κ η hη k p hg hsyntax
  have hsyntaxMap : (fun i => pL (syntaxMap i)) =
      snoc (UniformSyntaxSource.parameters (ordinalBound κ) (ordinalCarrier η) k) (pL 18) := by
    funext i
    fin_cases i <;> first | exact h2 | exact h17 | exact h5 | exact h16 | exact h6 | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | rfl
  have hfo : FOFormula.Satisfies lCarrierMem UniformSyntaxSource.formula (fun i => pL (syntaxMap i)) := by
    rw [hsyntaxMap,satisfies_ordinal_formula κ η hη k]
    exact hs
  exact GraphStepMatrix.checks_sound κ η hη k U pL
    ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ hstage
    ⟨hpair,hfo,hrel,hstruct,hatomic,hsol⟩

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (U : LCarrier.{u})
    (p : Fin 16 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet)
    (hq : OneYTruth.realize N (query K J) Empty.elim p) :
    (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val := by
  obtain ⟨w,hrest,hsyntax⟩ := (realize_query hV N hmem p).mp hq
  let P := Fin.append p w
  have hL (i : Fin 34) : (P i).val ∈ L := hVL _ (P i).property
  have hb (i : Fin 13) : (⟨(P (Fin.castAdd 21 i)).val,hL (Fin.castAdd 21 i)⟩ : LCarrier.{u}) =
      fixedParameters κ U i := by
    apply Subtype.ext
    change (Fin.append p w (Fin.castAdd 18 (Fin.castAdd 3 i))).val = _
    rw [Fin.append_left]
    exact hp i
  have hbase : BaseParameters κ U (fun i => ⟨(P i).val,hL i⟩) :=
    ⟨hb 0,hb 1,hb 2,congrArg (fun x : LCarrier.{u} => x.val) (hb 3),
      congrArg (fun x : LCarrier.{u} => x.val) (hb 4),
      hb 5,hb 6,hb 7,hb 8,hb 9,hb 10,hb 11,hb 12⟩
  exact checks_sound hV N hmem κ η hη k U P hL hbase hstage hrest hsyntax

end OneYTruth.GraphStepSigma
