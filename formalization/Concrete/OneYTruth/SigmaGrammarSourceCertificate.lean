import OneYTruth.SyntaxCertificates
import OneYTruth.SigmaFiniteConjunction
import OneYTruth.FiniteCodeFormula

/-! Sigma syntax with its actual Delta-zero initial source and falsum code
quantified internally. The surrounding twelve-parameter interface agrees
with the full/Delta grammar interface, enabling primitive-source assembly. -/

namespace OneYTruth.SigmaGrammarSourceCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FirstOrder FirstOrder.Language
open InternalClosure InternalNodes ConstructibleCodeUniverse FiniteCodeFormula

universe u v w

def falseFormula : Delta0Formula 14 := sequenceEqAt 1 ![4] 13 5 4

def falseQuery (K : Nat) (J : Type w) := ofConstructibleDeltaZero K J falseFormula

def deltaQuery (K : Nat) (J : Type w) :=
  renameScope ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, (12 : Fin 14)] (SyntaxCertificates.deltaQuery K J)

def sigmaQuery (K : Nat) (J : Type w) :=
  renameScope ![0, 2, 4, 13, 9, 10, 6, 7, 12, (11 : Fin 14)] (SyntaxCertificates.sigmaQuery K J)

theorem falseQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (falseQuery K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

theorem deltaQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (deltaQuery K J) :=
  (SyntaxCertificates.deltaQuery_isSigmaOne K J).renameScope _

theorem sigmaQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (sigmaQuery K J) :=
  (SyntaxCertificates.sigmaQuery_isSigmaOne K J).renameScope _

noncomputable def grammarsQuery (K : Nat) (J : Type w) :=
  sigmaConjFormula.{w, u} (deltaQuery K J) (sigmaQuery K J)
    (deltaQuery_isSigmaOne K J) (sigmaQuery_isSigmaOne K J)

theorem grammarsQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (grammarsQuery.{u, w} K J) :=
  sigmaConjFormula_isSigmaOne _ _ _ _

noncomputable def query (K : Nat) (J : Type w) : (language K J).BoundedFormula Empty 12 :=
  (sigmaConjFormula.{w, u} (falseQuery K J) (grammarsQuery.{u, w} K J)
    (falseQuery_isSigmaOne K J) (grammarsQuery_isSigmaOne K J)).ex.ex

theorem query_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (query.{u, w} K J) :=
  .ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _))

theorem realize_query {K : Nat} {J : Type w} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (p : Fin 12 → ZFCarrier V) (hZero : (p 4).val = ∅) (hOne : (p 5).val = natCode 1) :
    realize N (query.{u+1, w} K J) Empty.elim p ↔
      ∃ D F : ZFCarrier V, F.val = sequenceCode [natCode 0] ∧
        realize N (SyntaxCertificates.deltaQuery K J) Empty.elim (Fin.snoc (fun i : Fin 11 => p i.castSucc) D) ∧
        realize N (SyntaxCertificates.sigmaQuery K J) Empty.elim ![p 0, p 2, p 4, F, p 9, p 10, p 6, p 7, D, p 11] := by
  rw [query, realize_scoped_ex]
  apply exists_congr; intro D
  rw [realize_scoped_ex]
  apply exists_congr; intro F
  rw [realize_sigmaConjFormula, grammarsQuery, realize_sigmaConjFormula,
    deltaQuery, sigmaQuery, realize_renameScope, realize_renameScope]
  have hd : Fin.snoc (Fin.snoc p D) F ∘ ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, (12 : Fin 14)] =
      Fin.snoc (fun i : Fin 11 => p i.castSucc) D := by funext i; fin_cases i <;> rfl
  have hs : Fin.snoc (Fin.snoc p D) F ∘ ![0, 2, 4, 13, 9, 10, 6, 7, 12, (11 : Fin 14)] =
      ![p 0, p 2, p 4, F, p 9, p 10, p 6, p 7, D, p 11] := by funext i; fin_cases i <;> rfl
  rw [hd, hs]
  apply and_congr_left
  intro _
  rw [falseQuery, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  have hh := satisfies_sequenceEqAt_natCode 1 (![4] : Fin 1 → Fin 14) 13 5 4
    (Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc p D) F)) hZero hOne
  have he : List.ofFn (fun i : Fin 1 =>
      Constructible.Delta0Formula.val (Fin.snoc (Fin.snoc p D) F) (![4] i)) = [natCode 0] := by
    simp only [List.ofFn_succ, List.ofFn_zero]
    have hz : (p 4).val = natCode 0 := by simpa [natCode] using hZero
    change [(p 4).val] = [natCode 0]
    rw [hz]
  rw [he] at hh
  exact hh

theorem query_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {code : I → ZFSet.{u}}
    (A : LCarrier.{u}) (hA : A.val = ZFSet.range code) (p : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (p i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)
    (h : realize N (query.{u+1, w} K J) Empty.elim p) : (p 11).val = SigmaComparison.sigmaCodes (k := k) code := by
  obtain ⟨D, F, hF, hD, hS⟩ := (realize_query hV N hmem p (hp 4) (hp 5)).mp h
  have hd : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) code :=
    SyntaxCertificates.deltaQuery_sound hV N hmem A hA (Fin.snoc (fun i : Fin 11 => p i.castSucc) D)
      (by intro i; simpa using hp i) hD
  let DL : LCarrier.{u} := ⟨D.val, hd ▸ DeltaSyntaxGrammar.deltaCodes_mem_L (hA ▸ A.property)⟩
  apply SyntaxCertificates.sigmaQuery_sound hV N hmem A DL hA hd
    ![p 0, p 2, p 4, F, p 9, p 10, p 6, p 7, D, p 11] _ rfl hS
  intro i
  fin_cases i
  · exact hp 0
  · exact hp 2
  · exact hp 4
  · exact hF
  · exact hp 9
  · exact hp 10
  · exact hp 6
  · exact hp 7

theorem realize_query_iff {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {code : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range code)
    (p : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (p i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val) :
    realize N (query.{u+1, w} K J) Empty.elim p ↔ (p 11).val = SigmaComparison.sigmaCodes (k := k) code := by
  constructor
  · exact query_sound hV N hmem A hA p hp
  · intro hout
    have hOmega : (p 2).val = Ordinal.omega0.toZFSet := hp 2
    have hAlphabet : (p 1).val = A.val := hp 1
    have hBound : (p 0).val = (codeUniverse A).val := hp 0
    have hW : Ordinal.omega0.toZFSet ∈ V := hOmega ▸ (p 2).property
    have hAV : A.val ∈ V := hAlphabet ▸ (p 1).property
    have hDV := InternalSyntaxCodes.deltaCodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hW A hA hAV
    let DL : LCarrier.{u} := ⟨DeltaSyntaxGrammar.deltaCodes (k := k) code,
      DeltaSyntaxGrammar.deltaCodes_mem_L (hA ▸ A.property)⟩
    let D : ZFCarrier V := ⟨DL.val, hDV⟩
    have hFV : sequenceCode [natCode 0] ∈ V := by
      apply hV _ (hBound ▸ (p 0).property)
      apply ConstructibleCodeUniverse.sequenceCode_mem
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      exact natCode_mem A 0
    let F : ZFCarrier V := ⟨sequenceCode [natCode 0], hFV⟩
    apply (realize_query hV N hmem p (hp 4) (hp 5)).mpr
    refine ⟨D, F, rfl, ?_, ?_⟩
    · exact (SyntaxCertificates.realize_deltaQuery_iff hV N hmem hCol hSep hpair hUnion hempty A hA
        (Fin.snoc (fun i : Fin 11 => p i.castSucc) D) (by intro i; simpa using hp i)).mpr rfl
    · apply (SyntaxCertificates.realize_sigmaQuery_iff hV N hmem hCol hSep hpair hUnion hempty A DL hA rfl
        ![p 0, p 2, p 4, F, p 9, p 10, p 6, p 7, D, p 11] ?_ rfl).mpr hout
      intro i
      fin_cases i
      · exact hp 0
      · exact hp 2
      · exact hp 4
      · rfl
      · exact hp 9
      · exact hp 10
      · exact hp 6
      · exact hp 7

end OneYTruth.SigmaGrammarSourceCertificate

#print axioms OneYTruth.SigmaGrammarSourceCertificate.query_sound
#print axioms OneYTruth.SigmaGrammarSourceCertificate.realize_query_iff
#print axioms OneYTruth.SigmaGrammarSourceCertificate.query_isSigmaOne
