import OneYTruth.SyntaxCertificates
import OneYTruth.CodeUniverseCertificate
import OneYTruth.SigmaFiniteConjunction
import OneYTruth.NaturalTagCertificate
import OneYTruth.SigmaGrammarSourceCertificate

/-! Full, Delta-zero, and Sigma-one syntax sources from primitive parameters alone.
Both the complete code universe and all six constructor tags are quantified
and checked. No correct grammar-parameter tuple is assumed of a candidate. -/

namespace OneYTruth.SyntaxSourceCertificate

open Constructible Constructible.Model Constructible.Delta0Formula
open Constructible.FiniteSequenceZF FirstOrder FirstOrder.Language
open Constructible.IndexedSequenceZF
open InternalClosure InternalNodes ConstructibleCodeUniverse

universe u v w

inductive SyntaxClass | full | delta | sigma

noncomputable def codes (q : SyntaxClass) {k : Nat} {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) : ZFSet.{u} :=
  match q with
  | .full => syntaxCodes (k := k) code
  | .delta => DeltaSyntaxGrammar.deltaCodes (k := k) code
  | .sigma => SigmaComparison.sigmaCodes (k := k) code

noncomputable def oldQuery (q : SyntaxClass) (K : Nat) (J : Type w) : (language K J).BoundedFormula Empty 12 :=
  match q with
  | .full => SyntaxCertificates.syntaxQuery K J
  | .delta => SyntaxCertificates.deltaQuery K J
  | .sigma => SigmaGrammarSourceCertificate.query.{u, w} K J

theorem oldQuery_isSigmaOne (q : SyntaxClass) (K : Nat) (J : Type w) : IsSigmaOne (oldQuery.{u, w} q K J) := by
  cases q
  · exact SyntaxCertificates.syntaxQuery_isSigmaOne K J
  · exact SyntaxCertificates.deltaQuery_isSigmaOne K J
  · exact SigmaGrammarSourceCertificate.query_isSigmaOne K J

theorem oldQuery_sound (q : SyntaxClass) {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {code : I → ZFSet.{u}}
    (A : LCarrier.{u}) (hA : A.val = ZFSet.range code) (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)
    (h : realize N (oldQuery.{u+1, w} q K J) Empty.elim s) : (s 11).val = codes (k := k) q code := by
  cases q
  · exact SyntaxCertificates.syntaxQuery_sound hV N hmem A hA s hp h
  · exact SyntaxCertificates.deltaQuery_sound hV N hmem A hA s hp h
  · exact SigmaGrammarSourceCertificate.query_sound hV N hmem A hA s hp h

theorem realize_oldQuery_iff (q : SyntaxClass) {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {code : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range code)
    (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val) :
    realize N (oldQuery.{u+1, w} q K J) Empty.elim s ↔ (s 11).val = codes (k := k) q code := by
  cases q
  · exact SyntaxCertificates.realize_syntaxQuery_iff hV N hmem hCol hSep hpair hUnion hempty A hA s hp
  · exact SyntaxCertificates.realize_deltaQuery_iff hV N hmem hCol hSep hpair hUnion hempty A hA s hp
  · exact SigmaGrammarSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty A hA s hp

def tagsQuery (K : Nat) (J : Type w) := ofConstructibleDeltaZero K J NaturalTagCertificate.sixTags

def boundQuery (K : Nat) (J : Type w) :=
  renameScope ![0, 1, 2, (11 : Fin 12)] (CodeUniverseCertificate.query K J)

noncomputable def grammarQuery (q : SyntaxClass) (K : Nat) (J : Type w) :=
  renameScope ![11, 0, 1, 3, 2, 5, 6, 7, 8, 9, 10, (4 : Fin 12)] (oldQuery.{u, w} q K J)

theorem tagsQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (tagsQuery K J) :=
  .deltaZero (ofConstructibleDeltaZero_isDeltaZero _ _ _)

theorem boundQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (boundQuery K J) :=
  (CodeUniverseCertificate.query_isSigmaOne K J).renameScope _

theorem grammarQuery_isSigmaOne (q : SyntaxClass) (K : Nat) (J : Type w) : IsSigmaOne (grammarQuery.{u, w} q K J) :=
  (oldQuery_isSigmaOne q K J).renameScope _

noncomputable def sourceAndGrammar (q : SyntaxClass) (K : Nat) (J : Type w) :=
  sigmaConjFormula.{w, u} (boundQuery K J) (grammarQuery.{u, w} q K J)
    (boundQuery_isSigmaOne K J) (grammarQuery_isSigmaOne q K J)

theorem sourceAndGrammar_isSigmaOne (q : SyntaxClass) (K : Nat) (J : Type w) :
    IsSigmaOne (sourceAndGrammar.{u, w} q K J) := sigmaConjFormula_isSigmaOne _ _ _ _

/-- Primitive inputs A, omega, zero, natCode(k), candidate. -/
noncomputable def query (q : SyntaxClass) (K : Nat) (J : Type w) :
    (language K J).BoundedFormula Empty 5 :=
  (sigmaConjFormula.{w, u} (tagsQuery K J) (sourceAndGrammar.{u, w} q K J)
    (tagsQuery_isSigmaOne K J) (sourceAndGrammar_isSigmaOne q K J)).ex.ex.ex.ex.ex.ex.ex

theorem query_isSigmaOne (q : SyntaxClass) (K : Nat) (J : Type w) : IsSigmaOne (query.{u, w} q K J) :=
  .ex (.ex (.ex (.ex (.ex (.ex (.ex (sigmaConjFormula_isSigmaOne _ _ _ _)))))))

def extend {A : Type u} (p : Fin 5 → A) (t1 t2 t3 t4 t5 t6 B : A) : Fin 12 → A :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc p t1) t2) t3) t4) t5) t6) B

theorem realize_query (q : SyntaxClass) {K : Nat} {J : Type w} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 5 → ZFCarrier V)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅) :
    realize N (query.{u+1, w} q K J) Empty.elim p ↔
      ∃ t1 t2 t3 t4 t5 t6 B : ZFCarrier V,
        NaturalTagCertificate.SixTags (fun i => (extend p t1 t2 t3 t4 t5 t6 B i).val) ∧
        realize N (CodeUniverseCertificate.query K J) Empty.elim ![p 0, p 1, p 2, B] ∧
        realize N (oldQuery.{u+1, w} q K J) Empty.elim ![B, p 0, p 1, p 3, p 2, t1, t2, t3, t4, t5, t6, p 4] := by
  simp only [query, realize_scoped_ex]
  apply exists_congr; intro t1
  apply exists_congr; intro t2
  apply exists_congr; intro t3
  apply exists_congr; intro t4
  apply exists_congr; intro t5
  apply exists_congr; intro t6
  apply exists_congr; intro B
  rw [realize_sigmaConjFormula, sourceAndGrammar, realize_sigmaConjFormula,
    boundQuery, grammarQuery, realize_renameScope, realize_renameScope]
  have hb : extend p t1 t2 t3 t4 t5 t6 B ∘ ![0, 1, 2, (11 : Fin 12)] =
      ![p 0, p 1, p 2, B] := by funext i; fin_cases i <;> rfl
  have hg : extend p t1 t2 t3 t4 t5 t6 B ∘ ![11, 0, 1, 3, 2, 5, 6, 7, 8, 9, 10, (4 : Fin 12)] =
      ![B, p 0, p 1, p 3, p 2, t1, t2, t3, t4, t5, t6, p 4] := by funext i; fin_cases i <;> rfl
  change (realize N (tagsQuery K J) Empty.elim (extend p t1 t2 t3 t4 t5 t6 B) ∧ _ ∧ _) ↔ _
  dsimp only [extend] at hb hg
  rw [hb, hg]
  apply and_congr_left
  intro _
  rw [tagsQuery, realize_ofConstructibleDeltaZero_absolute hV N hmem]
  exact NaturalTagCertificate.satisfies_sixTags _ hOmega hZero

theorem query_sound (q : SyntaxClass) {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {code : I → ZFSet.{u}}
    (A : LCarrier.{u}) (hA : A.val = ZFSet.range code) (p : Fin 5 → ZFCarrier V)
    (hAlphabet : (p 0).val = A.val) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (hk : (p 3).val = natCode k)
    (h : realize N (query.{u+1, w} q K J) Empty.elim p) : (p 4).val = codes (k := k) q code := by
  obtain ⟨t1, t2, t3, t4, t5, t6, B, ht, hB, hG⟩ := (realize_query q hV N hmem p hOmega hZero).mp h
  have hb : B.val = (codeUniverse A).val := CodeUniverseCertificate.query_sound hV N hmem
    ![p 0, p 1, p 2, B] hOmega hZero A hAlphabet hB
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  apply oldQuery_sound q hV N hmem A hA ![B, p 0, p 1, p 3, p 2, t1, t2, t3, t4, t5, t6, p 4] _ hG
  intro i
  fin_cases i
  · exact hb
  · exact hAlphabet
  · exact hOmega
  · exact hk
  · exact hZero
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem realize_query_iff (q : SyntaxClass) {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    {code : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range code)
    (p : Fin 5 → ZFCarrier V) (hAlphabet : (p 0).val = A.val)
    (hOmega : (p 1).val = Ordinal.omega0.toZFSet) (hZero : (p 2).val = ∅) (hk : (p 3).val = natCode k) :
    realize N (query.{u+1, w} q K J) Empty.elim p ↔ (p 4).val = codes (k := k) q code := by
  constructor
  · exact query_sound q hV N hmem A hA p hAlphabet hOmega hZero hk
  · intro hout
    have hW : Ordinal.omega0.toZFSet ∈ V := hOmega ▸ (p 1).property
    have hn (m : Nat) : (natCode m : ZFSet.{u}) ∈ V :=
      hV _ hW ((mem_omega_iff_exists_natCode _).mpr ⟨m, rfl⟩)
    let tag (m : Nat) : ZFCarrier V := ⟨natCode m, hn m⟩
    have hBV := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty hW A
      (hAlphabet ▸ (p 0).property)
    let B : ZFCarrier V := ⟨(codeUniverse A).val, hBV⟩
    apply (realize_query q hV N hmem p hOmega hZero).mpr
    refine ⟨tag 1, tag 2, tag 3, tag 4, tag 5, tag 6, B, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
    · exact (CodeUniverseCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
        ![p 0, p 1, p 2, B] hOmega hZero A hAlphabet).mpr rfl
    · apply (realize_oldQuery_iff q hV N hmem hCol hSep hpair hUnion hempty A hA
        ![B, p 0, p 1, p 3, p 2, tag 1, tag 2, tag 3, tag 4, tag 5, tag 6, p 4] ?_).mpr hout
      intro i
      fin_cases i
      · rfl
      · exact hAlphabet
      · exact hOmega
      · exact hk
      · exact hZero
      all_goals rfl

end OneYTruth.SyntaxSourceCertificate

#print axioms OneYTruth.SyntaxSourceCertificate.query_sound
#print axioms OneYTruth.SyntaxSourceCertificate.realize_query_iff
#print axioms OneYTruth.SyntaxSourceCertificate.query_isSigmaOne
