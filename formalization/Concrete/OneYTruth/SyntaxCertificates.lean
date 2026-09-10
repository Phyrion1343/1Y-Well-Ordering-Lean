import OneYTruth.InternalSyntaxCodes
import OneYTruth.BoundedGrammarSoundness

/-! # Genuine Sigma-one candidate checks for all three syntax classes

Parameters contain the actual alphabet and the previously certified finite
code universe. The Sigma-one grammar additionally starts from the previously
certified Delta-zero code set. Soundness of any candidate requires no schema.
-/

namespace OneYTruth.SyntaxCertificates

open Constructible Constructible.Model Constructible.Delta0Formula
open InternalNodes InternalClosure InternalBoundedIteration ConstructibleCodeUniverse

universe u v w

theorem syntax_union_eq {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) :
    ZFSet.sUnion (InternalIteration.family
      (step SyntaxGrammar.ruleFormula 0
        (fun i => (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)) ∅) =
      syntaxCodes (k := k) indexCode :=
  (InternalBoundedIteration.union_eq_L SyntaxGrammar.ruleFormula 0
    (ConstructibleSyntaxStages.params (codeUniverse A) A k) emptyLCarrier).trans
    (ConstructibleSyntaxStages.allStages_eq_syntaxCodes A hA)

theorem delta_union_eq {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) :
    ZFSet.sUnion (InternalIteration.family
      (step DeltaSyntaxGrammar.ruleFormula 0
        (fun i => (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)) ∅) =
      DeltaSyntaxGrammar.deltaCodes (k := k) indexCode :=
  (InternalBoundedIteration.union_eq_L DeltaSyntaxGrammar.ruleFormula 0
    (ConstructibleSyntaxStages.params (codeUniverse A) A k) emptyLCarrier).trans
    (DeltaSyntaxGrammar.allStages_eq_deltaCodes A hA)

theorem sigma_union_eq {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A D : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode) :
    ZFSet.sUnion (InternalIteration.family
      (step SigmaSyntaxGrammar.ruleFormula 0 (fun i => (SigmaSyntaxGrammar.params (codeUniverse A) i).val)) D.val) =
      SigmaComparison.sigmaCodes (k := k) indexCode :=
  (InternalBoundedIteration.union_eq_L SigmaSyntaxGrammar.ruleFormula 0
    (SigmaSyntaxGrammar.params (codeUniverse A)) D).trans
    (SigmaSyntaxGrammar.allStages_eq_sigmaCodes A D hA hD)

def syntaxQuery (K : Nat) (J : Type w) :=
  grammarQueryAt K J SyntaxGrammar.ruleFormula 0 Fin.castSucc 4 2 4 (11 : Fin 12)

def deltaQuery (K : Nat) (J : Type w) :=
  grammarQueryAt K J DeltaSyntaxGrammar.ruleFormula 0 Fin.castSucc 4 2 4 (11 : Fin 12)

def sigmaQuery (K : Nat) (J : Type w) :=
  grammarQueryAt K J SigmaSyntaxGrammar.ruleFormula 0 (fun i => i.castSucc.castSucc) 8 1 2 (9 : Fin 10)

theorem syntaxQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (syntaxQuery K J) :=
  grammarQueryAt_isSigmaOne K J _ _ _ _ _ _ _

theorem deltaQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (deltaQuery K J) :=
  grammarQueryAt_isSigmaOne K J _ _ _ _ _ _ _

theorem sigmaQuery_isSigmaOne (K : Nat) (J : Type w) : IsSigmaOne (sigmaQuery K J) :=
  grammarQueryAt_isSigmaOne K J _ _ _ _ _ _ _

theorem syntaxQuery_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {indexCode : I → ZFSet.{u}}
    (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)
    (h : OneYTruth.realize N (syntaxQuery K J) Empty.elim s) : (s 11).val = syntaxCodes (k := k) indexCode := by
  have hh := grammarQueryAt_sound hV N hmem SyntaxGrammar.ruleFormula 0 Fin.castSucc
    4 2 4 (11 : Fin 12) s (hp 2) (hp 4) h
  have hZero : (s 4).val = (∅ : ZFSet) := hp 4
  rw [funext hp, hZero, syntax_union_eq A hA] at hh
  exact hh

theorem deltaQuery_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {indexCode : I → ZFSet.{u}}
    (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode) (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val)
    (h : OneYTruth.realize N (deltaQuery K J) Empty.elim s) :
    (s 11).val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode := by
  have hh := grammarQueryAt_sound hV N hmem DeltaSyntaxGrammar.ruleFormula 0 Fin.castSucc
    4 2 4 (11 : Fin 12) s (hp 2) (hp 4) h
  have hZero : (s 4).val = (∅ : ZFSet) := hp 4
  rw [funext hp, hZero, delta_union_eq A hA] at hh
  exact hh

theorem sigmaQuery_sound {k K : Nat} {I : Type v} {J : Type w} [Small.{u} I]
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) {indexCode : I → ZFSet.{u}}
    (A D : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode) (s : Fin 10 → ZFCarrier V)
    (hp : ∀ i : Fin 8, (s i.castSucc.castSucc).val = (SigmaSyntaxGrammar.params (codeUniverse A) i).val)
    (hinit : (s 8).val = D.val) (h : OneYTruth.realize N (sigmaQuery K J) Empty.elim s) :
    (s 9).val = SigmaComparison.sigmaCodes (k := k) indexCode := by
  have hh := grammarQueryAt_sound hV N hmem SigmaSyntaxGrammar.ruleFormula 0
    (fun i => i.castSucc.castSucc) 8 1 2 (9 : Fin 10) s (hp 1) (hp 2) h
  rw [funext hp, hinit, sigma_union_eq A D hA hD] at hh
  exact hh

section Completeness

variable {K : Nat} {J : Type w} {V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)

include hV N hmem hCol hSep hpair hUnion hempty

theorem realize_syntaxQuery_iff {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val) :
    OneYTruth.realize N (syntaxQuery K J) Empty.elim s ↔ (s 11).val = syntaxCodes (k := k) indexCode := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    SyntaxGrammar.ruleFormula 0 Fin.castSucc 4 2 4 (11 : Fin 12) s (hp 2) (hp 4)
  have hZero : (s 4).val = (∅ : ZFSet) := hp 4
  rw [funext hp, hZero, syntax_union_eq A hA] at hh
  exact hh

theorem realize_deltaQuery_iff {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (s : Fin 12 → ZFCarrier V)
    (hp : ∀ i : Fin 11, (s i.castSucc).val = (ConstructibleSyntaxStages.params (codeUniverse A) A k i).val) :
    OneYTruth.realize N (deltaQuery K J) Empty.elim s ↔
      (s 11).val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    DeltaSyntaxGrammar.ruleFormula 0 Fin.castSucc 4 2 4 (11 : Fin 12) s (hp 2) (hp 4)
  have hZero : (s 4).val = (∅ : ZFSet) := hp 4
  rw [funext hp, hZero, delta_union_eq A hA] at hh
  exact hh

theorem realize_sigmaQuery_iff {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A D : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hD : D.val = DeltaSyntaxGrammar.deltaCodes (k := k) indexCode) (s : Fin 10 → ZFCarrier V)
    (hp : ∀ i : Fin 8, (s i.castSucc.castSucc).val = (SigmaSyntaxGrammar.params (codeUniverse A) i).val)
    (hinit : (s 8).val = D.val) : OneYTruth.realize N (sigmaQuery K J) Empty.elim s ↔
      (s 9).val = SigmaComparison.sigmaCodes (k := k) indexCode := by
  have hh := realize_grammarQueryAt_iff hV N hmem hCol hSep hpair hUnion hempty
    SigmaSyntaxGrammar.ruleFormula 0 (fun i => i.castSucc.castSucc) 8 1 2 (9 : Fin 10) s (hp 1) (hp 2)
  rw [funext hp, hinit, sigma_union_eq A D hA hD] at hh
  exact hh

end Completeness
end OneYTruth.SyntaxCertificates

#print axioms OneYTruth.SyntaxCertificates.syntaxQuery_sound
#print axioms OneYTruth.SyntaxCertificates.sigmaQuery_sound
#print axioms OneYTruth.SyntaxCertificates.realize_sigmaQuery_iff
#print axioms OneYTruth.SyntaxCertificates.sigmaQuery_isSigmaOne
