import OneYTruth.InternalCodeUniverse
import OneYTruth.InternalBoundedIteration
import OneYTruth.SigmaSyntaxCodes

/-! # Complete genuine syntax classes inside an adequate transitive domain -/

namespace OneYTruth.InternalSyntaxCodes

open Constructible Constructible.FiniteSequenceZF Constructible.Model
open InternalClosure InternalNodes ConstructibleCodeUniverse

universe u v w

variable {K : Nat} {J : Type w} {V : ZFSet.{u}} (hV : V.IsTransitive)
  (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
  (hCol : HasCollection N) (hSep : HasSeparation N)
  (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
  (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
  (hOmega : Ordinal.omega0.toZFSet ∈ V)

include hV hempty hOmega in
theorem grammar_params_mem (A B : LCarrier.{u}) (hA : A.val ∈ V) (hB : B.val ∈ V) (k : Nat) :
    ∀ i, (ConstructibleSyntaxStages.params B A k i).val ∈ V := by
  have hNat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩) hOmega
  intro i
  fin_cases i
  · exact hB
  · exact hA
  · exact hOmega
  · exact hNat k
  · exact hempty
  all_goals exact hNat _

include hV N hmem hCol hSep hpair hUnion hempty hOmega

theorem syntaxCodes_mem {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hAV : A.val ∈ V) : syntaxCodes (k := k) indexCode ∈ V := by
  rw [← ConstructibleSyntaxStages.allStages_eq_syntaxCodes A hA]
  have hB := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty hOmega A hAV
  exact InternalBoundedIteration.allStages_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    SyntaxGrammar.ruleFormula 0 (ConstructibleSyntaxStages.params (codeUniverse A) A k)
    (grammar_params_mem hV hempty hOmega A (codeUniverse A) hAV hB k) emptyLCarrier hempty

theorem deltaCodes_mem {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hAV : A.val ∈ V) : DeltaSyntaxGrammar.deltaCodes (k := k) indexCode ∈ V := by
  rw [← DeltaSyntaxGrammar.allStages_eq_deltaCodes A hA]
  have hB := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty hOmega A hAV
  exact InternalBoundedIteration.allStages_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    DeltaSyntaxGrammar.ruleFormula 0 (ConstructibleSyntaxStages.params (codeUniverse A) A k)
    (grammar_params_mem hV hempty hOmega A (codeUniverse A) hAV hB k) emptyLCarrier hempty

theorem sigmaCodes_mem {k : Nat} {I : Type v} [Small.{u} I]
    {indexCode : I → ZFSet.{u}} (A : LCarrier.{u}) (hA : A.val = ZFSet.range indexCode)
    (hAV : A.val ∈ V) : SigmaComparison.sigmaCodes (k := k) indexCode ∈ V := by
  let D : LCarrier.{u} := ⟨DeltaSyntaxGrammar.deltaCodes (k := k) indexCode,
    DeltaSyntaxGrammar.deltaCodes_mem_L (hA ▸ A.property)⟩
  have hD : D.val ∈ V := deltaCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega A hA hAV
  rw [← SigmaSyntaxGrammar.allStages_eq_sigmaCodes A D hA rfl]
  have hB := InternalCodeUniverse.codeUniverse_mem hV N hmem hCol hSep hpair hUnion hempty hOmega A hAV
  have hNat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n, rfl⟩) hOmega
  have hf : (FiniteSequenceZF.sequenceCode [natCode 0] : ZFSet.{u}) ∈ V := by
    change ZFSet.pair (natCode 1) (ZFSet.pair (natCode 0) ∅) ∈ V
    exact hpair _ (hNat 1) _ (hpair _ (hNat 0) _ hempty)
  apply InternalBoundedIteration.allStages_mem hV N hmem hCol hSep hpair hUnion hempty hOmega
    SigmaSyntaxGrammar.ruleFormula 0 (SigmaSyntaxGrammar.params (codeUniverse A)) _ D hD
  intro i
  fin_cases i
  · exact hB
  · exact hOmega
  · exact hempty
  · exact hf
  all_goals exact hNat _

end OneYTruth.InternalSyntaxCodes

#print axioms OneYTruth.InternalSyntaxCodes.syntaxCodes_mem
#print axioms OneYTruth.InternalSyntaxCodes.sigmaCodes_mem
