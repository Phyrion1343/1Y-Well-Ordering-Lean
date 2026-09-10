import OneYTruth.GraphStepSigmaFO
import OneYTruth.InternalAssignmentLookup

/-! A complete internal one-step presentation. The thirteen fixed source sets
are constructed from the original domain and ordinal bound, and the step
itself is closed under the actual schema hypotheses. -/

namespace OneYTruth.InternalActualStep

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open InternalClosure UniformSyntaxSource GraphStepMatrix FormulaCode InternalNodes

universe u v

section

variable {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V) (hOmega : Ordinal.omega0.toZFSet ∈ V)

include hV N hmem hCol hSep hpair hUnion hOmega

theorem fixedParameters_mem (κ : Ordinal.{u}) (U : LCarrier.{u})
    (hκ : κ.toZFSet ∈ V) (hU : U.val ∈ V) :
    ∀ i, (fixedParameters κ U i).val ∈ V := by
  have hnat (n : Nat) : (natCode n : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨n,rfl⟩) hOmega
  have hempty : (∅ : ZFSet.{u}) ∈ V := by simpa [natCode] using hnat 0
  have hB : (ordinalBound κ).val ∈ V := InternalCodeUniverse.codeUniverse_mem
    hV N hmem hCol hSep hpair hUnion hempty hOmega (ordinalCarrier κ) hκ
  have hAs := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  have hLookup := AssignmentLookup.lookupSet_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  intro i
  fin_cases i <;> first | exact hU | exact hκ | exact hB | exact hAs | exact hLookup | exact hOmega | exact hempty | exact hnat 1 | exact hnat 2 | exact hnat 3 | exact hnat 4 | exact hnat 5 | exact hnat 6

theorem step_mem (κ η : Ordinal.{u}) (k : Nat) (U : LCarrier.{u}) (q : ZFSet.{u})
    (hκ : κ.toZFSet ∈ V) (hη : η.toZFSet ∈ V) (hU : U.val ∈ V) (hq : q ∈ V) :
    PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet q ∈ V := by
  have hzero : (natCode 0 : ZFSet.{u}) ∈ V :=
    hV.mem_trans ((Constructible.IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨0,rfl⟩) hOmega
  have hempty : (∅ : ZFSet.{u}) ∈ V := by simpa [natCode] using hzero
  have hA : ZFSet.range (ordinalIndexCode (η := η)) ∈ V := by rw [ordinal_range]; exact hη
  have hF := InternalSyntaxCodes.syntaxCodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hOmega
    (ordinalCarrier η) (ordinal_range η).symm hη
  have hAs := AssignmentGrammar.assignmentCodes_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  have hLookup := AssignmentLookup.lookupSet_mem hV N hmem hCol hSep hpair hUnion hempty hOmega U hU
  exact InternalGraphInput.step_mem_of_sources hV N hmem hCol hSep hpair hUnion
    ordinalIndexCode_injective hU hκ hq hA hOmega hF hAs hLookup

end

theorem foFormula_correct {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V)
    (hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V)
    (κ η : Ordinal.{u}) (hη : η ≤ κ) (k : Nat) (U : LCarrier.{u})
    (p : Fin 16 → ZFCarrier V)
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val)
    (hstage : (p 13).val = ZFSet.pair (natCode k) η.toZFSet) :
    FOFormula.Satisfies (zfCarrierMem V) GraphStepSigma.foFormula p ↔
      (p 15).val = PredecessorGraph.step k U.val (ordinalIndexCode (η := η)) κ.toZFSet (p 14).val := by
  simpa only [hmem] using (GraphStepSigma.realize_query_iff_fo N p).symm.trans
    (GraphStepSigma.realize_query_iff hV hVL N hmem hCol hSep hpair hUnion κ η hη k U p hp hstage)

end OneYTruth.InternalActualStep
