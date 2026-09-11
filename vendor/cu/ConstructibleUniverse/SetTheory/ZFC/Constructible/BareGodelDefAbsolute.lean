/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistory
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# Local correctness of the Goedel-definability evaluator

This file proves that the first-order formula used at a successor step of a
bare stage history has its intended ambient meaning when interpreted in a
constructible limit level above `omega`.

The proof deliberately separates soundness from completeness.  Soundness
only projects a restricted finite evaluation certificate to the ambient
universe.  Completeness constructs the canonical program and execution-trace
codes and checks, using the local bounds from `BareStageHistoryBounds`, that
every unbounded witness belongs to the prescribed level.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF

private abbrev Carrier (a : ZFSet.{u}) := Constructible.ZFCarrier a

private theorem satisfies_congr_assignment {A : Type u}
    (E : A → A → Prop) {n : Nat} (formula : FOFormula n)
    (s t : Tuple A n) (h : ∀ i, s i = t i) :
    FOFormula.Satisfies E formula s ↔ FOFormula.Satisfies E formula t := by
  induction formula with
  | mem i j =>
      change E (s i) (s j) ↔ E (t i) (t j)
      rw [h i, h j]
  | eq i j =>
      change s i = s j ↔ t i = t j
      rw [h i, h j]
  | neg formula ih => exact not_congr (ih s t h)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft s t h) (ihRight s t h)
  | ex formula ih =>
      simp only [FOFormula.Satisfies]
      apply exists_congr
      intro x
      apply ih
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last]
      · simpa only [snoc_castSucc] using h j

@[simp]
private theorem carrierVal_snoc_apply {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (x : Carrier a) (i : Fin (n + 1)) :
    (snoc s x i).1 = snoc (fun j => (s j).1) x.1 i := by
  exact congrFun (Delta0Formula.val_snoc s x) i

private theorem carrierVal_eq {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) :
    Delta0Formula.val s = (fun i => (s i).1) := by
  rfl

private theorem carrierVal_snoc4 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (w x y z : Carrier a) :
    Delta0Formula.val (snoc (snoc (snoc (snoc s w) x) y) z) =
      snoc (snoc (snoc (snoc (fun i => (s i).1) w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc, carrierVal_eq]

private theorem carrierVal_snoc5 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (v w x y z : Carrier a) :
    Delta0Formula.val
        (snoc (snoc (snoc (snoc (snoc s v) w) x) y) z) =
      snoc (snoc (snoc (snoc (snoc (fun i => (s i).1) v.1)
        w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, carrierVal_eq]

private theorem satisfies_kuratowskiPairEqAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (pair left right : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [Delta0Formula.val_apply]

@[simp]
private theorem satisfies_functionGraphValueAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (graph value index : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value).1 (s index).1 ∈ (s graph).1 := by
  rw [functionGraphValueAt,
    Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO]
  simp only [Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    have hpair : ZFSet.pair (s value).1 (s index).1 ∈ a :=
      ha.mem_trans hq (s graph).2
    let q : Carrier a :=
      ⟨ZFSet.pair (s value).1 (s index).1, hpair⟩
    exact ⟨q, hq, rfl⟩

@[simp]
private theorem satisfies_uniqueValueAtBody_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence length graph index value : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value.1 index.1 ∈ graph.1 ∧
        ∀ other : Carrier a,
          ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1 := by
  simp only [uniqueValueAtBody, FOFormula.Satisfies,
    FOFormula.satisfies_all, satisfies_formulaImp,
    satisfies_functionGraphValueAt_carrier ha,
    Subtype.ext_iff, Model.snoc_eq_finSnoc]
  change
    (ZFSet.pair value.1 index.1 ∈ graph.1 ∧
      ∀ other : Carrier a,
        ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1) ↔ _
  rfl

@[simp]
private theorem satisfies_totalFunctionalBody_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence length graph index : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index.1 ∈ length.1 →
        ∃ value : Carrier a,
          ZFSet.pair value.1 index.1 ∈ graph.1 ∧
            ∀ other : Carrier a,
              ZFSet.pair other.1 index.1 ∈ graph.1 →
                other.1 = value.1) := by
  simp only [totalFunctionalBody, satisfies_formulaImp,
    FOFormula.Satisfies, Model.snoc_eq_finSnoc, zfCarrierMem]
  change
    (index.1 ∈ length.1 →
      ∃ value : Carrier a,
        FOFormula.Satisfies (zfCarrierMem a) uniqueValueAtBody
          ![omega, sequence, length, graph, index, value]) ↔ _
  apply imp_congr_right
  intro _hindex
  apply exists_congr
  intro value
  exact satisfies_uniqueValueAtBody_carrier ha
    omega sequence length graph index value

@[simp]
private theorem satisfies_sequenceValidityFormula_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence : Carrier a) :
    FOFormula.Satisfies (zfCarrierMem a) sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : Carrier a,
        sequence.1 = ZFSet.pair length.1 graph.1 ∧
          length.1 ∈ omega.1 ∧
          ∀ index : Carrier a, index.1 ∈ length.1 →
            ∃ value : Carrier a,
              ZFSet.pair value.1 index.1 ∈ graph.1 ∧
                ∀ other : Carrier a,
                  ZFSet.pair other.1 index.1 ∈ graph.1 →
                    other.1 = value.1 := by
  simp only [sequenceValidityFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all]
  constructor
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · exact (satisfies_kuratowskiPairEqAt_carrier ha
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) _).mp hpair
    · intro index hindex
      have hbody := htotal index
      exact ((satisfies_totalFunctionalBody_carrier ha
        omega sequence length graph index).mp (by
          change FOFormula.Satisfies (zfCarrierMem a)
            totalFunctionalBody
            ![omega, sequence, length, graph, index] at hbody
          exact hbody)) hindex
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · exact (satisfies_kuratowskiPairEqAt_carrier ha
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) _).mpr hpair
    · intro index
      have hbody := (satisfies_totalFunctionalBody_carrier ha
        omega sequence length graph index).mpr (htotal index)
      change FOFormula.Satisfies (zfCarrierMem a)
        totalFunctionalBody ![omega, sequence, length, graph, index]
      exact hbody

private theorem sequenceValidity_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence : Carrier a)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![omega, sequence]) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![omega.1, sequence.1] := by
  rw [satisfies_sequenceValidityFormula_carrier ha] at hvalid
  rw [satisfies_sequenceValidityFormula]
  rcases hvalid with
    ⟨length, graph, hsequence, hlength, hfunctional⟩
  refine ⟨length.1, graph.1, hsequence, hlength, ?_⟩
  intro index hindex
  let indexA : Carrier a :=
    ⟨index, ha.mem_trans hindex length.2⟩
  rcases hfunctional indexA hindex with
    ⟨value, hvalue, hunique⟩
  refine ⟨value.1, hvalue, ?_⟩
  intro other hother
  have hpairA : ZFSet.pair other index ∈ a :=
    ha.mem_trans hother graph.2
  have hsingletonA : ({other} : ZFSet.{u}) ∈ a :=
    ha.mem_trans (by simp [ZFSet.pair]) hpairA
  have hotherA : other ∈ a :=
    ha.mem_trans (by simp) hsingletonA
  let otherA : Carrier a := ⟨other, hotherA⟩
  exact hunique otherA hother

private theorem sequenceValidityAssignment_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      (fun i => (s i).1) := by
  have hstandard : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![s 0, s 1] := by
    apply (satisfies_congr_assignment (zfCarrierMem a)
      sequenceValidityFormula s ![s 0, s 1] ?_).mp hvalid
    intro i
    fin_cases i <;> rfl
  have hambient := sequenceValidity_carrier_to_ambient ha
    (s 0) (s 1) hstandard
  apply (satisfies_congr_assignment Delta0Formula.ZFMem
    sequenceValidityFormula ![(s 0).1, (s 1).1]
      (fun i => (s i).1) ?_).mp hambient
  intro i
  fin_cases i <;> rfl

private theorem hasLength_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hlength : FOFormula.Satisfies (zfCarrierMem a)
      hasLengthFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
      (fun i => (s i).1) := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at hlength ⊢
  rcases hlength with ⟨graph, hgraph⟩
  refine ⟨graph.1, ?_⟩
  have hraw := (Delta0Formula.satisfies_toFO_absolute ha
    _ (snoc s graph)).mp hgraph
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (Delta0Formula.val (snoc s graph)) at hraw
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (snoc (fun i => (s i).1) graph.1)
  rw [Delta0Formula.val_snoc] at hraw
  have hval : Delta0Formula.val s = (fun i => (s i).1) := rfl
  rw [hval] at hraw
  exact hraw

private theorem variableStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      variableStackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem variableStackStepFormula
      (fun i => (s i).1) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with ⟨generator, htoken, hgenerator, houtput⟩
  refine ⟨generator.1, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp htoken
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw
  · rcases hgenerator with hgenerator | hgenerator
    · exact Or.inl (congrArg Subtype.val hgenerator)
    · exact Or.inr hgenerator
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp houtput
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw

set_option maxHeartbeats 1200000 in
private theorem operationStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive) (operation : Fin 9)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      (operationStackStepFormula operation) s) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      (operationStackStepFormula operation) (fun i => (s i).1) := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
  refine ⟨right.1, left.1, rest.1, result.1, inner.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp htoken
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinner
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp houtput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hop
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      (opGraphFormula operation).toFO _ _ ?_).mp hraw
    intro j
    exact congrFun (carrierVal_snoc5 s right left rest result inner)
      (stackStepOpGraphRename j)

private theorem stackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      stackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (fun i => (s i).1) := by
  simp only [stackStepFormula, anyOperationStackStepFormula,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with hvariable | hoperation
  · exact Or.inl (variableStackStep_carrier_to_ambient ha s hvariable)
  · right
    rcases hoperation with h | h | h | h | h | h | h | h | h
    · exact Or.inl (operationStackStep_carrier_to_ambient ha 0 s h)
    · exact Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 1 s h))
    · exact Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 2 s h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 3 s h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 4 s h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 5 s h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (operationStackStep_carrier_to_ambient ha 6 s h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl
          (operationStackStep_carrier_to_ambient ha 7 s h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr
          (operationStackStep_carrier_to_ambient ha 8 s h))))))))

set_option maxHeartbeats 1200000 in
private theorem traceStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      traceStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
      (fun i => (s i).1) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstack⟩
  refine ⟨token.1, input.1, succ.1, output.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp htoken
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepProgramValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepInputValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hsucc
    change FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20)) _ at hraw
    rw [carrierVal_snoc4] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp houtput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepOutputValueRename i)
  · have hraw := stackStep_carrier_to_ambient ha _ hstack
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackStepFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepStackStepRename i)

private theorem stackProgramEvalCore_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 20)
    (hcore : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalCore s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalCore
      (fun i => (s i).1) := by
  rw [stackProgramEvalCore] at hcore ⊢
  rcases hcore with
    ⟨hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramLength ⊢
    exact hasLength_carrier_to_ambient ha _ hprogramLength
  · rw [FOFormula.satisfies_rename] at htraceLength ⊢
    exact hasLength_carrier_to_ambient ha _ htraceLength
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hsuccessor
  · rw [FOFormula.satisfies_rename] at hinitial ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinitial
  · rw [FOFormula.satisfies_rename] at hfinal ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hfinal
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hfinalStack
  · rw [FOFormula.satisfies_boundedAll] at hsteps ⊢
    intro index hindex
    let indexA : Carrier a :=
      ⟨index, ha.mem_trans hindex (s 17).2⟩
    have hrestricted := hsteps indexA hindex
    rw [FOFormula.satisfies_rename] at hrestricted ⊢
    have hambient := traceStep_carrier_to_ambient ha _ hrestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      traceStepFormula _ _ ?_).mp hambient
    intro i
    simp only [carrierVal_snoc_apply, indexA]

private theorem stackProgramEval_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (heval : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (fun i => (s i).1) := by
  rw [stackProgramEvalFormula] at heval ⊢
  rcases heval with
    ⟨hprogramValid, trace, htraceValid,
      programLength, traceLength, finalStack, hcore⟩
  refine ⟨?_, trace.1, ?_, programLength.1, traceLength.1,
    finalStack.1, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramValid ⊢
    exact sequenceValidityAssignment_carrier_to_ambient
      ha _ hprogramValid
  · rw [FOFormula.satisfies_rename] at htraceValid ⊢
    let traceValidityAssignment : Tuple (Carrier a) 2 :=
      fun i => snoc s trace (evalTraceValidityRename i)
    have htraceRestricted :
        FOFormula.Satisfies (zfCarrierMem a) sequenceValidityFormula
          traceValidityAssignment := htraceValid
    have htraceAmbient := sequenceValidityAssignment_carrier_to_ambient
      ha traceValidityAssignment htraceRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      sequenceValidityFormula _ _ ?_).mp htraceAmbient
    intro i
    simp only [traceValidityAssignment, carrierVal_snoc_apply]
  · let coreAssignment : Tuple (Carrier a) 20 :=
      snoc (snoc (snoc (snoc s trace) programLength)
        traceLength) finalStack
    have hcoreRestricted :
        FOFormula.Satisfies (zfCarrierMem a) stackProgramEvalCore
          coreAssignment := hcore
    have hambient := stackProgramEvalCore_carrier_to_ambient
      ha coreAssignment hcoreRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackProgramEvalCore _ _ ?_).mp hambient
    intro i
    simp only [coreAssignment, carrierVal_snoc_apply]

/-! ## Canonical witnesses inside a limit stage -/

/-- The intended one-step assignment, with every coordinate packaged in the
prescribed constructible limit level. -/
private def stackStepStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    Tuple (Carrier A) 16 :=
  ![⟨U, hsub hU⟩,
    ⟨varTag, hsub (varTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨appTag, hsub (appTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨operationCode 0, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩,
    ⟨operationCode 1, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 1)⟩,
    ⟨operationCode 2, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 2)⟩,
    ⟨operationCode 3, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 3)⟩,
    ⟨operationCode 4, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 4)⟩,
    ⟨operationCode 5, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 5)⟩,
    ⟨operationCode 6, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 6)⟩,
    ⟨operationCode 7, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 7)⟩,
    ⟨operationCode 8, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 8)⟩,
    ⟨stackTokenZFCode U token,
      hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩,
    ⟨listCode input,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩,
    ⟨listCode output,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩]

private theorem stackStepStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    (fun i => (stackStepStageAssignment hdelta hsub U hU token input output
      hinput houtput i).1) =
      stackStepAssignment U (stackTokenZFCode U token)
        (listCode input) (listCode output) := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem stackStepStageAssignment_val_apply
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) (i : Fin 16) :
    (stackStepStageAssignment hdelta hsub U hU token input output
      hinput houtput i).1 =
      stackStepAssignment U (stackTokenZFCode U token)
        (listCode input) (listCode output) i := by
  exact congrFun (stackStepStageAssignment_val hdelta hsub U hU token
    input output hinput houtput) i

private theorem satisfies_variableStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        variableStackStepFormula
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ generator : Carrier A,
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          listCode output = ZFSet.pair generator.1 (listCode input) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex,
    Subtype.ext_iff]
  rfl

private theorem comp_stackStepOpGraphRename_carrier
    {A : ZFSet.{u}}
    (s : Tuple (Carrier A) 16)
    (right left rest result inner : Carrier A) :
    (fun i =>
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner (stackStepOpGraphRename i)).1) =
      ![result.1, left.1, right.1] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_operationStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (operation : Fin 9)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        (operationStackStepFormula operation)
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ right left rest result : Carrier A,
        stackTokenZFCode U token =
            triple appTag (operationCode operation) ∅ ∧
          listCode input = ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          listCode output = ZFSet.pair result.1 rest.1 ∧
          ZFSet.pair left.1 rest.1 ∈ A ∧
          result.1 = op operation left.1 right.1 := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply,
    stackStepLiftFive, stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output, stackStepWitness_right,
    stackStepWitness_left, stackStepWitness_rest,
    stackStepWitness_result, stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinputCode, hinner, houtputCode, hop⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] := by
      rw [hcomp] at hop
      exact hop
    have hop' : result.1 = op operation left.1 right.1 :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mp hopRaw
    have hinnerMem : ZFSet.pair left.1 rest.1 ∈ A := by
      rw [← hinner]
      exact inner.2
    exact ⟨right, left, rest, result, htoken,
      hinputCode.trans (congrArg (ZFSet.pair right.1) hinner),
      houtputCode, hinnerMem, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinputCode, houtputCode, hinnerMem, hop⟩
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mpr hop
    let inner : Carrier A :=
      ⟨ZFSet.pair left.1 rest.1, hinnerMem⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    refine ⟨right, left, rest, result, inner,
      htoken, hinputCode, rfl, houtputCode, ?_⟩
    rw [hcomp]
    exact hopRaw

private theorem satisfies_stackStepFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (hrun : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackStepFormula
      (stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj]
  cases token with
  | inl generator =>
      left
      rw [satisfies_variableStackStepFormula_stageCarrier
        hA hdelta hsub]
      cases generator with
      | none =>
          have houtputEq : output = U :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨U, hsub hU⟩, rfl, Or.inl rfl, ?_⟩
          simp only [houtputEq, listCode_cons]
      | some generator =>
          have hgenerator : generator.1 ∈ LStageZF delta :=
            (LStageZF_isTransitive delta).mem_trans generator.2 hU
          have houtputEq : output = generator.1 :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨generator.1, hsub hgenerator⟩, rfl,
            Or.inr generator.2, ?_⟩
          simp only [houtputEq, listCode_cons]
  | inr operation =>
      right
      simp only [anyOperationStackStepFormula,
        FOFormula.satisfies_disj]
      have hop : FOFormula.Satisfies (zfCarrierMem A)
          (operationStackStepFormula operation)
          (stackStepStageAssignment hdelta hsub U hU (Sum.inr operation)
            input output hinput houtput) := by
        rw [satisfies_operationStackStepFormula_stageCarrier
          hA hdelta hsub]
        cases input with
        | nil => cases hrun
        | cons right tail =>
            cases tail with
            | nil => cases hrun
            | cons left rest =>
                have hright := hinput right (by simp)
                have hleft := hinput left (by simp)
                have hrestEntries : ∀ x ∈ rest, x ∈ LStageZF delta := by
                  intro x hx
                  exact hinput x (by simp [hx])
                have hrest :=
                  listCode_mem_LStageZF_of_isSuccLimit hdelta hrestEntries
                have hresult := op_mem_LStageZF_of_isSuccLimit
                  hdelta operation hleft hright
                have hinner := orderedPair_mem_LStageZF_of_isSuccLimit
                  hdelta hleft hrest
                have houtputEq :
                    output = op operation left right :: rest :=
                  (Option.some.inj hrun).symm
                refine ⟨⟨right, hsub hright⟩, ⟨left, hsub hleft⟩,
                  ⟨listCode rest, hsub hrest⟩,
                  ⟨op operation left right, hsub hresult⟩,
                  rfl, rfl, ?_, hsub hinner, rfl⟩
                simp only [houtputEq, listCode_cons]
      fin_cases operation
      · exact Or.inl hop
      · exact Or.inr (Or.inl hop)
      · exact Or.inr (Or.inr (Or.inl hop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hop)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hop))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hop)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hop)))))))

private theorem satisfies_valueAtFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (k : Nat) (value : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [valueAtFormula,
    Delta0Formula.satisfies_toFO_absolute hA]
  have hval :
      Delta0Formula.val
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] = ![IndexedSequenceZF.sequenceCode xs,
            natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hval]
  exact satisfies_valueAt_sequenceCode_iff xs k value.1

private theorem satisfies_hasLengthFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (length : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) hasLengthFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          length] ↔
      length.1 = natCode xs.length := by
  simp only [hasLengthFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨graph, hpair⟩
    have hpairRaw := (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mp hpair
    exact (ZFSet.pair_inj.mp hpairRaw).1.symm
  · intro hlength
    let graph : Carrier A :=
      ⟨IndexedSequenceZF.graph xs,
        hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
    refine ⟨graph, ?_⟩
    apply (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mpr
    change IndexedSequenceZF.sequenceCode xs =
      ZFSet.pair length.1 (IndexedSequenceZF.graph xs)
    rw [hlength]
    rfl

private theorem satisfies_sequenceValidity_sequenceCode_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, homegaA⟩,
        ⟨IndexedSequenceZF.sequenceCode xs,
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩] := by
  rw [satisfies_sequenceValidityFormula_carrier
    hA]
  let length : Carrier A :=
    ⟨natCode xs.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta xs.length)⟩
  let graph : Carrier A :=
    ⟨IndexedSequenceZF.graph xs,
      hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
  refine ⟨length, graph, rfl, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    have hvalue : xs.get ⟨k, hk⟩ ∈ LStageZF delta :=
      hxs _ (List.get_mem xs ⟨k, hk⟩)
    let value : Carrier A :=
      ⟨xs.get ⟨k, hk⟩, hsub hvalue⟩
    refine ⟨value, ?_, ?_⟩
    · apply (mem_graph_iff xs _).mpr
      exact ⟨⟨k, hk⟩, by simp only [hindexEq, value]⟩
    · intro other hother
      rcases (mem_graph_iff xs _).mp hother with ⟨j, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hkj : k = j.1 := natCode_injective
        (hindexEq.symm.trans hparts.2)
      simpa only [value, hkj] using hparts.1

private theorem satisfies_successorFOAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (successor predecessor : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (Delta0Formula.successorFOAt successor predecessor) s ↔
      (s successor).1 = insert (s predecessor).1 (s predecessor).1 := by
  rw [Delta0Formula.successorFOAt,
    Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt]
  simp only [Delta0Formula.val_apply]

private theorem encodedStackStates_entries_mem_LStageZF
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {states : List (List ZFSet.{u})}
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF theta) :
    ∀ code ∈ encodedStackStates states, code ∈ LStageZF theta := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨stack, hstack, rfl⟩
  exact listCode_mem_LStageZF_of_isSuccLimit htheta
    (hstates stack hstack)

private def stackStepPrefixStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta) :
    Tuple (Carrier A) 13 :=
  ![⟨U, hsub hU⟩,
    ⟨varTag, hsub (varTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨appTag, hsub (appTag_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩,
    ⟨operationCode 0, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩,
    ⟨operationCode 1, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 1)⟩,
    ⟨operationCode 2, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 2)⟩,
    ⟨operationCode 3, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 3)⟩,
    ⟨operationCode 4, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 4)⟩,
    ⟨operationCode 5, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 5)⟩,
    ⟨operationCode 6, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 6)⟩,
    ⟨operationCode 7, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 7)⟩,
    ⟨operationCode 8, hsub (operationCode_mem_LStageZF_of_isSuccLimit hdelta 8)⟩]

private theorem stackStepPrefixStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta) :
    (fun i => (stackStepPrefixStageAssignment hdelta hsub U hU i).1) =
      stackStepPrefixAssignment U := by
  funext i
  fin_cases i <;> rfl

private def traceStepExecutionStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩)
    ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩

private theorem traceStepExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat) :
    (fun i => (traceStepExecutionStageAssignment hdelta hsub U hU program
      states hstateCodes k i).1) =
      traceStepAssignment U (stackProgramZFCode U program)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states))
        (natCode k) := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [traceStepExecutionStageAssignment,
          traceStepAssignment, stackStepAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_traceStepProgramValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepProgramValueRename i)) =
      ![⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, token] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepInputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepInputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, input] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepOutputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepOutputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        succ, output] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepStackStepRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (succ : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k)
      ⟨stackTokenZFCode U token,
        hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
      ⟨listCode input,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
      ⟨listCode output,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
      (traceStepStackStepRename i)) =
      stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput := by
  funext i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc (snoc (snoc (snoc
        (traceStepExecutionStageAssignment hdelta hsub U hU program states
          hstateCodes k)
        ⟨stackTokenZFCode U token,
          hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
        ⟨listCode input,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
        ⟨listCode output,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩ j).1) =
        snoc (snoc (snoc (snoc
          (traceStepAssignment U (stackProgramZFCode U program)
            (IndexedSequenceZF.sequenceCode (encodedStackStates states))
            (natCode k))
          (stackTokenZFCode U token)) (listCode input)) succ.1)
          (listCode output) := by
    rw [Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      traceStepExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_traceStepStackStepRename U (stackProgramZFCode U program)
      (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode k) (stackTokenZFCode U token) (listCode input)
      succ.1 (listCode output)) i
  rw [congrFun hextendedVal (traceStepStackStepRename i),
    congrFun (stackStepStageAssignment_val hdelta hsub U hU token input
      output hinput houtput) i]
  exact hraw

private theorem satisfies_traceStepFormula_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (k : Nat) (hk : k < program.length) :
    FOFormula.Satisfies (zfCarrierMem A) traceStepFormula
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) := by
  have hlength := htrace.length
  have hi : k < states.length := by omega
  have ho : k + 1 < states.length := by omega
  let token := program.get ⟨k, hk⟩
  let input := states.get ⟨k, hi⟩
  let output := states.get ⟨k + 1, ho⟩
  have hinput : ∀ x ∈ input, x ∈ LStageZF delta :=
    hstates input (List.get_mem states ⟨k, hi⟩)
  have houtput : ∀ x ∈ output, x ∈ LStageZF delta :=
    hstates output (List.get_mem states ⟨k + 1, ho⟩)
  let tokenStage : Carrier A :=
    ⟨stackTokenZFCode U token,
      hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩
  let inputStage : Carrier A :=
    ⟨listCode input,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩
  let succStage : Carrier A :=
    ⟨natCode (k + 1),
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta (k + 1))⟩
  let outputStage : Carrier A :=
    ⟨listCode output,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
  rw [traceStepFormula]
  refine ⟨tokenStage, inputStage, succStage, outputStage, ?_⟩
  rw [traceStepBody]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename,
      comp_traceStepProgramValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackProgram U program) (by
        intro code hcode
        rcases List.mem_map.mp hcode with ⟨item, _hitem, rfl⟩
        exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit
          hdelta hU item) k tokenStage).mpr
    refine ⟨by simpa only [encodedStackProgram, List.length_map] using hk, ?_⟩
    simp only [encodedStackProgram, tokenStage, token,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepInputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      k inputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using hi, ?_⟩
    simp only [encodedStackStates, inputStage, input,
      List.get_eq_getElem, List.getElem_map]
  · apply (satisfies_successorFOAt_carrier
      hA (18 : Fin 20) (15 : Fin 20) _).mpr
    exact natCode_succ_eq_insert k
  · rw [FOFormula.satisfies_rename,
      comp_traceStepOutputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      (k + 1) outputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using ho, ?_⟩
    simp only [encodedStackStates, outputStage, output,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepStackStepRename_execution_stage
        (hinput := hinput) (houtput := houtput)]
    apply satisfies_stackStepFormula_stageCarrier_of_run
      hA hdelta hsub U hU token input output hinput houtput
    rcases htrace.indexed with ⟨_hlength, hsteps⟩
    simpa only [token, input, output] using hsteps ⟨k, hk⟩

private def stackProgramEvalCoreExecutionStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    Tuple (Carrier A) 20 :=
  snoc (snoc (snoc (snoc
    (snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
      ⟨Ordinal.omega0.toZFSet, homegaA⟩)
      ⟨stackProgramZFCode U program,
        hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
          hdelta hU program)⟩) ⟨result, hsub hresult⟩)
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩)
      ⟨natCode program.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩)
      ⟨natCode states.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩)
      ⟨listCode [result],
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
          intro x hx
          simp only [List.mem_singleton] at hx
          subst x
          exact hresult))⟩

private theorem stackProgramEvalCoreExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes i).1) =
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U (stackProgramZFCode U program)
          result)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
        (natCode program.length)) (natCode states.length))
        (listCode [result]) := by
  funext i
  refine Fin.lastCases ?_ (fun i19 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i18 => ?_) i19
    · rfl
    · refine Fin.lastCases ?_ (fun i17 => ?_) i18
      · rfl
      · refine Fin.lastCases ?_ (fun i16 => ?_) i17
        · rfl
        · refine Fin.lastCases ?_ (fun i15 => ?_) i16
          · rfl
          · refine Fin.lastCases ?_ (fun i14 => ?_) i15
            · rfl
            · refine Fin.lastCases ?_ (fun i13 => ?_) i14
              · rfl
              · simpa only [stackProgramEvalCoreExecutionStageAssignment,
                  stackProgramEvalAssignment, stackStepAssignment,
                  snoc_castSucc] using congrFun
                    (stackStepPrefixStageAssignment_val hdelta hsub U hU) i13

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_trace
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (16 : Fin 20) =
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩ := by
  rfl

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_programLength
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (17 : Fin 20) =
      ⟨natCode program.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩ := by
  rfl

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_finalStack
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (19 : Fin 20)).1 =
      listCode [result] := by
  rfl

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_result
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (15 : Fin 20)).1 = result := by
  rfl

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_traceLength
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (18 : Fin 20) =
      ⟨natCode states.length,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩ := by
  rfl

@[simp]
private theorem stackProgramEvalCoreExecutionStageAssignment_empty
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
      result hresult states hstateCodes (3 : Fin 20) =
      (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
        Carrier A) := by
  apply Subtype.ext
  rw [show (3 : Fin 20) =
      (3 : Fin 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
    by rfl]
  simp only [stackProgramEvalCoreExecutionStageAssignment,
    snoc_castSucc]
  rfl

private theorem satisfies_evalTraceSteps_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.boundedAll (17 : Fin 20)
        (FOFormula.rename evalTraceStepRename traceStepFormula))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  rw [FOFormula.satisfies_boundedAll]
  intro index hindex
  change index.1 ∈ natCode program.length at hindex
  rcases (mem_natCode_iff index.1 program.length).mp hindex with
    ⟨k, hk, hindexValue⟩
  have hindexEq : index =
      (⟨natCode k,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
        Carrier A) := Subtype.ext hindexValue
  subst index
  rw [FOFormula.satisfies_rename]
  have hlocal := satisfies_traceStepFormula_execution_stageCarrier
    hA hdelta hsub U hU program states htrace hstates k hk
  apply (satisfies_congr_assignment (zfCarrierMem A)
    traceStepFormula _ _ ?_).mpr hlocal
  intro i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc
        (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
          result hresult states hstateCodes)
        (⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
          Carrier A) j).1) =
        snoc (snoc (snoc (snoc (snoc
          (stackProgramEvalAssignment U (stackProgramZFCode U program)
            result)
          (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
          (natCode program.length)) (natCode states.length))
          (listCode [result])) (natCode k) := by
    rw [Model.subtypeVal_snoc,
      stackProgramEvalCoreExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_evalTraceStepRename U (stackProgramZFCode U program)
      result (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode program.length) (natCode states.length)
      (listCode [result]) (natCode k)) i
  rw [congrFun hextendedVal (evalTraceStepRename i),
    congrFun (traceStepExecutionStageAssignment_val hdelta hsub U hU program
      states (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) i]
  exact hraw

private theorem satisfies_evalProgramLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalProgramLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let programLength : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalProgramLengthRename i)) =
        ![⟨stackProgramZFCode U program,
            hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
              hdelta hU program)⟩, programLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackProgram U program) hprogramCodes programLength).mpr
  simp only [programLength, encodedStackProgram, List.length_map]

private theorem satisfies_evalTraceLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  let traceLength : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalTraceLengthRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          traceLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes traceLength).mpr
  simp only [traceLength, encodedStackStates, List.length_map]

private theorem satisfies_evalSuccessor_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_successorFOAt_carrier
    hA (18 : Fin 20) (17 : Fin 20) _).mpr
  change natCode states.length =
    insert (natCode program.length) (natCode program.length)
  rw [hlength]
  exact natCode_succ_eq_insert program.length

private theorem exists_encodedStackStates_zero_eq
    (states : List (List ZFSet.{u}))
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    ∃ hzero : 0 < (encodedStackStates states).length,
      listCode [] = (encodedStackStates states).get ⟨0, hzero⟩ := by
  have hrawHead :
      (encodedStackStates states).head? = some (listCode []) := by
    simp only [encodedStackStates, List.head?_map, hhead,
      Option.map_some]
  have hzero : 0 < (encodedStackStates states).length := by
    simpa only [encodedStackStates, List.length_map] using hstatesNonempty
  refine ⟨hzero, ?_⟩
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hzero] at hrawHead
  exact (Option.some.inj hrawHead).symm

private theorem comp_evalInitialValueRename_execution_stageCarrier
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes
        (evalInitialValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun x => ?_) j) i
  · exact stackProgramEvalCoreExecutionStageAssignment_trace
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · fin_cases x
    exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes

private theorem satisfies_valueAt_zero_encodedStackStates_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  rcases exists_encodedStackStates_zero_eq states hstatesNonempty hhead with
    ⟨hzero, hrawHead⟩
  let emptyStage : Carrier A :=
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩
  let zeroStage : Carrier A :=
    ⟨natCode 0, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩
  have hvalue :
      FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          zeroStage, emptyStage] := by
    exact (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states) hstateCodes 0 emptyStage).mpr
        ⟨hzero, hrawHead⟩
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  fin_cases i
  · rfl
  · apply Subtype.ext
    change (∅ : ZFSet.{u}) = natCode 0
    simp [natCode]
  · rfl

private theorem satisfies_evalInitial_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalInitialValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hvalue := satisfies_valueAt_zero_encodedStackStates_stageCarrier
    hA hdelta hsub states hstateCodes (by omega) hhead
  rw [FOFormula.satisfies_rename]
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  exact congrFun
    (comp_evalInitialValueRename_execution_stageCarrier hdelta hsub homegaA
      U hU program result hresult states hstateCodes) i

private theorem satisfies_evalFinal_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hlast : states.getLast? = some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalFinalValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hrawLast :
      (encodedStackStates states).getLast? = some (listCode [result]) := by
    simp only [encodedStackStates, List.getLast?_map, hlast,
      Option.map_some]
  have hrawLength :
      (encodedStackStates states).length = program.length + 1 := by
    simpa only [encodedStackStates, List.length_map] using hlength
  have hprogramLength : program.length < (encodedStackStates states).length :=
    by omega
  have hrawLastGet :
      listCode [result] = (encodedStackStates states).get
        ⟨program.length, hprogramLength⟩ := by
    have hgetLast :
        (encodedStackStates states).getLast? =
          some ((encodedStackStates states).get
            ⟨program.length, hprogramLength⟩) := by
      rw [List.getLast?_eq_getElem?]
      have hindex :
          (encodedStackStates states).length - 1 = program.length := by
        omega
      rw [hindex, List.getElem?_eq_getElem hprogramLength]
      rfl
    rw [hgetLast] at hrawLast
    exact (Option.some.inj hrawLast).symm
  let finalStack : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
        U hU program result hresult states hstateCodes
          (evalFinalValueRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          ⟨natCode program.length,
            hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩,
          finalStack] := by
    funext i
    fin_cases i
    · exact stackProgramEvalCoreExecutionStageAssignment_trace
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · exact stackProgramEvalCoreExecutionStageAssignment_programLength
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · apply Subtype.ext
      exact stackProgramEvalCoreExecutionStageAssignment_finalStack
        hdelta hsub homegaA U hU program result hresult states hstateCodes
  rw [hcomp]
  apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes program.length finalStack).mpr
  exact ⟨hprogramLength, hrawLastGet⟩

private theorem satisfies_evalFinalStack_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.kuratowskiPairEqAt
        (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_kuratowskiPairEqAt_carrier
    hA
    (19 : Fin 20) (15 : Fin 20) (3 : Fin 20) _).mpr
  rw [stackProgramEvalCoreExecutionStageAssignment_finalStack,
    stackProgramEvalCoreExecutionStageAssignment_result]
  have hempty := congrArg Subtype.val
    (stackProgramEvalCoreExecutionStageAssignment_empty hdelta hsub homegaA
      U hU program result hresult states hstateCodes)
  rw [hempty]
  rfl

private theorem satisfies_stackProgramEvalCore_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hhead : states.head? = some [])
    (hlast : states.getLast? = some [result])
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalCore
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  rw [stackProgramEvalCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_evalProgramLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalSuccessor_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length
  · exact satisfies_evalInitial_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hhead
  · exact satisfies_evalFinal_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hlast
  · exact satisfies_evalFinalStack_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceSteps_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hstates
        hstateCodes

private def stackProgramEvalStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresultA : result ∈ A) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩)
    ⟨result, hresultA⟩

private theorem stackProgramEvalStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresultA : result ∈ A) :
    (fun i => (stackProgramEvalStageAssignment hdelta hsub homegaA U hU
      program result hresultA i).1) =
      stackProgramEvalAssignment U (stackProgramZFCode U program)
        result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalStageAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem satisfies_stackProgramEvalFormula_stageCarrier_to_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresultA : result ∈ A)
    (heval : FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalFormula
      (stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
        result hresultA)) :
    runStackProgram (rudimentaryGenerator U) program [] = some [result] := by
  apply (satisfies_stackProgramEvalFormula_iff_run U program result).mp
  have hambient := stackProgramEval_carrier_to_ambient
    hA _ heval
  rw [stackProgramEvalStageAssignment_val] at hambient
  exact hambient

private theorem satisfies_stackProgramEvalFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalFormula
      (stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
        result (hsub hresult)) := by
  rcases exists_executionTrace_of_run
      (rudimentaryGenerator U) program [] [result] hrun with
    ⟨states, htrace, hhead, hlast⟩
  have hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta :=
    htrace.entries_mem_LStageZF_of_isSuccLimit hdelta hU hhead (by simp)
  have hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta :=
    encodedStackStates_entries_mem_LStageZF hdelta hstates
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let omegaStage : Carrier A :=
    ⟨Ordinal.omega0.toZFSet, homegaA⟩
  let programStage : Carrier A :=
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩
  let traceStage : Carrier A :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩
  let programLengthStage : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  let traceLengthStage : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  let finalStackStage : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  let baseAssignment :=
    stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
      result (hsub hresult)
  let traceContext : Tuple (Carrier A) 17 :=
    snoc baseAssignment traceStage
  rw [stackProgramEvalFormula]
  refine ⟨?_, traceStage, ?_, programLengthStage,
    traceLengthStage, finalStackStage, ?_⟩
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => baseAssignment (evalProgramValidityRename i)) =
          ![omegaStage, programStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    simpa only [programStage, stackProgramZFCode,
      encodedStackProgram] using
      (satisfies_sequenceValidity_sequenceCode_stageCarrier
        hA hdelta hsub homegaA
          (encodedStackProgram U program) hprogramCodes)
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => traceContext (evalTraceValidityRename i)) =
          ![omegaStage, traceStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact satisfies_sequenceValidity_sequenceCode_stageCarrier
      hA hdelta hsub homegaA (encodedStackStates states) hstateCodes
  · exact satisfies_stackProgramEvalCore_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hhead hlast
        hstates hstateCodes

/-- A genuine finite rudimentary program has the same evaluation semantics
in a transitive carrier `A` as in the ambient universe, provided all of its
canonical finite witnesses are built in a nonzero limit sublevel of `A`. -/
theorem satisfiesIn_stackProgramEvalFormula_of_isSuccLimit_substage_iff_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta) :
    Model.SatisfiesIn (A : Set ZFSet.{u})
        stackProgramEvalFormula
        (stackProgramEvalAssignment U (stackProgramZFCode U program)
          result) ↔
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  let s := stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
    result (hsub hresult)
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (A : Set ZFSet.{u}) stackProgramEvalFormula s
  have hval : (fun i => (s i).1) =
      stackProgramEvalAssignment U (stackProgramZFCode U program)
        result := stackProgramEvalStageAssignment_val
          hdelta hsub homegaA U hU program result (hsub hresult)
  rw [hval] at hbridge
  exact hbridge.symm.trans
    ⟨satisfies_stackProgramEvalFormula_stageCarrier_to_run
      hA hdelta hsub homegaA U hU program result (hsub hresult),
     satisfies_stackProgramEvalFormula_stageCarrier_of_run
      hA hdelta hsub homegaA U hU program result hresult⟩

/-- Specialization of the substage theorem to a constructible limit level
above `omega`. -/
theorem satisfiesIn_stackProgramEvalFormula_LStageZF_iff_run
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF theta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF theta) :
    Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        stackProgramEvalFormula
        (stackProgramEvalAssignment U (stackProgramZFCode U program)
          result) ↔
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  exact satisfiesIn_stackProgramEvalFormula_of_isSuccLimit_substage_iff_run
    (LStageZF_isTransitive theta) htheta (fun _ hx => hx)
      (ordinal_toZFSet_mem_LStageZF_of_lt homega)
      U hU program result hresult

/-! ## The output formula over a limit stage -/

private def godelDefOutputStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    Tuple (Carrier A) 15 :=
  snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨nextU, hnextU⟩

private theorem godelDefOutputStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    (fun i => (godelDefOutputStageAssignment hdelta hsub homegaA
      U nextU hU hnextU i).1) =
      Model.bareGodelDefOutputRawAssignment
        Model.stageHistoryFixedParametersRaw U nextU := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · rfl
    · fin_cases i13 <;> rfl

private def stackProgramEvalCodeStageAssignment
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U code result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hcode : code ∈ A)
    (hresult : result ∈ A) :
    Tuple (Carrier A) 16 :=
  snoc (snoc (snoc (stackStepPrefixStageAssignment hdelta hsub U hU)
    ⟨Ordinal.omega0.toZFSet, homegaA⟩)
    ⟨code, hcode⟩) ⟨result, hresult⟩

private theorem stackProgramEvalCodeStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U code result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hcode : code ∈ A)
    (hresult : result ∈ A) :
    (fun i => (stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code
      result hU hcode hresult i).1) =
      stackProgramEvalAssignment U code result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalCodeStageAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_godelDefEvalRename_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result code : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) (hcode : code ∈ A) :
    (fun i => snoc (snoc
      (godelDefOutputStageAssignment hdelta hsub homegaA U nextU hU hnextU)
      ⟨result, hresult⟩) ⟨code, hcode⟩ (godelDefEvalRename i)) =
      stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code result
        hU hcode hresult := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [godelDefEvalRename, Fin.lastCases_castSucc,
        godelDefOutputStageAssignment,
        stackProgramEvalCodeStageAssignment, snoc_castSucc]

private theorem satisfies_godelDefSubset_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
      (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ⟨result, hresult⟩) ↔ result ⊆ U := by
  rw [Delta0Formula.satisfies_toFO_absolute
      hA,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_subsetAt]
  change result ⊆ U ↔ result ⊆ U
  rfl

private theorem satisfies_godelDefOutputFormula_components_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔
      ∀ result : Carrier A,
        result.1 ∈ nextU ↔ result.1 ⊆ U ∧
          ∃ code : Carrier A,
            FOFormula.Satisfies (zfCarrierMem A)
              stackProgramEvalFormula
              (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
                U code.1 result.1 hU code.2 result.2) := by
  simp only [godelDefOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp]
  apply forall_congr'
  intro result
  change
    (result.1 ∈ nextU ↔
      FOFormula.Satisfies (zfCarrierMem A)
          (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
          (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
            U nextU hU hnextU) result) ∧
        ∃ code : Carrier A,
          FOFormula.Satisfies (zfCarrierMem A)
            (FOFormula.rename godelDefEvalRename stackProgramEvalFormula)
            (snoc (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
              U nextU hU hnextU) result) code)) ↔ _
  rw [satisfies_godelDefSubset_stageCarrier hA]
  simp only [FOFormula.satisfies_rename,
    comp_godelDefEvalRename_stage]

private theorem rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (term : RudimentaryClosureTerm U) :
    term.eval ∈ LStageZF theta := by
  induction term with
  | var generator =>
      cases generator with
      | none => exact hU
      | some x =>
          exact (LStageZF_isTransitive theta).mem_trans x.2 hU
  | app i left right hleft hright =>
      exact op_mem_LStageZF_of_isSuccLimit htheta i hleft hright

private theorem godelDef_element_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U result : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (hresult : result ∈ godelDef U) : result ∈ LStageZF theta := by
  rcases mem_godelDef_iff_exists_rudimentaryTerm.mp hresult with
    ⟨_hsubset, term, hterm⟩
  rw [← hterm]
  exact rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    htheta hU term

private theorem satisfies_godelDefOutputFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔ nextU = godelDef U := by
  rw [satisfies_godelDefOutputFormula_components_stageCarrier hA]
  constructor
  · intro h
    apply ZFSet.ext
    intro result
    constructor
    · intro hnext
      have hresultA : result ∈ A := hA.mem_trans hnext hnextU
      let resultStage : Carrier A := ⟨result, hresultA⟩
      rcases (h resultStage).mp hnext with ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact mem_godelDef_iff.mpr
        ⟨hsubset, mem_rudimentaryClosure_of_runStackProgram
          U program result hrun⟩
    · intro hgodel
      have hresultDelta : result ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU hgodel
      let resultStage : Carrier A := ⟨result, hsub hresultDelta⟩
      apply (h resultStage).mpr
      have hparts := mem_godelDef_iff.mp hgodel
      rcases mem_rudimentaryClosure_iff_exists_term.mp hparts.2 with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hparts.1, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result hU code.2 (hsub hresultDelta))
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
  · intro hnext result
    rw [hnext, mem_godelDef_iff]
    constructor
    · rintro ⟨hsubset, hclosure⟩
      have hresultDelta : result.1 ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU
          (mem_godelDef_iff.mpr ⟨hsubset, hclosure⟩)
      rcases mem_rudimentaryClosure_iff_exists_term.mp hclosure with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result.1] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hsubset, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result.1 hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result.1 hU code.2 result.2)
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
    · rintro ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result.1).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact ⟨hsubset,
        mem_rudimentaryClosure_of_runStackProgram
          U program result.1 hrun⟩

/-- Pointwise correctness of the internal Goedel-definability output formula
in a transitive carrier containing a nonzero limit level with all canonical
finite witnesses.  Only the predecessor `U` is required to lie in that
sublevel; the candidate output may be any element of the ambient carrier. -/
theorem bareGodelDefOutputIn_of_isSuccLimit_substage_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    Model.BareGodelDefOutputIn (A : Set ZFSet.{u})
        Model.stageHistoryFixedParametersRaw U nextU ↔
      nextU = godelDef U := by
  let s := godelDefOutputStageAssignment
    hdelta hsub homegaA U nextU hU hnextU
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (A : Set ZFSet.{u}) godelDefOutputFormula s
  have hval := godelDefOutputStageAssignment_val
    hdelta hsub homegaA U nextU hU hnextU
  rw [hval] at hbridge
  exact hbridge.symm.trans
    (satisfies_godelDefOutputFormula_stageCarrier_iff
      hA hdelta hsub homegaA U nextU hU hnextU)

/-- Over a constructible nonzero limit level above `omega`, the internal
Goedel-definability output formula has exactly its ambient meaning. -/
theorem bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
    {theta : Ordinal.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta) :
    Model.BareGodelDefOutputCorrectIn
      (LStageZF theta)
      Model.stageHistoryFixedParametersRaw := by
  intro predecessorStage stage hpredecessor hstage
  exact bareGodelDefOutputIn_of_isSuccLimit_substage_iff
    (LStageZF_isTransitive theta) htheta (fun _ hx => hx)
      (ordinal_toZFSet_mem_LStageZF_of_lt homega)
      predecessorStage stage hpredecessor hstage
