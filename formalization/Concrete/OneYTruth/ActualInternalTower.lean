import OneYTruth.InternalStageStepFormula
import OneYTruth.InternalActualStep
import OneYTruth.GraphInputConstructible

/-! # The complete actual truth tower inside every adequate larger level

All source sets, one-step truth sets, and canonical certificate witnesses
are constructed inside Lβ. The entire tower then follows from the proved
weak internal recursion theorem. No one-step presentation remains as a
hypothesis of the theorem below.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model RootSemantics InternalClosure

universe u

theorem graph_mem_of_adequate {κ β : Ordinal.{u}} (hβ : Adequate β)
    (hκβ : κ < β) {U : ZFSet.{u}} (hU : U ∈ LStageZF β) :
    @graph κ U ∈ LStageZF β := by
  let V := LStageZF β
  let N := interpretation (κ := β) V (0, ⟨0, zero_le⟩)
  let E := recursionEnvironment_of_adequate hβ
  have hs := hβ.2.2 0 0 zero_le
  have hV : V.IsTransitive := LStageZF_isTransitive β
  have hVL : ∀ x ∈ V, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  have hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V :=
    fun _ ha _ hb => E.orderedPair_mem ha hb
  have hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V := fun _ ha => E.sUnion_mem ha
  have hOmega : Ordinal.omega0.toZFSet ∈ V := ordinal_toZFSet_mem_LStageZF_of_lt hβ.1
  have hκ : κ.toZFSet ∈ V := ordinal_toZFSet_mem_LStageZF_of_lt hκβ
  let UL : LCarrier.{u} := ⟨U, hVL U hU⟩
  have hparams := InternalActualStep.fixedParameters_mem hV N rfl hs.2 hs.1
    hpair hUnion hOmega κ UL hκ hU
  let params : Tuple (ZFCarrier V) 13 :=
    fun i => ⟨(GraphStepMatrix.fixedParameters κ UL i).val, hparams i⟩
  apply graph_mem_of_internal_stepFormula E (stageSet_mem_LStage hβ.2.1 hβ.1 hκβ)
    U params GraphStepSigma.foFormula
  · intro x q v hx
    obtain ⟨s, hsCode⟩ := ZFSet.mem_range.mp hx
    let p := snoc (snoc (snoc params x) q) v
    have hp : ∀ i : Fin 13, (p (Fin.castAdd 3 i)).val =
        (GraphStepMatrix.fixedParameters κ UL i).val := by
      intro i
      change ((snoc (snoc (snoc params x) q) v) i.castSucc.castSucc.castSucc).val = _
      simp only [snoc_castSucc]
      rfl
    have hstage : (p 13).val = ZFSet.pair (Constructible.FiniteSequenceZF.natCode s.1) s.2.val.toZFSet :=
      hsCode.symm
    have hh := InternalActualStep.foFormula_correct hV hVL N rfl hs.2 hs.1
      hpair hUnion κ s.2.val s.2.property s.1 UL p hp hstage
    change FOFormula.Satisfies (zfCarrierMem V) GraphStepSigma.foFormula p ↔ _
    rw [hh, ← hsCode, graphInputStep_code_eq_predecessorStep]
    rfl
  · intro x q hx
    obtain ⟨s, hsCode⟩ := ZFSet.mem_range.mp hx
    rw [← hsCode, graphInputStep_code_eq_predecessorStep]
    exact InternalActualStep.step_mem hV N rfl hs.2 hs.1 hpair hUnion hOmega
      κ s.2.val s.1 UL q.val hκ
      (ordinal_toZFSet_mem_LStageZF_of_lt (s.2.property.trans_lt hκβ)) hU q.property

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.graph_mem_of_adequate

