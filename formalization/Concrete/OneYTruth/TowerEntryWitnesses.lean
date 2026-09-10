import OneYTruth.TowerEntrySoundness
import OneYTruth.InternalGraphRestrictions

/-! Actual local records for the whole-tower certificate. The predecessor
graph is constructed internally by separation, and all twenty-one step
witnesses are supplied by the proved local completeness theorem. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula Constructible.Model
open ExternalTower GraphStepMatrix InternalClosure

universe u v w

def localParameters {A : Type w} (p : Fin 15 → A) (s q T : A) : Fin 16 → A :=
  Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin 13 => p (Fin.castAdd 2 i)) s) q) T

def localWitnesses {A : Type w} (s T q : A) (w : Fin 21 → A) : Fin 24 → A :=
  Fin.append ![s,T,q] w

theorem localMap_append {A : Type w} (p : Fin 15 → A) (s T q : A) (w : Fin 21 → A) :
    (fun i => Fin.append p (localWitnesses s T q w) (localMap i)) =
      Fin.append (localParameters p s q T) w := by
  funext i
  fin_cases i <;> simp [localMap,localWitnesses,localParameters,Fin.append,Fin.addCases,
    Fin.snoc,Fin.castLT]

theorem entry_witnesses {K : Nat} {J : Type v} {β κ : Ordinal.{u}}
    (hβ : RootSemantics.Adequate β) (hκβ : κ < β)
    (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (hCol : HasCollection N)
    (hSep : HasSeparation N) (U : LCarrier.{u}) (hU : U.val ∈ LStageZF β)
    (p : Fin 15 → ZFCarrier (LStageZF β))
    (hp : ∀ i : Fin 13, (p (Fin.castAdd 2 i)).val = (fixedParameters κ U i).val)
    (hg : (p 13).val = @graph κ U.val)
    (he : (p 14).val ∈ @graph κ U.val) :
    ∃ w : Fin 24 → ZFCarrier (LStageZF β),
      Satisfies ZFMem entryMatrix
        (Fin.append (fun i => (p i).val) (fun i => (w i).val)) := by
  let V := LStageZF β
  have hV : V.IsTransitive := LStageZF_isTransitive β
  have hVL : ∀ x ∈ V, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  let E := recursionEnvironment_of_adequate hβ
  have hpair : ∀ a ∈ V, ∀ b ∈ V, ZFSet.pair a b ∈ V :=
    fun _ ha _ hb => E.orderedPair_mem ha hb
  have hUnion : ∀ a ∈ V, ZFSet.sUnion a ∈ V := fun _ ha => E.sUnion_mem ha
  obtain ⟨s,hs⟩ := ZFSet.mem_range.mp he
  have hentry : ZFSet.pair (stageCode s) (truth U.val s) ∈ V := hs ▸ (p 14).property
  have hcomponents := pair_components_mem hV hentry
  let z : ZFCarrier V := ⟨stageCode s,hcomponents.1⟩
  let T : ZFCarrier V := ⟨truth U.val s,hcomponents.2⟩
  let q : ZFCarrier V := ⟨predecessorRestrictionGraph
    (stagePredecessors κ (stageCode s)) (codedTruth κ U.val),
    predecessorGraph_mem_of_adequate hβ hκβ hU s⟩
  let lp := localParameters p z q T
  have hfixed : ∀ i : Fin 13, (lp (Fin.castAdd 3 i)).val = (fixedParameters κ U i).val := by
    intro i
    change ((Fin.snoc (Fin.snoc (Fin.snoc (fun j : Fin 13 => p (Fin.castAdd 2 j)) z) q) T : Fin 16 → ZFCarrier V)
      i.castSucc.castSucc.castSucc).val = _
    simp only [Fin.snoc_castSucc]
    exact hp i
  have hstep : (lp 15).val = PredecessorGraph.step s.1 U.val
      (FormulaCode.ordinalIndexCode (η := s.2.val)) κ.toZFSet (lp 14).val := by
    change truth U.val s = _
    rw [← graphInputStep_code_eq_predecessorStep]
    exact (codedTruth_code U.val s).symm.trans (codedTruth_graphInputStep U.val s)
  have hquery := GraphStepSigma.query_complete hV hVL N hmem hCol hSep hpair hUnion
    κ s.2.val s.2.property s.1 U lp hfixed rfl hstep
  obtain ⟨w,hw⟩ := (GraphStepSigma.realize_query_iff_matrix hV N hmem lp).mp hquery
  refine ⟨localWitnesses z T q w,(satisfies_entryMatrix _).mpr ?_⟩
  have hvalues : Fin.append (fun i => (p i).val) (fun i => (localWitnesses z T q w i).val) =
      fun i => (Fin.append p (localWitnesses z T q w) i).val := by
    funext i
    refine Fin.addCases (m := 15) (n := 24) (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
  rw [hvalues]
  refine ⟨?_,?_,?_⟩
  · change (p 14).val = ZFSet.pair (stageCode s) (truth U.val s)
    exact hs.symm
  · change q.val = TowerRestriction.restrict (stageCode s) (p 13).val
    rw [hg,TowerRestriction.restrict_graph]
  · have hm := congrArg (fun f => val f) (localMap_append p z T q w)
    change Satisfies ZFMem GraphStepSigma.matrix
      (val (fun i => Fin.append p (localWitnesses z T q w) (localMap i)))
    rw [hm]
    exact hw

end OneYTruth.TowerSigma
