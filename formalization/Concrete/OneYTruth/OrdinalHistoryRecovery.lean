import OneYTruth.OrdinalHistoryFormula

/-! # Soundness and actual internal witnesses for the bounded history matrix

The displayed native Delta0 successor matrix remains the sole local
interface. Its soundness is required only on actual internal sets, and its
completeness only on the canonical stored successor values.
-/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model Constructible.Delta0Formula Constructible.Godel

universe u v

theorem historyFormula_top_eq {p : Nat} (step : Delta0Formula (p+2))
    (params : Tuple ZFSet.{u} p) {V g B U : ZFSet.{u}} {a : Ordinal.{u}}
    (hV : V.IsTransitive) (hg : g ∈ V)
    (hstep : ∀ S ∈ V, ∀ D ∈ V,
      Satisfies ZFMem step (snoc (snoc params S) D) → D = DefZF S)
    (h : Satisfies ZFMem (historyFormula step)
      (snoc (snoc (snoc (snoc params (Order.succ a).toZFSet) g) B) ∅))
    (hU : Entry g a U) : U = LStageZF a := by
  apply top_eq_of_internal hV hg hstep
    ((satisfies_historyFormula step params _ _ _).mp h).toChecks hU

/-- Both the actual history and its state container are supplied here.
The step completeness input can be obtained by one Collection bound for
the genuine local Sigma-one Def certificates. -/
theorem exists_internal_historyFormula {p : Nat} (step : Delta0Formula (p+2))
    (params : Tuple ZFSet.{u} p) {a β : Ordinal.{u}}
    (hβ : Order.IsSuccLimit β) (ha : a < β)
    (hstep : ∀ i, Order.succ i ≤ a →
      Satisfies ZFMem step (snoc (snoc params (LStageZF i)) (LStageZF (Order.succ i)))) :
    ∃ g ∈ LStageZF β, ∃ B ∈ LStageZF β,
      Satisfies ZFMem (historyFormula step)
        (snoc (snoc (snoc (snoc params (Order.succ a).toZFSet) g) B) ∅) ∧
      Entry g a (LStageZF a) := by
  refine ⟨canonicalBareHistory a, canonical_mem_of_limit hβ ha,
    pairField (canonicalBareHistory a), history_field_mem_of_limit hβ ha, ?_,
    canonicalBareHistory_top_mem a⟩
  exact (satisfies_historyFormula step params _ _ _).mpr
    (canonical_rawChecks a (canonical_stage_mem_field a) hstep)

def mixedHistoryFormula (K : Nat) (J : Type v) {p : Nat} (step : Delta0Formula (p+2)) :=
  ofConstructibleDeltaZero K J (historyFormula step)

theorem mixedHistoryFormula_isDeltaZero (K : Nat) (J : Type v) {p : Nat}
    (step : Delta0Formula (p+2)) : IsDeltaZero (mixedHistoryFormula K J step) :=
  ofConstructibleDeltaZero_isDeltaZero _ _ _

theorem realize_history_top_eq {K : Nat} {J : Type v} {p : Nat} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (step : Delta0Formula (p+2))
    (params : Tuple (ZFCarrier V) p) (I g B Z U : ZFCarrier V) (a : Ordinal.{u})
    (hI : I.val = (Order.succ a).toZFSet) (hZ : Z.val = ∅)
    (hstep : ∀ S ∈ V, ∀ D ∈ V,
      Satisfies ZFMem step (snoc (snoc (fun i => (params i).val) S) D) → D = DefZF S)
    (h : realize N (mixedHistoryFormula K J step) Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc params I) g) B) Z))
    (hU : Entry g.val a U.val) : U.val = LStageZF a := by
  rw [mixedHistoryFormula, realize_ofConstructibleDeltaZero_absolute hV N hmem] at h
  have he : val (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc params I) g) B) Z) =
      snoc (snoc (snoc (snoc (fun i => (params i).val) I.val) g.val) B.val) Z.val := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [val, Fin.snoc_last, snoc_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [val, Fin.snoc_castSucc, Fin.snoc_last, snoc_castSucc, snoc_last]
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simp only [val, Fin.snoc_castSucc, Fin.snoc_last, snoc_castSucc, snoc_last]
        · refine Fin.lastCases ?_ (fun m => ?_) l
          · simp only [val, Fin.snoc_castSucc, Fin.snoc_last, snoc_castSucc, snoc_last]
          · simp only [val, Fin.snoc_castSucc, snoc_castSucc]
  rw [he, hI, hZ] at h
  exact historyFormula_top_eq step _ hV g.property hstep h hU

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.historyFormula_top_eq
#print axioms OneYTruth.OrdinalStageHistory.exists_internal_historyFormula
