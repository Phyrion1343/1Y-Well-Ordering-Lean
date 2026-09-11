/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalBareHistory

/-!
# Internal semantics of the canonical bare history

For an ordinal `alpha`, the set `canonicalBareHistory alpha` is the actual
graph

`{ <beta, L_beta> | beta <= alpha }`.

This file proves an assumption-transparent completeness statement.  If this
particular graph belongs to a transitive carrier `U`, the zero parameter is
the actual empty set, and the internal Goedel evaluator is correct on `U`,
then the graph is internally valid and witnesses the bare-stage formula at
`alpha`.  No reflection or elementarity hypothesis is used, and no theorem
below assumes `CanonicalBareStagesCorrectIn`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- A canonical graph pair belongs to `U` whenever its index is within the
bound and the whole canonical history belongs to the transitive set `U`. -/
theorem canonicalBareHistoryPair_mem_of_history_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    canonicalBareHistoryPair ordinal ∈ U := by
  apply hU.mem_trans _ hhistory
  exact mem_canonicalBareHistory_iff.mpr
    ⟨ordinal, hordinal, rfl⟩

/-- Consequently both coordinates of every relevant canonical graph pair
belong to `U`. -/
theorem canonicalBareHistory_components_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    ordinal.toZFSet ∈ U ∧ LStageZF ordinal ∈ U := by
  apply orderedPair_components_mem_of_transitive hU
  simpa only [canonicalBareHistoryPair] using
    (canonicalBareHistoryPair_mem_of_history_mem hU hordinal hhistory)

/-- The canonical graph contains its expected entry at every index through
the bound. -/
theorem canonicalBareHistory_entry
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound) :
    BareHistoryEntryIn (canonicalBareHistory bound)
      ordinal.toZFSet (LStageZF ordinal) := by
  exact pair_mem_canonicalBareHistory_iff.mpr
    ⟨ordinal, hordinal, rfl, rfl⟩

/-- Before invoking the internal evaluator, the canonical graph satisfies the
usual ambient zero/successor/limit recursion at every index through its
bound.  All witnesses required by the restricted predicate are obtained from
membership of the graph in the transitive carrier. -/
theorem canonicalBareHistory_localStateAmbientIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateAmbientIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) ordinal.toZFSet
      (LStageZF ordinal) := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      exact Or.inl ⟨by rw [Ordinal.toZFSet_zero, hempty],
        by rw [LStageZF_zero, hempty]⟩
  | add_one alpha _ih =>
      rw [← Order.succ_eq_add_one] at hordinal ⊢
      have hcomponents := canonicalBareHistory_components_mem hU
        ((Order.le_succ alpha).trans hordinal) hhistory
      refine Or.inr (Or.inl
        ⟨alpha.toZFSet, hcomponents.1,
          LStageZF alpha, hcomponents.2, ?_, ?_, ?_⟩)
      · exact (ordinalToZFSet_successor_predecessor_iff
          alpha alpha.toZFSet).mpr rfl
      · exact canonicalBareHistory_entry
          ((Order.le_succ alpha).trans hordinal)
      · rw [LStageZF_succ,
          Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  | limit limit hl _ih =>
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · constructor
        · intro hzero
          have hcodes : limit.toZFSet = (0 : Ordinal.{u}).toZFSet := by
            calc
              limit.toZFSet = fixed (2 : Fin 13) := hzero
              _ = (∅ : ZFSet.{u}) := hempty
              _ = (0 : Ordinal.{u}).toZFSet := Ordinal.toZFSet_zero.symm
          exact hl.ne_bot (Ordinal.toZFSet_injective hcodes)
        · intro hpredecessor
          apply ordinalToZFSet_limit_no_predecessor hl
          rcases hpredecessor with
            ⟨predecessor, _hpredecessorU, hpredecessor⟩
          exact ⟨predecessor, hpredecessor⟩
      · intro z _hzU
        constructor
        · intro hz
          rcases (mem_LStageZF_limit_iff hl).mp hz with
            ⟨earlierOrdinal, hearlierOrdinal, hzEarlier⟩
          have hearlierLe : earlierOrdinal ≤ bound :=
            hearlierOrdinal.le.trans hordinal
          have hcomponents := canonicalBareHistory_components_mem hU
            hearlierLe hhistory
          exact ⟨earlierOrdinal.toZFSet, hcomponents.1,
            Ordinal.toZFSet_mem_toZFSet_iff.mpr hearlierOrdinal,
            LStageZF earlierOrdinal, hcomponents.2,
            canonicalBareHistory_entry hearlierLe, hzEarlier⟩
        · rintro ⟨earlierIndex, _hearlierIndexU, hearlierIndex,
            earlierStage, _hearlierStageU, hearlierEntry, hzEarlier⟩
          rcases pair_mem_canonicalBareHistory_iff.mp hearlierEntry with
            ⟨historyOrdinal, _hhistoryOrdinal,
              hearlierIndexEq, hearlierStageEq⟩
          subst earlierIndex
          subst earlierStage
          have hearlierOrdinal : historyOrdinal < limit :=
            Ordinal.toZFSet_mem_toZFSet_iff.mp hearlierIndex
          exact (mem_LStageZF_limit_iff hl).mpr
            ⟨historyOrdinal, hearlierOrdinal, hzEarlier⟩

/-- With the evaluator-correctness obligation supplied explicitly, the same
canonical graph satisfies the internally relativized local rule. -/
theorem canonicalBareHistory_localStateIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    {bound ordinal : Ordinal.{u}} (hordinal : ordinal ≤ bound)
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareHistoryLocalStateIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) ordinal.toZFSet
      (LStageZF ordinal) := by
  have hstageU :=
    (canonicalBareHistory_components_mem hU hordinal hhistory).2
  apply (bareHistoryLocalStateIn_iff_ambient fixed
    (canonicalBareHistory bound) ordinal.toZFSet
    (LStageZF ordinal) hstageU hcorrect).mpr
  exact canonicalBareHistory_localStateAmbientIn hU fixed hempty
    hordinal hhistory

private theorem exists_ordinal_code_le_of_code_le
    {bound : Ordinal.{u}} {index : ZFSet.{u}}
    (hindex : index ∈ bound.toZFSet ∨ index = bound.toZFSet) :
    ∃ ordinal ≤ bound, index = ordinal.toZFSet := by
  rcases hindex with hindex | rfl
  · rcases Ordinal.mem_toZFSet_iff.mp hindex with
      ⟨ordinal, hordinal, hcode⟩
    exact ⟨ordinal, hordinal.le, hcode.symm⟩
  · exact ⟨bound, le_refl bound, rfl⟩

/-- If the canonical graph through `bound` is an element of a transitive
carrier, it is an internally total, functional, locally correct history
through `bound`.  The only non-bounded semantic input is the explicitly
displayed evaluator-correctness hypothesis. -/
theorem canonicalBareHistory_validIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (bound : Ordinal.{u})
    (hhistory : canonicalBareHistory bound ∈ U) :
    BareValidStageHistoryIn (U : Set ZFSet.{u}) fixed
      (canonicalBareHistory bound) bound.toZFSet := by
  intro index _hindexU hindex
  rcases exists_ordinal_code_le_of_code_le hindex with
    ⟨ordinal, hordinal, rfl⟩
  have hcomponents := canonicalBareHistory_components_mem hU
    hordinal hhistory
  refine ⟨LStageZF ordinal, hcomponents.2,
    canonicalBareHistory_entry hordinal, ?_, ?_⟩
  · intro otherStage _hotherStageU hotherEntry
    exact canonicalBareHistory_functional
      (canonicalBareHistory_entry hordinal) hotherEntry
  · exact canonicalBareHistory_localStateIn hU fixed hempty hcorrect
      hordinal hhistory

/-- Predicate-level completeness: membership of the actual canonical history
in `U` supplies a witness for the actual constructible stage. -/
theorem canonicalBareHistory_stageAtIn
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u})
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet
      (LStageZF ordinal) := by
  exact ⟨canonicalBareHistory ordinal, hhistory,
    canonicalBareHistory_validIn hU fixed hempty hcorrect ordinal hhistory,
    canonicalBareHistory_entry (le_refl ordinal)⟩

/-- Combining completeness with the independent soundness induction gives
the exact predicate semantics, conditional only on the displayed canonical
history bound and evaluator correctness. -/
theorem bareStageAtIn_ordinal_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) (stage : ZFSet.{u})
    (hindex : ordinal.toZFSet ∈ U) (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    BareStageAtIn (U : Set ZFSet.{u}) fixed ordinal.toZFSet stage ↔
      stage = LStageZF ordinal := by
  constructor
  · exact bareStageAtIn_ordinal_sound_of_transitive hU fixed hempty
      hcorrect ordinal hindex hstage
  · rintro rfl
    exact canonicalBareHistory_stageAtIn hU fixed hempty hcorrect
      ordinal hhistory

/-- Formula-level completeness.  Fixed-parameter membership is included
because these are the free coordinates of the formula assignment. -/
theorem satisfiesIn_bareStageAtFormula_canonical
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (hfixed : ∀ i, fixed i ∈ U)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u})
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
      (bareStageAtRawAssignment fixed ordinal.toZFSet
        (LStageZF ordinal)) := by
  have hcomponents := canonicalBareHistory_components_mem hU
    (le_refl ordinal) hhistory
  apply (satisfiesIn_bareStageAtFormula_iff hU fixed
    ordinal.toZFSet (LStageZF ordinal) hfixed
    hcomponents.1 hcomponents.2).mpr
  exact canonicalBareHistory_stageAtIn hU fixed hempty hcorrect
    ordinal hhistory

/-- Exact formula semantics under the same transparent assumptions. -/
theorem satisfiesIn_bareStageAtFormula_ordinal_iff_of_canonicalHistory_mem
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (fixed : Tuple ZFSet.{u} 13) (hfixed : ∀ i, fixed i ∈ U)
    (hempty : fixed (2 : Fin 13) = (∅ : ZFSet.{u}))
    (hcorrect : BareGodelDefOutputCorrectIn U fixed)
    (ordinal : Ordinal.{u}) (stage : ZFSet.{u})
    (hindex : ordinal.toZFSet ∈ U) (hstage : stage ∈ U)
    (hhistory : canonicalBareHistory ordinal ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) bareStageAtFormula
        (bareStageAtRawAssignment fixed ordinal.toZFSet stage) ↔
      stage = LStageZF ordinal := by
  rw [satisfiesIn_bareStageAtFormula_iff hU fixed
      ordinal.toZFSet stage hfixed hindex hstage,
    bareStageAtIn_ordinal_iff_of_canonicalHistory_mem hU fixed hempty
      hcorrect ordinal stage hindex hstage hhistory]

end

end Constructible.Model
