/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# ZFC together with the selected evaluator-coded `V = L` sentence

This file packages the parameter-free sentence constructed in `VEqualsL`
with the first-order theory ZFC. That sentence has been proved to express
the internally recomputed hierarchy for `LCarrier`; a generic adequacy theorem
over arbitrary ZFC models is not part of this file. The constructible
membership structure is a model of the resulting combined theory.
-/

@[expose] public section

universe u

namespace FirstOrder.Language.Theory

/-- ZFC together with the selected parameter-free evaluator-coded sentence
for `V = L`. -/
def ZFCVEqualsL : FirstOrder.Language.setTheory.Theory :=
  ZFC ∪ {Constructible.Model.vEqualsLSentence}

@[simp]
theorem model_ZFCVEqualsL_iff {M : Type u}
    [FirstOrder.Language.setTheory.Structure M] :
    M ⊨ ZFCVEqualsL ↔
      M ⊨ ZFC ∧ M ⊨ Constructible.Model.vEqualsLSentence := by
  simp only [ZFCVEqualsL, model_union_iff, model_singleton_iff]

end FirstOrder.Language.Theory

namespace Constructible.Model

/-- The constructible universe models ZFC together with the selected
evaluator-coded `V = L` sentence. -/
theorem lCarrier_models_ZFCVEqualsL :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCVEqualsL := by
  rw [FirstOrder.Language.Theory.model_ZFCVEqualsL_iff]
  exact ⟨lCarrier_models_ZFC, lCarrier_models_vEqualsL⟩

end Constructible.Model
