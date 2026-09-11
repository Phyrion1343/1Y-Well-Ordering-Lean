/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ContinuumHypothesis
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFCVEqualsL
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHApplication

/-!
# ZFC together with the selected `V = L` sentence and GCH

This file packages the previously constructed parameter-free sentences into
one first-order theory. The scope restriction on the evaluator-coded
`V = L` sentence is documented in `VEqualsL`. For the constructible
membership structure, modeling the combined theory is reduced exactly to the
GCH theorem proved from the textbook condensation argument.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

/-- Satisfaction of the GCH sentence in `LCarrier` is exactly its explicit
relation-parametric semantics for constructible membership. -/
@[simp]
theorem lCarrier_models_gchSentence_iff :
    Constructible.Model.LCarrier.{u} ⊨ gchSentence ↔
      ModelsGCH (A := Constructible.Model.LCarrier.{u})
        Constructible.Model.lCarrierMem := by
  change Constructible.Model.realizes
      Constructible.Model.lCarrierMem gchSentence
        (fun i : Fin 0 => Fin.elim0 i) ↔
    ModelsGCH (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem
  exact realizes_gchSentence_iff
    (A := Constructible.Model.LCarrier.{u})
    Constructible.Model.lCarrierMem

end Constructible.ContinuumFormula

namespace FirstOrder.Language.Theory

/-- ZFC together with the parameter-free sentences `V = L` and GCH. -/
def ZFCVEqualsLGCH : FirstOrder.Language.setTheory.Theory :=
  ZFCVEqualsL ∪ {Constructible.ContinuumFormula.gchSentence}

@[simp]
theorem model_ZFCVEqualsLGCH_iff {M : Type u}
    [FirstOrder.Language.setTheory.Structure M] :
    M ⊨ ZFCVEqualsLGCH ↔
      M ⊨ ZFC ∧
        M ⊨ Constructible.Model.vEqualsLSentence ∧
          M ⊨ Constructible.ContinuumFormula.gchSentence := by
  simp only [ZFCVEqualsLGCH, model_union_iff, model_singleton_iff,
    model_ZFCVEqualsL_iff, and_assoc]

end FirstOrder.Language.Theory

namespace Constructible.Model

/-- For the already constructed model of `ZFC + V = L`, satisfaction of the
combined theory is equivalent to satisfaction of its GCH sentence. -/
theorem lCarrier_models_ZFCVEqualsLGCH_iff :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCVEqualsLGCH ↔
      LCarrier.{u} ⊨ Constructible.ContinuumFormula.gchSentence := by
  rw [FirstOrder.Language.Theory.model_ZFCVEqualsLGCH_iff]
  simp only [lCarrier_models_ZFC, lCarrier_models_vEqualsL, true_and]

/-- Once the specialized GCH obligation is discharged, `LCarrier` is a model
of the packaged theory `ZFC + V = L + GCH`. -/
theorem lCarrier_models_ZFCVEqualsLGCH_of_gch
    (hgch : LCarrier.{u} ⊨ Constructible.ContinuumFormula.gchSentence) :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCVEqualsLGCH :=
  lCarrier_models_ZFCVEqualsLGCH_iff.mpr hgch

/-- The constructible membership structure is a model of
`ZFC + V = L + GCH`. -/
theorem lCarrier_models_ZFCVEqualsLGCH :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCVEqualsLGCH :=
  lCarrier_models_ZFCVEqualsLGCH_of_gch
    (Constructible.ContinuumFormula.lCarrier_models_gchSentence_iff.mpr
      Constructible.ContinuumFormula.modelsGCH_lCarrier)

end Constructible.Model
