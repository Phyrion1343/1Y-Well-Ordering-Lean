/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GCHImpliesCH
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFCVEqualsLGCH
public import Mathlib.ModelTheory.Satisfiability

/-!
# Semantic consistency consequences of the constructible universe

This file packages CH and GCH with Mathlib's first-order theory `ZFC` and
uses the concrete constructible membership structure as a model.  Thus the
conclusions use Mathlib's standard semantic notion `Theory.IsSatisfiable`.

These theorems record model existence in Lean's metatheory.  They do not claim
that the present `ZFSet`-specific construction has been parameterized over an
arbitrary, possibly externally ill-founded, model of ZFC.
-/

@[expose] public section

universe u

namespace FirstOrder.Language.Theory

/-- ZFC together with the standard first-order CH sentence. -/
def ZFCCH : FirstOrder.Language.setTheory.Theory :=
  ZFC ∪ {Constructible.ContinuumFormula.chSentence}

/-- ZFC together with the standard first-order GCH sentence. -/
def ZFCGCH : FirstOrder.Language.setTheory.Theory :=
  ZFC ∪ {Constructible.ContinuumFormula.gchSentence}

@[simp]
theorem model_ZFCCH_iff {M : Type u}
    [FirstOrder.Language.setTheory.Structure M] :
    M ⊨ ZFCCH ↔
      M ⊨ ZFC ∧
        M ⊨ Constructible.ContinuumFormula.chSentence := by
  simp only [ZFCCH, model_union_iff, model_singleton_iff]

@[simp]
theorem model_ZFCGCH_iff {M : Type u}
    [FirstOrder.Language.setTheory.Structure M] :
    M ⊨ ZFCGCH ↔
      M ⊨ ZFC ∧
        M ⊨ Constructible.ContinuumFormula.gchSentence := by
  simp only [ZFCGCH, model_union_iff, model_singleton_iff]

end FirstOrder.Language.Theory

namespace Constructible.ContinuumFormula

/-- Satisfaction of the CH sentence by `LCarrier` is exactly `ModelsCH`. -/
@[simp]
theorem lCarrier_models_chSentence_iff :
    Constructible.Model.LCarrier.{u} ⊨ chSentence ↔
      ModelsCH (A := Constructible.Model.LCarrier.{u})
        Constructible.Model.lCarrierMem := by
  change Constructible.Model.realizes
      Constructible.Model.lCarrierMem chSentence
        (fun i : Fin 0 => Fin.elim0 i) ↔
    ModelsCH (A := Constructible.Model.LCarrier.{u})
      Constructible.Model.lCarrierMem
  exact realizes_chSentence_iff
    (A := Constructible.Model.LCarrier.{u})
    Constructible.Model.lCarrierMem

end Constructible.ContinuumFormula

namespace Constructible.Model

/-- The CH sentence holds in the constructible membership structure. -/
theorem lCarrier_models_chSentence :
    LCarrier.{u} ⊨ Constructible.ContinuumFormula.chSentence :=
  Constructible.ContinuumFormula.lCarrier_models_chSentence_iff.mpr
    Constructible.ContinuumFormula.modelsCH_lCarrier

/-- The constructible membership structure is a model of `ZFC + CH`. -/
theorem lCarrier_models_ZFCCH :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCCH := by
  rw [FirstOrder.Language.Theory.model_ZFCCH_iff]
  exact ⟨lCarrier_models_ZFC, lCarrier_models_chSentence⟩

/-- The constructible membership structure is a model of `ZFC + GCH`. -/
theorem lCarrier_models_ZFCGCH :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFCGCH := by
  rw [FirstOrder.Language.Theory.model_ZFCGCH_iff]
  exact ⟨lCarrier_models_ZFC,
    Constructible.ContinuumFormula.lCarrier_models_gchSentence_iff.mpr
      Constructible.ContinuumFormula.modelsGCH_lCarrier⟩

end Constructible.Model

namespace FirstOrder.Language.Theory

private instance lCarrierNonempty :
    Nonempty Constructible.Model.LCarrier.{0} :=
  ⟨Constructible.Model.emptyLCarrier⟩

/-- `ZFC + CH` has the concrete constructible membership structure as a
model, in Mathlib's standard semantic sense. -/
theorem ZFCCH_isSatisfiable : ZFCCH.IsSatisfiable :=
  by
    letI : Constructible.Model.LCarrier.{0} ⊨ ZFCCH :=
      Constructible.Model.lCarrier_models_ZFCCH
    exact Model.isSatisfiable Constructible.Model.LCarrier

/-- `ZFC + GCH` has the concrete constructible membership structure as a
model. -/
theorem ZFCGCH_isSatisfiable : ZFCGCH.IsSatisfiable :=
  by
    letI : Constructible.Model.LCarrier.{0} ⊨ ZFCGCH :=
      Constructible.Model.lCarrier_models_ZFCGCH
    exact Model.isSatisfiable Constructible.Model.LCarrier

/-- The packaged theory `ZFC + V = L + GCH` is satisfiable, witnessed by
the constructible membership structure. -/
theorem ZFCVEqualsLGCH_isSatisfiable : ZFCVEqualsLGCH.IsSatisfiable :=
  by
    letI : Constructible.Model.LCarrier.{0} ⊨ ZFCVEqualsLGCH :=
      Constructible.Model.lCarrier_models_ZFCVEqualsLGCH
    exact Model.isSatisfiable Constructible.Model.LCarrier

end FirstOrder.Language.Theory
