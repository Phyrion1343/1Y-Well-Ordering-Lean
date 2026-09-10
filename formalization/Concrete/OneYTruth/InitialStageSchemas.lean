import OneYTruth.InitialStageClub
import OneYTruth.AuxiliarySeparation
import OneYTruth.AuxiliaryCollectionSchema
import OneYTruth.AmbientCollection

/-!
# Actual schemas in the initial elementary stages

Collection needs no constructibility of W. Separation is conditional on
the displayed W being constructible. These are the restrictions of the
ambient predicate, not an identification with a smaller canonical tower.
-/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Ordinal

universe u v

theorem ambient_auxCollection (M : Auxiliary.Interpretation Ambient.{u}) :
    Auxiliary.HasCollection M := by
  intro n φ xs a ht
  exact collection_bound a
    (fun x y => Auxiliary.realize M φ Empty.elim (Fin.snoc (Fin.snoc xs x) y)) ht

theorem stage_auxCollection (W : ZFSet.{u}) {α : Ordinal.{u}}
    (hα : α ∈ elementaryStages (AuxiliaryCode.interpretation (LStageZF (ω₁ : Ordinal.{u})) W)) :
    Auxiliary.HasCollection (AuxiliaryCode.interpretation (LStageZF α) W) := by
  let M := AuxiliaryCode.interpretation (LStageZF (ω₁ : Ordinal.{u})) W
  have he : letI := M.structure; (Auxiliary.setSubstructure M (LStageZF α)).IsElementary := hα.2.2
  have hc := Auxiliary.restrict_hasCollection M rfl (LStageZF_mono hα.1.le)
    (LStageZF_isTransitive α) he (ambient_auxCollection M)
  exact hc

theorem stage_auxSeparation (W : ZFSet.{u}) (hW : W ∈ L) {α : Ordinal.{u}}
    (hα : α ∈ elementaryStages (AuxiliaryCode.interpretation (LStageZF (ω₁ : Ordinal.{u})) W)) :
    Auxiliary.HasSeparation (AuxiliaryCode.interpretation (LStageZF α) W) := by
  let M := AuxiliaryCode.interpretation (LStageZF (ω₁ : Ordinal.{u})) W
  have he : letI := M.structure; (Auxiliary.setSubstructure M (LStageZF α)).IsElementary := hα.2.2
  exact Auxiliary.restrict_hasSeparation M rfl (LStageZF_mono hα.1.le) he
    (AuxiliaryCode.ambient_hasSeparation W hW)

/-- Every actual mixed local schema follows using its finite set of auxiliary parameters. -/
theorem stage_reduct_schemas (W : ZFSet.{u}) (hW : W ∈ L) {α : Ordinal.{u}}
    (hα : α ∈ elementaryStages (AuxiliaryCode.interpretation (LStageZF (ω₁ : Ordinal.{u})) W))
    {k : Nat} {I : Type v} (block : Fin (k + 1) → ZFCarrier (LStageZF α))
    (index : I → ZFCarrier (LStageZF α)) :
    let N := Auxiliary.reduct (AuxiliaryCode.interpretation (LStageZF α) W) block index
    InternalClosure.HasCollection N ∧ InternalClosure.HasSeparation N ∧
      InternalClosure.HasReplacement N := by
  let N := Auxiliary.reduct (AuxiliaryCode.interpretation (LStageZF α) W) block index
  have hc := Auxiliary.reduct_hasCollection _ (stage_auxCollection W hα) block index
  have hs := Auxiliary.reduct_hasSeparation _ (stage_auxSeparation W hW hα) block index
  refine ⟨hc, hs, ?_⟩
  exact InternalClosure.hasReplacement_of_collection_separation N rfl hc hs

end OneYTruth.InitialStage
