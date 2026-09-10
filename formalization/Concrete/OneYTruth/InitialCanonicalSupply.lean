import OneYTruth.RootSemantics

/-! Concrete initial endpoints for the rebuilt canonical towers. -/

namespace OneYTruth.RootSemantics

open Constructible FirstOrder FirstOrder.Language ExternalTower InitialStage
open scoped Ordinal

universe u

noncomputable def ambientTruth : ZFSet.{u} := @uniformSet (ω₁ : Ordinal.{u}) (LStageZF ω₁)

def initialClub : Set Ordinal.{u} := elementaryStages truthAuxiliary

theorem initialClub_relation {a b η : Ordinal.{u}} (ha : a ∈ initialClub)
    (hb : b ∈ initialClub) (hab : a < b) (hηa : η ≤ a) (k : Nat) : R k η a b := by
  have hea : letI := (@auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁))
        (LStageZF a)).IsElementary := ha.2.2
  have heb : letI := (@auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁)).structure
      (Auxiliary.setSubstructure (@auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁))
        (LStageZF b)).IsElementary := hb.2.2
  refine ⟨hηa, hab, ?_⟩
  intro A n φ _ v xs
  have hleft := canonical_realize_trace_params ha.1.le ha.2.1 hea (k, ⟨η, hηa⟩) φ v xs
  have hright := canonical_realize_trace_params hb.1.le hb.2.1 heb
    (k, ⟨η, hηa.trans hab.le⟩) φ
    (Auxiliary.inclusion (LStageZF_mono hab.le) ∘ v)
    (Auxiliary.inclusion (LStageZF_mono hab.le) ∘ xs)
  exact hright.trans hleft.symm

theorem initialClub_adequate (hW : ambientTruth.{u} ∈ L) {a : Ordinal.{u}}
    (ha : a ∈ initialClub) (hωa : Ordinal.omega0 < a) : Adequate a := by
  let M := @auxiliaryInterpretation (ω₁ : Ordinal.{u}) (LStageZF ω₁)
  have he : letI := M.structure; (Auxiliary.setSubstructure M (LStageZF a)).IsElementary := ha.2.2
  have heq := canonical_auxiliary_restrict ha.1.le ha.2.1 he
  have hc := Auxiliary.restrict_hasCollection M rfl (LStageZF_mono ha.1.le)
    (LStageZF_isTransitive a) he (ambient_auxCollection M)
  have hs := Auxiliary.restrict_hasSeparation M rfl (LStageZF_mono ha.1.le) he
    (AuxiliaryCode.ambient_hasSeparation ambientTruth hW)
  rw [heq] at hc hs
  refine ⟨hωa, ha.2.1, ?_⟩
  intro k η hηa
  let block := traceBlock ha.2.1 k
  let index := traceIndex (k, ⟨η, hηa⟩)
  have hred := auxiliaryReduct_interpretation (LStageZF a) k hηa block (fun _ => rfl)
    index (fun _ => rfl)
  have hc' : InternalClosure.HasCollection (Auxiliary.reduct _ block index) :=
    Auxiliary.reduct_hasCollection _ hc block index
  have hs' : InternalClosure.HasSeparation (Auxiliary.reduct _ block index) :=
    Auxiliary.reduct_hasSeparation _ hs block index
  rw [hred] at hc' hs'
  exact ⟨hs', hc'⟩

theorem exists_initialEndpoint_above (γ : Index.{u}) :
    ∃ a : Ordinal.{u}, a ∈ initialClub ∧ γ.val < a ∧ Ordinal.omega0 < a := by
  let δ : Index.{u} := ⟨max γ.val Ordinal.omega0,
    max_lt γ.property Ordinal.omega0_lt_omega_one⟩
  obtain ⟨a, ha, hδa⟩ := elementaryStages_unbounded truthAuxiliary δ
  exact ⟨a, ha, (le_max_left _ _).trans_lt hδa, (le_max_right _ _).trans_lt hδa⟩

end OneYTruth.RootSemantics
