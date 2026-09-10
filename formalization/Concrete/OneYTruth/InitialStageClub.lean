import OneYTruth.InitialStageClosure

/-! The actual auxiliary elementary L stages are closed as well as unbounded. -/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Cardinal Ordinal

universe u

variable (M : Auxiliary.Interpretation Ambient.{u})

theorem elementary_of_cofinal {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)
    (hcofinal : letI := M.structure
      ∀ γ < α, ∃ β, γ ≤ β ∧ β < α ∧ (stageSubstructure M β).IsElementary) :
    letI := M.structure
    (stageSubstructure M α).IsElementary := by
  classical
  letI := M.structure
  apply Substructure.isElementary_of_exists
  intro n φ xs a ha
  have hxs : ∀ i : Fin n, ∃ γ < α, (xs i).val ∈ stageSet γ := by
    intro i
    exact (mem_LStageZF_limit_iff hα).mp (xs i).property
  choose γ hγα hxγ using hxs
  let γ₀ : Ordinal.{u} := Finset.univ.sup γ
  have hγ₀ : γ₀ < α := Finset.sup_lt_iff hα.pos |>.mpr (fun i _ => hγα i)
  obtain ⟨β, hγβ, hβα, hβ⟩ := hcofinal γ₀ hγ₀
  let S : Auxiliary.language.ElementarySubstructure Ambient.{u} :=
    ⟨stageSubstructure M β, hβ⟩
  let ys : Fin n → S := fun i => ⟨(xs i).val,
    stageSet_mono ((Finset.le_sup (f := γ) (Finset.mem_univ i)).trans hγβ) (hxγ i)⟩
  have hfree : S.subtype ∘ (default : Empty → S) = default := by
    funext e
    nomatch e
  have hys : S.subtype ∘ ys = Subtype.val ∘ xs := rfl
  have hex : φ.ex.Realize (S.subtype ∘ (default : Empty → S)) (S.subtype ∘ ys) := by
    rw [hfree, hys]
    exact BoundedFormula.realize_ex.mpr ⟨a, ha⟩
  have hexS := (S.subtype.map_boundedFormula φ.ex default ys).mp hex
  obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.mp hexS
  have hbM := (S.subtype.map_boundedFormula φ default (Fin.snoc ys b)).mpr hb
  rw [hfree, Fin.comp_snoc, hys] at hbM
  refine ⟨⟨b.val, stageSet_mono hβα.le b.property⟩, ?_⟩
  simpa only [ElementarySubstructure.coe_subtype] using hbM

/-- Membership in the concrete initial club, without a chosen club parameter. -/
def elementaryStages : Set Ordinal.{u} :=
  letI := M.structure
  {α | α < ω₁ ∧ Order.IsSuccLimit α ∧ (stageSubstructure M α).IsElementary}

theorem elementaryStages_unbounded (γ : Index.{u}) :
    ∃ α ∈ elementaryStages M, γ.val < α := by
  obtain ⟨α, hγα, hακ, hα, he⟩ := exists_elementary_LStage M γ
  exact ⟨α, ⟨hακ, hα, he⟩, hγα⟩

theorem elementaryStages_closed {α : Ordinal.{u}} (hακ : α < ω₁)
    (hα : Order.IsSuccLimit α)
    (hacc : ∀ γ < α, ∃ β ∈ elementaryStages M, γ ≤ β ∧ β < α) :
    α ∈ elementaryStages M := by
  refine ⟨hακ, hα, elementary_of_cofinal M hα ?_⟩
  intro γ hγ
  obtain ⟨β, hβ, hγβ, hβα⟩ := hacc γ hγ
  exact ⟨β, hγβ, hβα, hβ.2.2⟩

end OneYTruth.InitialStage
