import OneYTruth.FiniteSupport

/-!
# Finite formulas at a limit language stage

The index order is kept generic. Applied to ordinals, the two hypotheses
state that the stage is nonzero and has no immediate predecessor. The
conclusion is an exact syntactic factorization through a smaller stage.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v

theorem finite_indices_below_limit {O : Type u} [LinearOrder O]
    (η : O) (hne : ∃ x, x < η)
    (hlim : ∀ x, x < η → ∃ y, x < y ∧ y < η)
    (S : Finset {x : O // x < η}) :
    ∃ δ, δ < η ∧ ∀ i ∈ S, i.val < δ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨δ, hδ⟩ := hne
    exact ⟨δ, hδ, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨δ, hδ, hS⟩ := ih
    obtain ⟨ε, hε, hεη⟩ := hlim (max i.val δ) (max_lt i.property hδ)
    refine ⟨ε, hεη, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact lt_of_le_of_lt (le_max_left _ _) hε
    · exact lt_trans (hS j hj) (lt_of_le_of_lt (le_max_right _ _) hε)

/-- The inclusion between two stage languages has no new parameter for the upper stage. -/
def stageInclusion {O : Type u} [Preorder O] {δ η : O} (h : δ < η) :
    {x : O // x < δ} → {x : O // x < η} :=
  fun x => ⟨x.val, lt_trans x.property h⟩

/-- Every formula at a limit stage already lies in one smaller named language. -/
theorem exists_smaller_stage_formula {O : Type u} [LinearOrder O]
    {k : Nat} {α : Type v} {n : Nat} (η : O) (hne : ∃ x, x < η)
    (hlim : ∀ x, x < η → ∃ y, x < y ∧ y < η)
    (φ : (language k {x : O // x < η}).BoundedFormula α n) :
    ∃ (δ : O) (hδ : δ < η)
      (ψ : (language k {x : O // x < δ}).BoundedFormula α n),
      (namedMap (stageInclusion hδ)).onBoundedFormula ψ = φ := by
  classical
  let S := namedSupport φ
  obtain ⟨δ, hδ, hS⟩ := finite_indices_below_limit η hne hlim S
  let g : {i // i ∈ S} → {x : O // x < δ} := fun i => ⟨i.val.val, hS i.val i.property⟩
  let ψ₀ := restrictFormula S φ (fun _ h => h)
  have hcomp : (namedMap (k := k) (stageInclusion hδ)).comp (namedMap g) =
      namedMap (Subtype.val : {i // i ∈ S} → {x : O // x < η}) := by
    apply LHom.funext
    · funext n e
      nomatch e
    · funext n r
      cases r <;> rfl
  refine ⟨δ, hδ, (namedMap g).onBoundedFormula ψ₀, ?_⟩
  calc
    (namedMap (stageInclusion hδ)).onBoundedFormula ((namedMap g).onBoundedFormula ψ₀)
      = ((namedMap (stageInclusion hδ)).comp (namedMap g)).onBoundedFormula ψ₀ :=
        (congrFun (LHom.comp_onBoundedFormula (namedMap (stageInclusion hδ)) (namedMap g)) ψ₀).symm
    _ = (namedMap (Subtype.val : {i // i ∈ S} → {x : O // x < η})).onBoundedFormula ψ₀ := by
      rw [hcomp]
    _ = φ := namedMap_restrictFormula S φ _

end OneYTruth
