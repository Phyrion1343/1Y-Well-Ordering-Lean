import OneYTruth.AuxiliaryFormulaCompilation
import OneYTruth.PureSetSatisfaction
import OneYTruth.ConstructibleSubsetBound
import OneYTruth.AuxiliaryClosure

/-!
# Separation for a constructible auxiliary relation

The four-place predicate is the literal membership code in W. Its
constructibility is an explicit remaining hypothesis, not an axiom of
an expanded model. All input formulas are evaluated by the satisfaction
set of one larger set domain. A single fixed bounded Separation query in L
and the countable-stage subset bound supply Separation in the ambient stage.
-/

namespace OneYTruth.AuxiliaryCode

open Constructible Constructible.Model FirstOrder FirstOrder.Language
open scoped Ordinal

universe u

def flatten {n : Nat} (φ : Language.setTheory.BoundedFormula (Fin 2) (n + 1)) :
    Language.setTheory.Formula (Fin ((2 + n) + 1)) :=
  φ.toFormula.relabel (Sum.elim (Fin.castAdd (n + 1)) (Fin.natAdd 2))

theorem realize_flatten {n : Nat}
    (φ : Language.setTheory.BoundedFormula (Fin 2) (n + 1))
    (us : Fin 2 → LCarrier.{u}) (xs : Fin n → LCarrier.{u}) (x : LCarrier.{u}) :
    (flatten φ).Realize (Fin.snoc (Fin.append us xs) x) ↔
      φ.Realize us (Fin.snoc xs x) := by
  rw [flatten, Formula.realize_relabel, ← Fin.append_snoc]
  have hv : Fin.append us (Fin.snoc xs x) ∘
      Sum.elim (Fin.castAdd (n + 1)) (Fin.natAdd 2) =
      Sum.elim us (Fin.snoc xs x) := by
    funext i
    cases i with
    | inl i => simp only [Function.comp_apply, Sum.elim_inl, Fin.append_left]
    | inr i => simp only [Function.comp_apply, Sum.elim_inr, Fin.append_right]
  rw [hv, BoundedFormula.realize_toFormula]
  rfl

theorem exists_separation_L (U W : LCarrier.{u}) {n : Nat}
    (φ : Auxiliary.language.BoundedFormula Empty (n + 1))
    (xs : Fin n → ZFCarrier U.val) (a : ZFCarrier U.val) :
    ∃ b : LCarrier.{u}, b.val ⊆ a.val ∧ ∀ x : ZFCarrier U.val,
      x.val ∈ b.val ↔ x.val ∈ a.val ∧
        Auxiliary.realize (interpretation U.val W.val) φ Empty.elim (Fin.snoc xs x) := by
  obtain ⟨γ, hUγ⟩ := mem_L_iff.mp U.property
  obtain ⟨θ, hWθ⟩ := mem_L_iff.mp W.property
  let δ : Ordinal.{u} := max γ θ + Ordinal.omega0
  have hδ : Order.IsSuccLimit δ := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hγδ : γ ≤ δ := (le_max_left γ θ).trans le_self_add
  have hθδ : θ ≤ δ := (le_max_right γ θ).trans le_self_add
  let D := LStageZF δ
  letI : Language.setTheory.Structure (ZFCarrier D) := setTheoryStructure (zfCarrierMem D)
  have hDL : D ∈ L := ⟨Order.succ δ, LStageZF_mem_succ δ⟩
  let U' : ZFCarrier D := ⟨U.val, LStageZF_mono hγδ hUγ⟩
  let W' : ZFCarrier D := ⟨W.val, LStageZF_mono hθδ hWθ⟩
  let ι := intoSet (LStageZF_isTransitive δ) U'
  let N := PureSatisfactionMatrix.interpretation D
  obtain ⟨b, hba, hb⟩ := PureSetSatisfaction.exists_separation hDL (n := 2 + n)
    (compile (translate φ)) (Fin.append ![U', W'] (fun i => ι (xs i))) (intoL U a)
  refine ⟨b, hba, fun x => (hb (ι x)).trans (and_congr Iff.rfl ?_)⟩
  change OneYTruth.realize N (compile (translate φ)) Empty.elim
    (Fin.snoc (Fin.append ![U', W'] (fun i => ι (xs i))) (ι x)) ↔ _
  rw [realize_compile_set_snoc N (fun _ _ => Iff.rfl)]
  change (translate φ).Realize ![U', W']
    (Fin.snoc (fun i => intoSet (LStageZF_isTransitive δ) U' (xs i))
      (intoSet (LStageZF_isTransitive δ) U' x)) ↔ _
  rw [← intoSet_snoc]
  exact realize_translate_stage hδ U' W' φ (Fin.snoc xs x)

/-- Actual ambient Separation, conditional only on the displayed relation W being in L. -/
theorem exists_separation_ambient (W : ZFSet.{u}) (hW : W ∈ L) {n : Nat}
    (φ : Auxiliary.language.BoundedFormula Empty (n + 1))
    (xs : Fin n → InitialStage.Ambient.{u}) (a : InitialStage.Ambient.{u}) :
    ∃ b : InitialStage.Ambient.{u}, ∀ x : InitialStage.Ambient.{u},
      x.val ∈ b.val ↔ x.val ∈ a.val ∧
        Auxiliary.realize (interpretation (LStageZF (ω₁ : Ordinal.{u})) W)
          φ Empty.elim (Fin.snoc xs x) := by
  let U : LCarrier.{u} := ⟨LStageZF (ω₁ : Ordinal.{u}),
    ⟨Order.succ (ω₁ : Ordinal.{u}), LStageZF_mem_succ _⟩⟩
  obtain ⟨b, hba, hb⟩ := exists_separation_L U ⟨W, hW⟩ φ xs a
  exact ⟨⟨b.val, InitialStage.constructible_subset_mem_ambient a.property hba b.property⟩, hb⟩

theorem ambient_hasSeparation (W : ZFSet.{u}) (hW : W ∈ L) :
    Auxiliary.HasSeparation (interpretation (LStageZF (ω₁ : Ordinal.{u})) W) :=
  fun _ φ xs a => exists_separation_ambient W hW φ xs a

/-- The separate local truth predicates inherit Separation via finite actual parameters. -/
theorem ambient_reduct_hasSeparation (W : ZFSet.{u}) (hW : W ∈ L)
    {k : Nat} {I : Type*} (block : Fin (k + 1) → InitialStage.Ambient.{u})
    (index : I → InitialStage.Ambient.{u}) :
    InternalClosure.HasSeparation
      (Auxiliary.reduct (interpretation (LStageZF (ω₁ : Ordinal.{u})) W) block index) :=
  Auxiliary.reduct_hasSeparation _ (ambient_hasSeparation W hW) block index

end OneYTruth.AuxiliaryCode
