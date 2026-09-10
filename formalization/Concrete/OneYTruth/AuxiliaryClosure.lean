import OneYTruth.Auxiliary
import OneYTruth.InternalClosure

/-! Finite auxiliary parameters preserve the actual Separation schema. -/

namespace OneYTruth.Auxiliary

open Constructible FirstOrder FirstOrder.Language

universe u v w

def HasSeparation {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U)) : Prop :=
  ∀ (n : Nat) (φ : language.BoundedFormula Empty (n + 1))
    (xs : Fin n → ZFCarrier U) (a : ZFCarrier U),
    ∃ b : ZFCarrier U, ∀ x : ZFCarrier U,
      x.val ∈ b.val ↔ x.val ∈ a.val ∧ realize M φ Empty.elim (Fin.snoc xs x)

noncomputable def closeParameters {α : Type v} [Fintype α] {n : Nat}
    (φ : language.BoundedFormula α (n + 1)) :
    language.BoundedFormula Empty ((Fintype.card α + n) + 1) :=
  BoundedFormula.relabel (Sum.elim
    (fun a => .inr ((Fintype.equivFin α a).castAdd (n + 1)))
    (fun i => .inr (i.natAdd (Fintype.card α)))) φ.toFormula

theorem realize_closeParameters {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    {α : Type v} [Fintype α] {n : Nat} (φ : language.BoundedFormula α (n + 1))
    (v : α → ZFCarrier U) (xs : Fin n → ZFCarrier U) (x : ZFCarrier U) :
    realize M (closeParameters φ) Empty.elim
      (Fin.snoc (Fin.append (v ∘ (Fintype.equivFin α).symm) xs) x) ↔
        realize M φ v (Fin.snoc xs x) := by
  letI := M.structure
  unfold realize closeParameters
  rw [BoundedFormula.realize_relabel, ← Fin.append_snoc]
  have hv : Sum.elim (Empty.elim : Empty → ZFCarrier U)
      (Fin.append (v ∘ (Fintype.equivFin α).symm) (Fin.snoc xs x) ∘ Fin.castAdd 0) ∘
      Sum.elim (fun a => Sum.inr ((Fintype.equivFin α a).castAdd (n + 1)))
        (fun i => Sum.inr (i.natAdd (Fintype.card α))) =
      Sum.elim v (Fin.snoc xs x) := by
    funext i
    cases i with
    | inl a =>
        change Fin.append (v ∘ (Fintype.equivFin α).symm) (Fin.snoc xs x)
          ((Fintype.equivFin α a).castAdd (n + 1)) = v a
        simp only [Fin.append_left, Function.comp_apply, Equiv.symm_apply_apply]
    | inr i =>
        change Fin.append (v ∘ (Fintype.equivFin α).symm) (Fin.snoc xs x)
          (i.natAdd (Fintype.card α)) = (Fin.snoc xs x : Fin (n + 1) → ZFCarrier U) i
        exact Fin.append_right _ _ i
  rw [hv, Formula.boundedFormula_realize_eq_realize, BoundedFormula.realize_toFormula]
  rfl

theorem separation_with_parameters {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hSep : HasSeparation M) {α : Type v} [Fintype α] {n : Nat}
    (φ : language.BoundedFormula α (n + 1)) (v : α → ZFCarrier U)
    (xs : Fin n → ZFCarrier U) (a : ZFCarrier U) :
    ∃ b : ZFCarrier U, ∀ x : ZFCarrier U,
      x.val ∈ b.val ↔ x.val ∈ a.val ∧ realize M φ v (Fin.snoc xs x) := by
  obtain ⟨b, hb⟩ := hSep _ (closeParameters φ)
    (Fin.append (v ∘ (Fintype.equivFin α).symm) xs) a
  exact ⟨b, fun x => (hb x).trans
    (and_congr_right fun _ => realize_closeParameters M φ v xs x)⟩

/-- Only the finitely many named predicates actually used by a formula are parameters. -/
theorem reduct_hasSeparation {U : ZFSet.{u}} (M : Interpretation (ZFCarrier U))
    (hSep : HasSeparation M) {k : Nat} {I : Type w}
    (block : Fin (k + 1) → ZFCarrier U) (index : I → ZFCarrier U) :
    InternalClosure.HasSeparation (reduct M block index) := by
  classical
  intro n φ xs a
  let v := Sum.elim (Empty.elim : Empty → ZFCarrier U)
    (Sum.elim block (fun i : {i // i ∈ namedSupport φ} => index i.val))
  obtain ⟨b, hb⟩ := separation_with_parameters M hSep (finiteTranslate φ) v xs a
  exact ⟨b, fun x => (hb x).trans (and_congr_right fun _ =>
    realize_finiteTranslate M block index φ Empty.elim (Fin.snoc xs x))⟩

end OneYTruth.Auxiliary
