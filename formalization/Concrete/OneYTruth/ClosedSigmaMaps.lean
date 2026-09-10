import OneYTruth.ComplexityRelabel
import OneYTruth.Weakening

/-!
# Sigma-one maps can be checked using set-coded closed finite scopes

Arbitrary free parameter types are eliminated using only the finitely many
variables occurring in the formula. Capturing them adds no quantifiers and
preserves the actual Sigma-one syntax. A dummy slot handles unused variables.
-/

namespace OneYTruth

open FirstOrder FirstOrder.Language

universe u v w z

theorem realize_freeVar_congr {k : Nat} {I : Type u} {A : Type v} {α : Type w}
    [DecidableEq α] {n : Nat} (M : Interpretation k I A)
    (φ : (language k I).BoundedFormula α n) (v w : α → A) (xs : Fin n → A)
    (h : ∀ a ∈ φ.freeVarFinset, v a = w a) : realize M φ v xs ↔ realize M φ w xs := by
  letI := M.structure
  have hv := @BoundedFormula.realize_restrictFreeVar (language k I) A _ α
    {a // a ∈ φ.freeVarFinset} _ n φ id (v ∘ Subtype.val) xs v (fun _ => rfl)
  have hw := @BoundedFormula.realize_restrictFreeVar (language k I) A _ α
    {a // a ∈ φ.freeVarFinset} _ n φ id (v ∘ Subtype.val) xs w (fun a => h a.val a.property)
  exact hv.symm.trans hw

theorem realize_captureParameters {k : Nat} {I : Type u} {A : Type v} {α : Type w}
    [DecidableEq α] {n m : Nat} (M : Interpretation k I A)
    (φ : (language k I).BoundedFormula α n) (g : α → Fin m)
    (p : Fin m → A) (v : α → A) (xs : Fin n → A)
    (hp : ∀ a ∈ φ.freeVarFinset, p (g a) = v a) :
    realize M (φ.relabel (fun a => (Sum.inr (g a) : Empty ⊕ Fin m))) Empty.elim
      (Fin.append p xs) ↔ realize M φ v xs := by
  letI := M.structure
  change (BoundedFormula.relabel _ φ).Realize Empty.elim _ ↔ _
  rw [BoundedFormula.realize_relabel]
  have hfree : Sum.elim (Empty.elim : Empty → A) (Fin.append p xs ∘ Fin.castAdd n) ∘
      (fun a => Sum.inr (g a)) = p ∘ g := by
    funext a
    simp only [Function.comp_apply, Sum.elim_inr, Fin.append_left]
  have hbound : Fin.append p xs ∘ Fin.natAdd m = xs := by
    funext i
    exact Fin.append_right p xs i
  rw [hfree, hbound]
  exact realize_freeVar_congr M φ (p ∘ g) v xs hp

def ClosedSigmaOneMap {k : Nat} {I : Type u} {A : Type v} {B : Type w}
    (M : Interpretation k I A) (N : Interpretation k I B) (f : A → B) : Prop :=
  ∀ (n : Nat) (φ : (language k I).BoundedFormula Empty n), IsSigmaOne φ →
    ∀ xs : Fin n → A, realize N φ Empty.elim (f ∘ xs) ↔ realize M φ Empty.elim xs

theorem sigmaOneMap_iff_closed {k : Nat} {I : Type u} {A : Type v} {B : Type w}
    [Nonempty A] (M : Interpretation k I A) (N : Interpretation k I B) (f : A → B) :
    SigmaOneMap M N f ↔ ClosedSigmaOneMap M N f := by
  classical
  constructor
  · intro hf n φ hφ xs
    let e : Empty ≃ ULift.{u} Empty := Equiv.ulift.symm
    let ψ := BoundedFormula.relabelEquiv e φ
    let vU : ULift.{u} Empty → A := fun z => nomatch z.down
    have hm : realize M ψ vU xs ↔ realize M φ Empty.elim xs := by
      letI := M.structure
      change (BoundedFormula.relabelEquiv e φ).Realize vU xs ↔ _
      rw [BoundedFormula.realize_relabelEquiv]
      have hv : vU ∘ e = (Empty.elim : Empty → A) := by
        funext z
        nomatch z
      rw [hv]
      rfl
    have hn : realize N ψ (f ∘ vU) (f ∘ xs) ↔
        realize N φ Empty.elim (f ∘ xs) := by
      letI := N.structure
      change (BoundedFormula.relabelEquiv e φ).Realize (f ∘ vU) (f ∘ xs) ↔ _
      rw [BoundedFormula.realize_relabelEquiv]
      have hv : (f ∘ vU) ∘ e = (Empty.elim : Empty → B) := by
        funext z
        nomatch z
      rw [hv]
      rfl
    exact hn.symm.trans ((hf ψ (hφ.relabelEquiv e) vU xs).trans hm)
  · intro hf α n φ hφ v xs
    let S := {a // a ∈ φ.freeVarFinset}
    let m := Fintype.card S + 1
    let g : α → Fin m := fun a => if h : a ∈ φ.freeVarFinset then
      (Fintype.equivFin S ⟨a, h⟩).succ else 0
    let p : Fin m → A := Fin.cons (Classical.choice (inferInstance : Nonempty A))
      (fun i => v ((Fintype.equivFin S).symm i).val)
    have hp : ∀ a ∈ φ.freeVarFinset, p (g a) = v a := by
      intro a ha
      simp only [p, g, dif_pos ha, Fin.cons_succ, Equiv.symm_apply_apply]
    let ψ := φ.relabel (fun a => (Sum.inr (g a) : Empty ⊕ Fin m))
    have hm := realize_captureParameters M φ g p v xs hp
    have hn := realize_captureParameters N φ g (f ∘ p) (f ∘ v) (f ∘ xs)
      (fun a ha => congrArg f (hp a ha))
    have hh := hf (m + n) ψ (hφ.relabel _) (Fin.append p xs)
    have hmap : f ∘ Fin.append p xs = Fin.append (f ∘ p) (f ∘ xs) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Function.comp_apply, Fin.append_left]
      · simp only [Function.comp_apply, Fin.append_right]
    rw [hmap] at hh
    exact hn.symm.trans (hh.trans hm)

end OneYTruth
