import OneYTruth.AuxiliarySkolem
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull

/-!
# External countable elementary membership hulls as actual sets

This is an external countability construction. The resulting hull is an
actual ZFSet and fully elementary in its ambient set, but is not asserted
to belong to L. This is sufficient for the external Condensation Lemma.
-/

namespace OneYTruth.CountableSetHull

open Constructible Constructible.Model FirstOrder FirstOrder.Language

universe u v

private def relCode : (Σ n, Language.setTheory.Relations n) → Unit
  | ⟨_, .mem⟩ => ()

private instance : Countable (Σ n, Language.setTheory.Relations n) := by
  apply Function.Injective.countable (f := relCode)
  rintro ⟨_, r⟩ ⟨_, s⟩ _
  cases r
  cases s
  rfl

private instance : Countable (Σ n, Language.setTheory.Functions n) := by
  have : IsEmpty (Σ n, Language.setTheory.Functions n) := ⟨fun ⟨_, e⟩ => nomatch e⟩
  infer_instance

private instance : Countable Language.setTheory.Symbols := by
  change Countable ((Σ n, Language.setTheory.Functions n) ⊕
    (Σ n, Language.setTheory.Relations n))
  infer_instance

private instance : Countable
    (Σ n, (Language.setTheory.sum Language.setTheory.skolem₁).Functions n) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact FirstOrder.Language.card_functions_sum_skolem₁_le.trans
    (max_le le_rfl Cardinal.mk_le_aleph0)

/-- Raw membership satisfaction transported along any injective set-valued coding. -/
theorem satisfies_range {A : Type v} [Small.{u} A] (e : A → ZFSet.{u})
    (he : Function.Injective e) {n : Nat} (φ : FOFormula n) (xs : Fin n → A) :
    FOFormula.Satisfies (fun a b => e a ∈ e b) φ xs ↔
      SatisfiesIn (ZFSet.range e : Set ZFSet.{u}) φ (fun i => e (xs i)) := by
  induction φ with
  | mem => rfl
  | eq => exact ⟨congrArg e, fun h => he h⟩
  | neg φ ih => exact not_congr (ih xs)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ xs) (ihψ xs)
  | ex φ ih =>
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨e a, ZFSet.mem_range_self (f := e) a, ?_⟩
        have h := (ih (Constructible.snoc xs a)).mp ha
        simpa only [Constructible.Model.snoc_eq_finSnoc, ← Function.comp_def,
          Fin.comp_snoc] using h
      · rintro ⟨a, ha, hφ⟩
        obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp ha
        refine ⟨b, (ih (Constructible.snoc xs b)).mpr ?_⟩
        simpa only [Constructible.Model.snoc_eq_finSnoc, ← Function.comp_def,
          Fin.comp_snoc] using hφ

/-- Every countable seed in a nonempty set has an actual countable full
elementary hull, in the membership language used by Condensation. -/
theorem exists_countable_elementary_hull (U : ZFSet.{u}) [Nonempty (ZFCarrier U)]
    (seed : Set (ZFCarrier U)) (hseed : seed.Countable) :
    ∃ H : ZFSet.{u}, H ⊆ U ∧
      (∀ x : ZFCarrier U, x ∈ seed → x.val ∈ H) ∧
      Countable (ZFCarrier H) ∧ SatisfactionAbsolute (H : Set ZFSet.{u}) U := by
  classical
  letI : Language.setTheory.Structure (ZFCarrier U) := setTheoryStructure (zfCarrierMem U)
  let C := Substructure.closure (Language.setTheory.sum Language.setTheory.skolem₁) seed
  let S := C.elementarySkolem₁Reduct
  haveI : Countable C := @Set.Countable.substructure_closure
    (Language.setTheory.sum Language.setTheory.skolem₁) (ZFCarrier U) _ seed _ hseed
  haveI : Countable S := inferInstanceAs (Countable C)
  let e : S → ZFSet.{u} := fun x => x.val.val
  have he : Function.Injective e := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  let H : ZFSet.{u} := ZFSet.range e
  have hHU : H ⊆ U := by
    intro x hx
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hx
    exact s.val.property
  have hCount : Countable (ZFCarrier H) := by
    have hpre : ∀ x : ZFCarrier H, ∃ s : S, e s = x.val :=
      fun x => ZFSet.mem_range.mp x.property
    choose f hf using hpre
    apply Function.Injective.countable (f := f)
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg e h).trans (hf y))
  refine ⟨H, hHU, ?_, hCount, ?_⟩
  · intro x hx
    exact ZFSet.mem_range_self (f := e)
      (⟨x, Substructure.subset_closure hx⟩ : S)
  · intro n φ xs hxs
    have hpre : ∀ i, ∃ s : S, e s = xs i :=
      fun i => ZFSet.mem_range.mp (hxs i)
    choose ys hys using hpre
    have heys : (fun i => e (ys i)) = xs := funext hys
    have hpure : (setTheoryStructure (fun x y : S => e x ∈ e y)) =
        @Substructure.inducedStructure Language.setTheory (ZFCarrier U) _ S.toSubstructure := by
      apply FirstOrder.Language.Structure.ext
      · funext n f
        nomatch f
      · funext n r xs
        cases r
        rfl
    have helem := S.subtype.map_boundedFormula (toBoundedFormula φ) Empty.elim ys
    have hempty : S.subtype ∘ (Empty.elim : Empty → S) =
        (Empty.elim : Empty → ZFCarrier U) := funext (fun e => nomatch e)
    rw [hempty] at helem
    have hsmall : FOFormula.Satisfies (fun x y : S => e x ∈ e y) φ ys ↔
        @BoundedFormula.Realize Language.setTheory S
          (@Substructure.inducedStructure Language.setTheory (ZFCarrier U) _ S.toSubstructure)
          Empty n (toBoundedFormula φ) Empty.elim ys := by
      have h := (realizes_toBoundedFormula (fun x y : S => e x ∈ e y) φ ys).symm
      change _ ↔ @BoundedFormula.Realize Language.setTheory S
        (setTheoryStructure (fun x y : S => e x ∈ e y)) _ _ _ _ _ at h
      rwa [hpure] at h
    have hbig := (realizes_toBoundedFormula (zfCarrierMem U) φ
      (fun i => (ys i).val)).trans (satisfies_subtype_iff_satisfiesIn U φ (fun i => (ys i).val))
    have hres := (satisfies_range e he φ ys).symm.trans
      (hsmall.trans (helem.symm.trans hbig))
    change SatisfiesIn (H : Set ZFSet.{u}) φ (fun i => e (ys i)) ↔
      SatisfiesIn (U : Set ZFSet.{u}) φ (fun i => e (ys i)) at hres
    simpa only [heys] using hres

theorem countable_range {A : Type v} [Countable A] (e : A → ZFSet.{u}) :
    Countable (ZFCarrier (ZFSet.range e)) := by
  classical
  have hpre : ∀ x : ZFCarrier (ZFSet.range e), ∃ s : A, e s = x.val :=
    fun x => ZFSet.mem_range.mp x.property
  choose f hf using hpre
  apply Function.Injective.countable (f := f)
  intro x y h
  exact Subtype.ext ((hf x).symm.trans ((congrArg e h).trans (hf y)))

end OneYTruth.CountableSetHull
