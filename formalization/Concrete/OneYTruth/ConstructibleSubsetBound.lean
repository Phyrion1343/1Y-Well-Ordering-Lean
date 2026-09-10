import OneYTruth.CountableSetHull
import OneYTruth.InitialStageBounds
import ConstructibleUniverse.SetTheory.ZFC.Constructible.StandardCondensation

/-!
# Constructible subsets of members of L_(external omega_1)

A constructible subset of any member of L_(omega_1) already belongs to
L_(omega_1). The proof uses an external countable elementary hull and the
actual Condensation Lemma. External countability is not confused with an
internal L-cardinality estimate.
-/

namespace OneYTruth.InitialStage

open Constructible Constructible.MostowskiCollapse
open scoped Cardinal Ordinal

universe u

theorem collapse_fixes_transitive_subset {T H : ZFSet.{u}}
    (hT : T.IsTransitive) (hTH : T ⊆ H) :
    ∀ x : ZFSet.{u}, x ∈ T → collapse H x = x := by
  intro x
  refine ZFSet.inductionOn (p := fun x => x ∈ T → collapse H x = x) x ?_
  intro x ih hx
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _, hvalue⟩
    have hy : y ∈ T := hT.mem_trans hyx hx
    have hyz : y = z := (ih y hyx hy).symm.trans hvalue
    simpa only [hyz] using hyx
  · intro hzx
    have hzT : z ∈ T := hT.mem_trans hzx hx
    exact ⟨z, hzx, hTH hzT, ih z hzx hzT⟩

theorem collapse_fixes_subset {T H s : ZFSet.{u}}
    (hT : T.IsTransitive) (hTH : T ⊆ H) (hsT : s ⊆ T) : collapse H s = s := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hys, _, hy⟩
    have hyz : y = z :=
      (collapse_fixes_transitive_subset hT hTH y (hsT hys)).symm.trans hy
    simpa only [hyz] using hys
  · intro hzs
    exact ⟨z, hzs, hTH (hsT hzs), collapse_fixes_transitive_subset hT hTH z (hsT hzs)⟩

/-- Countable elementary membership hulls collapse to a stage below the external omega_1. -/
theorem collapse_stage_lt_omega_one {θ : Ordinal.{u}} {H : ZFSet.{u}}
    (hθ : Order.IsSuccLimit θ) (hH : H ⊆ LStageZF θ)
    (helem : SatisfactionAbsolute (H : Set ZFSet.{u}) (LStageZF θ))
    [Countable (ZFCarrier H)] :
    ∃ β < (ω₁ : Ordinal.{u}), range H = LStageZF β := by
  obtain ⟨β, hβ⟩ := exists_collapse_eq_LStageZF_of_elementary_isSuccLimit hθ hH helem
  haveI : Countable (ZFCarrier (range H)) :=
    CountableSetHull.countable_range (fun x : ZFCarrier H => collapse H x.val)
  have hcard : ZFSet.card (range H) ≤ Cardinal.aleph0 := by
    have hmk := Cardinal.mk_le_aleph0 (α := ZFCarrier (range H))
    rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_le_aleph0] at hmk
    exact hmk
  have hβcard : β.card ≤ Cardinal.aleph0 :=
    (card_ordinal_le_card_LStageZF β).trans (by simpa only [hβ] using hcard)
  exact ⟨β, Cardinal.lt_omega_iff_card_lt.mpr (Cardinal.lt_aleph_one_iff.mpr hβcard), hβ⟩

/-- A constructible subset of a member of the ambient stage is itself internal. -/
theorem constructible_subset_mem_ambient {a s : ZFSet.{u}}
    (ha : a ∈ LStageZF (ω₁ : Ordinal.{u})) (hsa : s ⊆ a) (hsL : s ∈ L) :
    s ∈ LStageZF (ω₁ : Ordinal.{u}) := by
  classical
  obtain ⟨γ, hγκ, haγ⟩ := (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp ha
  obtain ⟨θ, hsθ⟩ := mem_L_iff.mp hsL
  let δ : Ordinal.{u} := max γ θ + Ordinal.omega0
  have hγδ : γ ≤ δ := (le_max_left γ θ).trans (le_self_add)
  have hθδ : θ ≤ δ := (le_max_right γ θ).trans (le_self_add)
  have hδ : Order.IsSuccLimit δ := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  let U : ZFSet.{u} := LStageZF δ
  have hsU : s ∈ U := LStageZF_mono hθδ hsθ
  have hTU : LStageZF γ ⊆ U := LStageZF_mono hγδ
  have hsT : s ⊆ LStageZF γ :=
    fun _ hx => (LStageZF_isTransitive γ).mem_trans (hsa hx) haγ
  haveI : Nonempty (ZFCarrier U) := ⟨⟨s, hsU⟩⟩
  let sU : ZFCarrier U := ⟨s, hsU⟩
  let t : Set (ZFCarrier U) := {x | x.val ∈ LStageZF γ}
  have ht : t.Countable := by
    haveI := countable_LStage hγκ
    apply Set.countable_coe_iff.mp
    apply Function.Injective.countable (f := fun x : t =>
      (⟨x.val.val, x.property⟩ : ZFCarrier (LStageZF γ)))
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZFCarrier (LStageZF γ) => z.val) h
  obtain ⟨H, hHU, hseed, hCount, helem⟩ :=
    CountableSetHull.exists_countable_elementary_hull U ({sU} ∪ t)
      ((Set.countable_singleton sU).union ht)
  haveI := hCount
  have hsH : s ∈ H := hseed sU (Or.inl (Set.mem_singleton sU))
  have hTH : LStageZF γ ⊆ H := by
    intro z hz
    exact hseed ⟨z, hTU hz⟩ (Or.inr hz)
  obtain ⟨β, hβκ, hβ⟩ := collapse_stage_lt_omega_one hδ hHU helem
  have hsRange : s ∈ range H := mem_range_iff.mpr
    ⟨s, hsH, collapse_fixes_subset (LStageZF_isTransitive γ) hTH hsT⟩
  exact LStageZF_mono hβκ.le (by simpa only [hβ] using hsRange)

end OneYTruth.InitialStage
