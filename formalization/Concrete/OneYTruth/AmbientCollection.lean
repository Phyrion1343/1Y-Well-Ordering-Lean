import OneYTruth.InitialStageBounds
import OneYTruth.CollectionReplacement

/-!
# Actual Collection in L_(external omega_1)

Each member of the ambient L level is externally countable. For any total
relation on such a member, choose countably many witnesses and bound them
in a smaller L stage. That stage itself belongs to the ambient model and
is a Collection bound. The relation need not be constructible or definable.

In particular, every displayed mixed-language Collection instance holds.
This argument does not prove Separation: a subset picked by an arbitrary
external predicate need not be constructible.
-/

namespace OneYTruth.InitialStage

open Constructible FirstOrder FirstOrder.Language
open scoped Ordinal

universe u v

theorem countable_members (a : Ambient.{u}) : Countable (ZFCarrier a.val) := by
  obtain ⟨γ, hγ, haγ⟩ :=
    (mem_LStageZF_limit_iff (Cardinal.isSuccLimit_omega 1)).mp a.property
  haveI := countable_LStage hγ
  apply Function.Injective.countable (f := fun x : ZFCarrier a.val =>
    (⟨x.val, (LStageZF_isTransitive γ).mem_trans x.property haγ⟩ : ZFCarrier (LStageZF γ)))
  intro x y h
  exact Subtype.ext (congrArg (fun z : ZFCarrier (LStageZF γ) => z.val) h)

theorem countable_memberSet (a : Ambient.{u}) :
    Countable {x : Ambient.{u} // x.val ∈ a.val} := by
  haveI := countable_members a
  apply Function.Injective.countable (f := fun x : {x : Ambient.{u} // x.val ∈ a.val} =>
    (⟨x.val.val, x.property⟩ : ZFCarrier a.val))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ZFCarrier a.val => z.val) h

/-- Collection for an arbitrary external relation, with an actual internal bound. -/
theorem collection_bound (a : Ambient.{u}) (P : Ambient.{u} → Ambient.{u} → Prop)
    (h : ∀ x : Ambient.{u}, x.val ∈ a.val → ∃ y : Ambient.{u}, P x y) :
    ∃ b : Ambient.{u}, ∀ x : Ambient.{u}, x.val ∈ a.val →
      ∃ y : Ambient.{u}, y.val ∈ b.val ∧ P x y := by
  classical
  haveI := countable_memberSet a
  have hex : ∀ x : {x : Ambient.{u} // x.val ∈ a.val}, ∃ y : Ambient.{u}, P x.val y :=
    fun x => h x.val x.property
  choose y hy using hex
  obtain ⟨β, _, hβ⟩ := exists_stage_bound (Set.range y) (Set.countable_range y)
    ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩
  have hLβ : LStageZF β.val ∈ LStageZF (ω₁ : Ordinal.{u}) :=
    LStageZF_mono (Order.succ_le_iff.mpr β.property) (LStageZF_mem_succ β.val)
  refine ⟨⟨LStageZF β.val, hLβ⟩, ?_⟩
  intro x hx
  exact ⟨y ⟨x, hx⟩, hβ (Set.mem_range_self (f := y) ⟨x, hx⟩), hy ⟨x, hx⟩⟩

/-- Every actual formula's Collection instance is supplied, not postulated. -/
theorem ambient_hasCollection {k : Nat} {I : Type v}
    (N : OneYTruth.Interpretation k I Ambient.{u}) : InternalClosure.HasCollection N := by
  intro n φ params a h
  exact collection_bound a
    (fun x y => OneYTruth.realize N φ Empty.elim (Fin.snoc (Fin.snoc params x) y)) h

end OneYTruth.InitialStage
