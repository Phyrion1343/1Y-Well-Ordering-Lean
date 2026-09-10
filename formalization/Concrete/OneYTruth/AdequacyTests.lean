import OneYTruth.RootSemantics
import OneYTruth.SchemaTests

/-!
# A single bounded set test for every canonical expanded schema

The full closed-stage tower and both test families are actual set ranges.
Their comparison is a bounded formula. No claim of their internal existence
is built into the definitions or into the equivalence with Adequate.
-/

namespace OneYTruth.AdequacyTests

open Constructible FirstOrder FirstOrder.Language ExternalTower FormulaCode SchemaTests
open RootSemantics

universe u v

noncomputable def flatten {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) (F : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun w : Σ i : I, ZFCarrier (F i) => ZFSet.pair (code w.1) w.2.val)

theorem mem_flatten_iff {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) (hi : Function.Injective code) (F : I → ZFSet.{u})
    (i : I) (x : ZFSet.{u}) : ZFSet.pair (code i) x ∈ flatten code F ↔ x ∈ F i := by
  constructor
  · intro h
    obtain ⟨⟨j, y⟩, he⟩ := ZFSet.mem_range.mp h
    obtain ⟨hij, hy⟩ := ZFSet.pair_inj.mp he
    change code j = code i at hij
    have hji : j = i := hi hij
    subst j
    change y.val = x at hy
    exact hy ▸ y.property
  · intro h
    exact ZFSet.mem_range_self (f := fun w : Σ i : I, ZFCarrier (F i) =>
      ZFSet.pair (code w.1) w.2.val) ⟨i, ⟨x, h⟩⟩

theorem flatten_subset_iff {I : Type v} [Small.{u} I]
    (code : I → ZFSet.{u}) (hi : Function.Injective code) (F G : I → ZFSet.{u}) :
    flatten code F ⊆ flatten code G ↔ ∀ i, F i ⊆ G i := by
  constructor
  · intro h i x hx
    exact (mem_flatten_iff code hi G i x).mp (h ((mem_flatten_iff code hi F i x).mpr hx))
  · intro h p hp
    obtain ⟨⟨i, x⟩, rfl⟩ := ZFSet.mem_range.mp hp
    exact (mem_flatten_iff code hi G i x.val).mpr (h i x.property)

/-- Includes η=κ, which the auxiliary open-stage uniformSet deliberately omits. -/
noncomputable def closedTruth {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  flatten (@stageCode κ) (truth U)

noncomputable def allSeparationTests {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  flatten (@stageCode κ) (fun s => separationTests (k := s.1)
    (ordinalIndexCode (η := s.2.val)) U)

noncomputable def allCollectionTests {κ : Ordinal.{u}} (U : ZFSet.{u}) : ZFSet.{u} :=
  flatten (@stageCode κ) (fun s => collectionTests (k := s.1)
    (ordinalIndexCode (η := s.2.val)) U)

theorem allSeparationTests_subset_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    @allSeparationTests κ U ⊆ @closedTruth κ U ↔
      ∀ s : Stage κ, InternalClosure.HasSeparation (interpretation U s) := by
  rw [allSeparationTests, closedTruth, flatten_subset_iff stageCode stageCode_injective]
  apply forall_congr'
  intro s
  rw [truth_eq_satisfactionSet]
  exact separationTests_subset_iff ordinalIndexCode ordinalIndexCode_injective _ rfl

theorem allCollectionTests_subset_iff {κ : Ordinal.{u}} (U : ZFSet.{u}) :
    @allCollectionTests κ U ⊆ @closedTruth κ U ↔
      ∀ s : Stage κ, InternalClosure.HasCollection (interpretation U s) := by
  rw [allCollectionTests, closedTruth, flatten_subset_iff stageCode stageCode_injective]
  apply forall_congr'
  intro s
  rw [truth_eq_satisfactionSet]
  exact collectionTests_subset_iff ordinalIndexCode ordinalIndexCode_injective _ rfl

theorem adequate_iff_tests (a : Ordinal.{u}) :
    Adequate a ↔ Ordinal.omega0 < a ∧ Order.IsSuccLimit a ∧
      @allSeparationTests a (LStageZF a) ⊆ @closedTruth a (LStageZF a) ∧
      @allCollectionTests a (LStageZF a) ⊆ @closedTruth a (LStageZF a) := by
  rw [allSeparationTests_subset_iff, allCollectionTests_subset_iff]
  constructor
  · rintro ⟨hω, hlim, h⟩
    exact ⟨hω, hlim, (fun s => (h s.1 s.2.val s.2.property).1),
      (fun s => (h s.1 s.2.val s.2.property).2)⟩
  · rintro ⟨hω, hlim, hs, hc⟩
    exact ⟨hω, hlim, fun k η hηa => ⟨hs (k, ⟨η, hηa⟩), hc (k, ⟨η, hηa⟩)⟩⟩

theorem realize_check_iff_adequate {a : Ordinal.{u}}
    (hω : Ordinal.omega0 < a) (hlim : Order.IsSuccLimit a)
    {W : ZFSet.{u}} {K : Nat} {J : Type v} (hW : W.IsTransitive)
    (N : Interpretation K J (ZFCarrier W)) (hNmem : N.mem = zfCarrierMem W)
    (p : Fin 3 → ZFCarrier W)
    (hp0 : (p 0).val = @allSeparationTests a (LStageZF a))
    (hp1 : (p 1).val = @allCollectionTests a (LStageZF a))
    (hp2 : (p 2).val = @closedTruth a (LStageZF a)) :
    realize N (mixedCheckFormula K J) Empty.elim p ↔ Adequate a := by
  rw [mixedCheckFormula, realize_ofConstructibleDeltaZero_absolute hW N hNmem]
  simp only [checkFormula, Delta0Formula.Satisfies, Delta0Formula.satisfies_subsetAt]
  change ((p 0).val ⊆ (p 2).val ∧ (p 1).val ⊆ (p 2).val) ↔ _
  rw [hp0, hp1, hp2, adequate_iff_tests]
  simp only [hω, hlim, true_and]

end OneYTruth.AdequacyTests

#print axioms OneYTruth.AdequacyTests.adequate_iff_tests
#print axioms OneYTruth.AdequacyTests.realize_check_iff_adequate
