import OneYTruth.StageCoding
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalDomainLCarrier

/-! # The actual stage order as a textbook recursion domain over L

All domain, relation, predecessor closure, and local-domain requirements are
proved for the actual lexicographic stage set. No recursive truth set is an
input to these constructions.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model Constructible.Delta0Formula

universe u

theorem earlier_trans {κ : Ordinal.{u}} {s t v : Stage κ}
    (h : Earlier s t) (g : Earlier t v) : Earlier s v := by
  cases h with
  | left _ _ h =>
      cases g with
      | left _ _ g => exact Prod.Lex.left _ _ (Nat.lt_trans h g)
      | right _ g => exact Prod.Lex.left _ _ h
  | right _ h =>
      cases g with
      | left _ _ g => exact Prod.Lex.left _ _ g
      | right _ g => exact Prod.Lex.right _ (lt_trans h g)

theorem codedEarlier_trans {κ : Ordinal.{u}} {a b c : ZFSet.{u}}
    (h : CodedEarlier κ a b) (g : CodedEarlier κ b c) : CodedEarlier κ a c := by
  obtain ⟨s, t, rfl, rfl, hst⟩ := h
  obtain ⟨p, q, hp, rfl, hpq⟩ := g
  have he : p = t := stageCode_injective hp
  subst p
  exact ⟨s, q, rfl, rfl, earlier_trans hst hpq⟩

def stageClassRelation (κ : Ordinal.{u}) : Set (Tuple ZFSet.{u} 2) :=
  fun v => CodedEarlier κ (v 0) (v 1)

theorem stage_relationOn (κ : Ordinal.{u}) :
    IsRelationOn (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ) := by
  rintro v ⟨s, t, hs, ht, _⟩ i
  fin_cases i
  · change v 0 ∈ stageSet κ
    rw [← hs]
    exact stageCode_mem_stageSet s
  · change v 1 ∈ stageSet κ
    rw [← ht]
    exact stageCode_mem_stageSet t

theorem stage_setMinima (κ : Ordinal.{u}) :
    HasSetMinimaOn (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ) := by
  apply (hasSetMinimaOn_iff_wellFounded_zfCarrier _ _).mpr
  exact InvImage.wf Subtype.val (codedEarlier_wellFounded κ)

theorem stage_setPredecessors (κ : Ordinal.{u}) :
    HasSetPredecessorsOn (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ) := by
  intro x _
  refine ⟨stagePredecessors κ x, ?_⟩
  intro y
  rw [mem_stagePredecessors]
  constructor
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨s, t, rfl, rfl, _⟩ := h
    exact stageCode_mem_stageSet s
  · exact And.right

theorem stage_wellFoundedSetLike (κ : Ordinal.{u}) :
    IsWellFoundedSetLikeOn (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ) :=
  ⟨stage_relationOn κ, stage_setMinima κ, stage_setPredecessors κ⟩

theorem stage_predecessorsClosedIn_L (κ : Ordinal.{u}) :
    PredecessorsClosedIn (L : Set ZFSet.{u}) (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ) :=
  fun _ _ _ hy _ => mem_L_of_mem hy (stageSet_mem_L κ)

theorem displayedPredecessors_eq_stage {κ : Ordinal.{u}} (s : Stage κ) :
    displayedPredecessors (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ)
      (stage_setPredecessors κ) (stageCode s) = stagePredecessors κ (stageCode s) := by
  apply (eq_displayedPredecessors_of_isPredecessorSet (stage_setPredecessors κ)
    (stageCode_mem_stageSet s) ?_).symm
  intro y
  rw [mem_stagePredecessors]
  exact ⟨fun h => ⟨(stage_relationOn κ).left_mem h, h⟩, And.right⟩

noncomputable def stageLocalDomain {κ : Ordinal.{u}} (s : Stage κ) : ZFSet.{u} :=
  ({stageCode s} : ZFSet.{u}) ∪ stagePredecessors κ (stageCode s)

theorem mem_stageLocalDomain {κ : Ordinal.{u}} (s : Stage κ) (z : ZFSet.{u}) :
    z ∈ stageLocalDomain s ↔ z = stageCode s ∨ CodedEarlier κ z (stageCode s) := by
  simp only [stageLocalDomain, ZFSet.mem_union, ZFSet.mem_singleton, mem_stagePredecessors]

theorem localRecursionDomain_eq_stage {κ : Ordinal.{u}} (s : Stage κ) :
    localRecursionDomain (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ)
      (stage_setPredecessors κ) (stageCode s) = stageLocalDomain s := by
  have hself : stageCode s ∈ localRecursionDomain (stageSet κ : Set ZFSet.{u})
      (stageClassRelation κ) (stage_setPredecessors κ) (stageCode s) :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  have hsubset := localRecursionDomain_subset_of_closed (stage_setPredecessors κ)
    (stageCode_mem_stageSet s) ((mem_stageLocalDomain s _).mpr (Or.inl rfl))
    (D := (stageLocalDomain s : Set ZFSet.{u})) (by
      intro t ht y _ hyt
      apply (mem_stageLocalDomain s _).mpr
      rcases (mem_stageLocalDomain s _).mp ht with he | hts
      · subst t
        exact Or.inr hyt
      · exact Or.inr (codedEarlier_trans hyt hts))
  apply ZFSet.ext
  intro z
  refine ⟨fun hz => hsubset hz, ?_⟩
  intro hz
  rcases (mem_stageLocalDomain s _).mp hz with rfl | hzs
  · exact hself
  · exact localRecursionDomain_predecessorClosed (stage_relationOn κ) (stage_setPredecessors κ)
      (stageCode_mem_stageSet s) hself hzs

theorem stageLocalDomain_mem_L {κ : Ordinal.{u}} (s : Stage κ) : stageLocalDomain s ∈ L :=
  union_mem_L (singleton_mem_L (stageCode_mem_L s)) (stagePredecessors_mem_L s)

theorem localRecursionDomain_mem_L_stage {κ : Ordinal.{u}} (s : Stage κ) :
    localRecursionDomain (stageSet κ : Set ZFSet.{u}) (stageClassRelation κ)
      (stage_setPredecessors κ) (stageCode s) ∈ L := by
  rw [localRecursionDomain_eq_stage]
  exact stageLocalDomain_mem_L s

def stageClassFormula : Delta0Formula 2 := .mem 1 0

def stageRelationFormula : Delta0Formula 3 :=
  .conj (.mem 1 0) (.conj (.mem 2 0) (earlierFormula.rename ![1, 2]))

noncomputable def stageParams (κ : Ordinal.{u}) : Tuple LCarrier.{u} 1 :=
  ![⟨stageSet κ, stageSet_mem_L κ⟩]

theorem satisfies_stageClassFormula (κ : Ordinal.{u}) (z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem stageClassFormula.toFO (snoc (stageParams κ) z) ↔
      z.val ∈ stageSet κ := Iff.rfl

theorem satisfies_stageRelationFormula (κ : Ordinal.{u}) (y z : LCarrier.{u}) :
    FOFormula.Satisfies lCarrierMem stageRelationFormula.toFO
      (snoc (snoc (stageParams κ) y) z) ↔ ClassRel (stageClassRelation κ) y.val z.val := by
  rw [satisfies_toFO_lCarrier_absolute, satisfies_toFO]
  simp only [stageRelationFormula, Satisfies, satisfies_rename]
  change (y.val ∈ stageSet κ ∧ z.val ∈ stageSet κ ∧
    Satisfies ZFMem earlierFormula ![y.val, z.val]) ↔ CodedEarlier κ y.val z.val
  constructor
  · rintro ⟨hy, hz, h⟩
    obtain ⟨s, hs⟩ := ZFSet.mem_range.mp hy
    obtain ⟨t, ht⟩ := ZFSet.mem_range.mp hz
    rw [← hs, ← ht] at h
    exact ⟨s, t, hs, ht, (satisfies_earlierFormula s t).mp h⟩
  · rintro ⟨s, t, hs, ht, h⟩
    rw [← hs, ← ht]
    exact ⟨stageCode_mem_stageSet s, stageCode_mem_stageSet t, (satisfies_earlierFormula s t).mpr h⟩

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.stage_wellFoundedSetLike
#print axioms OneYTruth.ExternalTower.localRecursionDomain_mem_L_stage
#print axioms OneYTruth.ExternalTower.satisfies_stageRelationFormula
