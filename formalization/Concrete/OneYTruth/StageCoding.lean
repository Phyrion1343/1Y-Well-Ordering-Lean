import OneYTruth.ExternalTower
import OneYTruth.ConstructibleDiagramSources
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookSetWellFounded

/-! # The actual bounded tower index set and its bounded lexicographic relation

The whole stage-code domain, and each actual predecessor set, belong to L.
This does not assert that the recursively constructed truth graph belongs to L.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Delta0Formula Constructible.FiniteSequenceZF
open Constructible.Model Constructible.Godel CodedPaths InternalProducts
open Constructible.IndexedSequenceZF
open ConstructibleDiagramSources ConstructibleBoundedIteration FormulaCode

universe u

noncomputable def stageSet (κ : Ordinal.{u}) : ZFSet.{u} := ZFSet.range (@stageCode κ)

theorem stageSet_eq_product (κ : Ordinal.{u}) :
    stageSet κ = pairProduct Ordinal.omega0.toZFSet (Order.succ κ).toZFSet := by
  apply ZFSet.ext
  intro z
  rw [stageSet, ZFSet.mem_range, pairProduct_eq_F2, mem_F2_iff]
  constructor
  · rintro ⟨⟨k, η⟩, he⟩
    exact ⟨natCode k, (mem_omega_iff_exists_natCode _).mpr ⟨k, rfl⟩,
      η.val.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ_iff.mpr η.property), he.symm⟩
  · rintro ⟨k, hk, η, hη, he⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_exists_natCode _).mp hk
    obtain ⟨η, hηlt, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη
    exact ⟨(k, ⟨η, Order.lt_succ_iff.mp hηlt⟩), he.symm⟩

theorem stageSet_mem_L (κ : Ordinal.{u}) : stageSet κ ∈ L := by
  rw [stageSet_eq_product]
  exact pairProduct_mem_L (ordinal_toZFSet_mem_L _) (ordinal_toZFSet_mem_L _)

theorem stageCode_mem_stageSet {κ : Ordinal.{u}} (s : Stage κ) : stageCode s ∈ stageSet κ :=
  ZFSet.mem_range_self s

theorem stageCode_mem_L {κ : Ordinal.{u}} (s : Stage κ) : stageCode s ∈ L :=
  mem_L_of_mem (stageCode_mem_stageSet s) (stageSet_mem_L κ)

/-- Membership comparison of the same literal pair component at two nodes.
All component witnesses are bounded by a pair and one of its members. -/
def componentMemAt {n : Nat} (right : Bool) (p q : Fin n) : Delta0Formula n :=
  .boundedEx q (.boundedEx (Fin.last n)
    (.conj (componentEqAt right q.castSucc.castSucc (Fin.last (n+1)))
      (pathMemAt [right] p.castSucc.castSucc (Fin.last (n+1)))))

theorem satisfies_componentMemAt {n : Nat} (right : Bool) (p q : Fin n)
    (v : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (componentMemAt right p q) v ↔
      ∃ a b, Component right (v p) a ∧ Component right (v q) b ∧ a ∈ b := by
  simp only [componentMemAt, Satisfies, satisfies_componentEqAt, satisfies_pathMemAt,
    snoc_last, snoc_castSucc, Follows, exists_eq_right]
  constructor
  · rintro ⟨box, _, b, _, hb, a, ha, hab⟩
    exact ⟨a, b, ha, hb, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨box, hbox, hbbox⟩ := component_bounded hb
    exact ⟨box, hbox, b, hbbox, hb, a, ha, hab⟩

/-- Pure bounded formula on the two actual stage codes. -/
def earlierFormula : Delta0Formula 2 :=
  .disj (componentMemAt false 0 1)
    (.conj (pathsEqualAt [false] [false] 0 1) (componentMemAt true 0 1))

theorem satisfies_earlierFormula {κ : Ordinal.{u}} (s t : Stage κ) :
    Satisfies ZFMem earlierFormula ![stageCode s, stageCode t] ↔ Earlier s t := by
  simp [earlierFormula, satisfies_disj, Satisfies, satisfies_componentMemAt,
    satisfies_pathsEqualAt, stageCode, Follows, natCode_inj]
  constructor
  · rintro (h | ⟨hk, hη⟩)
    · exact Prod.Lex.left _ _ h
    · rcases s with ⟨k, η⟩
      rcases t with ⟨j, ξ⟩
      dsimp at hk
      subst j
      exact Prod.Lex.right _ hη
  · intro h
    cases h with
    | left _ _ h => exact Or.inl h
    | right _ h => exact Or.inr ⟨rfl, h⟩

def CodedEarlier (κ : Ordinal.{u}) (a b : ZFSet.{u}) : Prop :=
  ∃ s t : Stage κ, stageCode s = a ∧ stageCode t = b ∧ Earlier s t

theorem codedEarlier_codes {κ : Ordinal.{u}} (s t : Stage κ) :
    CodedEarlier κ (stageCode s) (stageCode t) ↔ Earlier s t := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    have hp' : p = s := stageCode_injective hp
    have hq' : q = t := stageCode_injective hq
    simpa only [hp', hq'] using hpq
  · intro h
    exact ⟨s, t, rfl, rfl, h⟩

noncomputable def decodeStage (κ : Ordinal.{u}) (z : ZFSet.{u}) : Stage κ := by
  classical
  exact if h : ∃ s : Stage κ, stageCode s = z then h.choose else (0, ⟨0, zero_le⟩)

theorem decodeStage_code {κ : Ordinal.{u}} (s : Stage κ) : decodeStage κ (stageCode s) = s := by
  rw [decodeStage, dif_pos ⟨s, rfl⟩]
  exact stageCode_injective (Exists.choose_spec (⟨s, rfl⟩ : ∃ t : Stage κ, stageCode t = stageCode s))

theorem codedEarlier_wellFounded (κ : Ordinal.{u}) : WellFounded (CodedEarlier κ) := by
  apply Subrelation.wf (r := InvImage (@Earlier κ) (decodeStage κ))
  · rintro a b ⟨s, t, rfl, rfl, h⟩
    change Earlier (decodeStage κ (stageCode s)) (decodeStage κ (stageCode t))
    rwa [decodeStage_code, decodeStage_code]
  · exact InvImage.wf _ (earlier_wellFounded κ)

noncomputable def stagePredecessors (κ : Ordinal.{u}) (z : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => CodedEarlier κ w z) (stageSet κ)

theorem mem_stagePredecessors {κ : Ordinal.{u}} {w z : ZFSet.{u}} :
    w ∈ stagePredecessors κ z ↔ CodedEarlier κ w z := by
  rw [stagePredecessors, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨s, t, rfl, rfl, hs⟩ := h
    exact ⟨stageCode_mem_stageSet s, s, t, rfl, rfl, hs⟩

theorem stagePredecessors_mem_L {κ : Ordinal.{u}} (s : Stage κ) :
    stagePredecessors κ (stageCode s) ∈ L := by
  let φ : Delta0Formula 2 := earlierFormula.rename ![1, 0]
  have hsep := deltaSep_mem_L φ ![⟨stageCode s, stageCode_mem_L s⟩]
    ⟨stageSet κ, stageSet_mem_L κ⟩
  have heq : deltaSep φ ![stageCode s] (stageSet κ) = stagePredecessors κ (stageCode s) := by
    apply ZFSet.ext
    intro z
    rw [deltaSep, ZFSet.mem_sep, stagePredecessors, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    obtain ⟨t, rfl⟩ := ZFSet.mem_range.mp hz
    dsimp only [φ]
    rw [satisfies_rename]
    have hv : (fun i => snoc ![stageCode s] (stageCode t) (![1, 0] i)) =
        ![stageCode t, stageCode s] := by funext i; fin_cases i <;> rfl
    rw [hv, satisfies_earlierFormula, codedEarlier_codes]
  change deltaSep φ ![stageCode s] (stageSet κ) ∈ L at hsep
  rwa [heq] at hsep

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.stageSet_mem_L
#print axioms OneYTruth.ExternalTower.satisfies_earlierFormula
#print axioms OneYTruth.ExternalTower.codedEarlier_wellFounded
#print axioms OneYTruth.ExternalTower.stagePredecessors_mem_L
