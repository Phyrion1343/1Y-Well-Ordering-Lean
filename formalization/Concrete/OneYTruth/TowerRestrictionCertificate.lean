import OneYTruth.BoundedFilterGraph
import OneYTruth.GraphInputTower

/-! A predecessor restriction is checked as the exact bounded separation of
the candidate whole graph. It cannot silently change parent-stage data. -/

namespace OneYTruth.TowerRestriction

open Constructible Constructible.Delta0Formula CodedPaths ExternalTower

universe u

/-- Parameters: current stage, candidate graph entry. -/
def predicate : Delta0Formula 2 :=
  .boundedEx 1 (.boundedEx (Fin.last 2)
    (.conj (componentEqAt false 1 (Fin.last 3))
      (earlierFormula.rename ![Fin.last 3,0])))

theorem satisfies_predicate (x p : ZFSet.{u}) :
    Satisfies ZFMem predicate ![x,p] ↔
      ∃ y, Component false p y ∧ Satisfies ZFMem earlierFormula ![y,x] := by
  simp only [predicate,Satisfies,satisfies_componentEqAt,satisfies_rename,snoc_last,snoc_castSucc]
  change (∃ box ∈ p, ∃ y ∈ box, Component false p y ∧
    Satisfies ZFMem earlierFormula ![y,x]) ↔ _
  constructor
  · rintro ⟨box,_,y,_,hy,hr⟩
    exact ⟨y,hy,hr⟩
  · rintro ⟨y,hy,hr⟩
    obtain ⟨box,hbox,hybox⟩ := component_bounded hy
    exact ⟨box,hbox,y,hybox,hy,hr⟩

theorem satisfies_predicate_pair {κ : Ordinal.{u}} (s t : Stage κ) (T : ZFSet.{u}) :
    Satisfies ZFMem predicate ![stageCode s,ZFSet.pair (stageCode t) T] ↔ Earlier t s := by
  rw [satisfies_predicate]
  simp only [component_pair,Bool.false_eq_true,if_false,exists_eq_left]
  exact satisfies_earlierFormula t s

noncomputable def restrict (x g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => Satisfies ZFMem predicate ![x,p]) g

def certificate : Delta0Formula 3 := BoundedFilterGraph.filterFormula predicate

theorem satisfies_certificate (x g q : ZFSet.{u}) :
    Satisfies ZFMem certificate ![x,g,q] ↔ q = restrict x g := by
  change Satisfies ZFMem (BoundedFilterGraph.filterFormula predicate)
    (snoc (snoc ![x] g) q) ↔ _
  rw [BoundedFilterGraph.satisfies_filterFormula]
  rfl

theorem restrict_graph {κ : Ordinal.{u}} (U : ZFSet.{u}) (s : Stage κ) :
    restrict (stageCode s) (@graph κ U) =
      predecessorRestrictionGraph (stagePredecessors κ (stageCode s)) (codedTruth κ U) := by
  apply ZFSet.ext
  intro p
  rw [restrict,ZFSet.mem_sep,mem_predecessorRestrictionGraph_iff]
  constructor
  · rintro ⟨hg,hrel⟩
    obtain ⟨t,rfl⟩ := ZFSet.mem_range.mp hg
    exact ⟨stageCode t,mem_stagePredecessors.mpr ((codedEarlier_codes t s).mpr
      ((satisfies_predicate_pair s t _).mp hrel)),by simp only [codedTruth_code]⟩
  · rintro ⟨z,hz,he⟩
    obtain ⟨t,ht⟩ := ZFSet.mem_range.mp ((stage_relationOn κ).left_mem (mem_stagePredecessors.mp hz))
    rw [← ht,codedTruth_code] at he
    rw [← he]
    refine ⟨ZFSet.mem_range_self t,?_⟩
    apply (satisfies_predicate_pair s t _).mpr
    apply (codedEarlier_codes t s).mp
    rw [ht]
    exact mem_stagePredecessors.mp hz

end OneYTruth.TowerRestriction
