import OneYTruth.InternalStageDomain
import OneYTruth.StageRecursionL

/-! # The actual weak environment needed by internal stage recursion

Every field below is supplied for an adequate Lβ. No Power Set axiom or
set model of full ZF occurs, and no truth graph is among the fields.
-/

namespace OneYTruth.ExternalTower

open Constructible Constructible.Model InternalClosure RootSemantics

universe u

structure RecursionEnvironment (V : ZFSet.{u}) : Prop where
  transitive : V.IsTransitive
  separation : HasFOSeparation V
  replacement : HasFOReplacement V
  singleton_mem : ∀ {a : ZFSet.{u}}, a ∈ V → ({a} : ZFSet.{u}) ∈ V
  union_mem : ∀ {a b : ZFSet.{u}}, a ∈ V → b ∈ V → a ∪ b ∈ V
  orderedPair_mem : ∀ {a b : ZFSet.{u}}, a ∈ V → b ∈ V → ZFSet.pair a b ∈ V
  sUnion_mem : ∀ {a : ZFSet.{u}}, a ∈ V → ZFSet.sUnion a ∈ V

theorem recursionEnvironment_of_adequate {β : Ordinal.{u}} (h : Adequate β) :
    RecursionEnvironment (LStageZF β) where
  transitive := LStageZF_isTransitive β
  separation := h.pureFOSchemas.1
  replacement := h.pureFOSchemas.2
  singleton_mem := singleton_mem_LStageZF_of_isSuccLimit h.2.1
  union_mem := union_mem_LStageZF_of_isSuccLimit h.2.1
  orderedPair_mem := orderedPair_mem_LStageZF_of_isSuccLimit h.2.1
  sUnion_mem := sUnion_mem_LStageZF_of_isSuccLimit h.2.1

namespace RecursionEnvironment

variable {V : ZFSet.{u}} (E : RecursionEnvironment V)
include E

theorem stageCode_mem {κ : Ordinal.{u}} (hsource : stageSet κ ∈ V) (s : Stage κ) :
    stageCode s ∈ V := E.transitive.mem_trans (stageCode_mem_stageSet s) hsource

theorem stagePredecessors_mem {κ : Ordinal.{u}} (hsource : stageSet κ ∈ V) (s : Stage κ) :
    stagePredecessors κ (stageCode s) ∈ V :=
  stagePredecessors_mem_of_foSeparation E.transitive E.separation hsource s

theorem stageLocalDomain_mem {κ : Ordinal.{u}} (hsource : stageSet κ ∈ V) (s : Stage κ) :
    stageLocalDomain s ∈ V :=
  E.union_mem (E.singleton_mem (E.stageCode_mem hsource s)) (E.stagePredecessors_mem hsource s)

theorem value_mem_of_restrictionGraph {d g : ZFSet.{u}}
    {F : ZFSet.{u} → ZFSet.{u}} (hg : g = predecessorRestrictionGraph d F)
    (hgV : g ∈ V) {z : ZFSet.{u}} (hz : z ∈ d) : F z ∈ V := by
  have hp : ZFSet.pair z (F z) ∈ V := by
    apply E.transitive.mem_trans ?_ hgV
    rw [hg]
    exact pair_mem_predecessorRestrictionGraph F hz
  have hb : ({z, F z} : ZFSet.{u}) ∈ ZFSet.pair z (F z) := by simp [ZFSet.pair]
  exact E.transitive.mem_trans (by simp : F z ∈ ({z, F z} : ZFSet.{u}))
    (E.transitive.mem_trans hb hp)

end RecursionEnvironment

end OneYTruth.ExternalTower

#print axioms OneYTruth.ExternalTower.recursionEnvironment_of_adequate
