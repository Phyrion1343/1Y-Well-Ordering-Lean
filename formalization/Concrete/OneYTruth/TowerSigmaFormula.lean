import OneYTruth.UniformWitnessBound
import OneYTruth.TowerRestrictionCertificate
import OneYTruth.InternalActualStep

/-! The complete bounded-tower candidate has three existential witnesses:
the stage domain, its closed ordinal factor, and a common local-witness bound.
All stage/entry/local-witness quantifiers in the remaining matrix are bounded. -/

namespace OneYTruth.TowerSigma

open Constructible Constructible.Delta0Formula CodedPaths BoundedFilterGraph

universe u v

def successorAt {n : Nat} (out a : Fin n) : Delta0Formula n :=
  .conj (.boundedAll out (.disj (.eq (Fin.last n) a.castSucc) (.mem (Fin.last n) a.castSucc)))
    (.conj (.mem a out) (subsetAt a out))

theorem satisfies_successorAt {n : Nat} (out a : Fin n) (p : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (successorAt out a) p ↔ p out = insert (p a) (p a) := by
  simp only [successorAt,Satisfies,satisfies_boundedAll,satisfies_disj,satisfies_subsetAt,
    snoc_last,snoc_castSucc]
  change ((∀ x ∈ p out, x = p a ∨ x ∈ p a) ∧ p a ∈ p out ∧ p a ⊆ p out) ↔ _
  constructor
  · rintro ⟨hh,ha,hsub⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_insert_iff]
    exact ⟨hh x,fun h => h.elim (fun he => he ▸ ha) (fun hx => hsub hx)⟩
  · rintro h
    rw [h]
    simp only [ZFSet.mem_insert_iff,true_or,true_and]
    exact ⟨fun _ hx => hx,fun _ hx => ZFSet.mem_insert_iff.mpr (Or.inr hx)⟩

def coversAt {n : Nat} (D g : Fin n) : Delta0Formula n :=
  .conj (.boundedAll D (.boundedEx g.castSucc
    (componentEqAt false (Fin.last (n+1)) (Fin.last n).castSucc)))
    (.boundedAll g (.boundedEx D.castSucc
      (componentEqAt false (Fin.last n).castSucc (Fin.last (n+1)))))

theorem satisfies_coversAt {n : Nat} (D g : Fin n) (p : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (coversAt D g) p ↔
      (∀ x ∈ p D, ∃ e ∈ p g, Component false e x) ∧
      (∀ e ∈ p g, ∃ x ∈ p D, Component false e x) := by
  simp only [coversAt,Satisfies,satisfies_boundedAll,satisfies_componentEqAt,snoc_last,snoc_castSucc]

/-- Fixed13, graph, entry; then stage, output, restriction, 21 local witnesses. -/
def localMap : Fin 37 → Fin 39 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,15,17,16,
    18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]

def entryMatrix : Delta0Formula 39 :=
  .conj (kuratowskiPairEqAt 14 15 16)
    (.conj (TowerRestriction.certificate.rename ![15,13,17])
      (GraphStepSigma.matrix.rename localMap))

def entryCertificate : Delta0Formula 16 := BoundedExistentialBlock.certificate 24 entryMatrix

attribute [irreducible] entryCertificate

def entryMap : Fin 16 → Fin 18 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,17,16]

/-- Fixed13, proposed graph, stage domain, closed ordinal factor, witness bound. -/
def matrix : Delta0Formula 17 :=
  .conj (successorAt 15 1)
    (.conj (productAt 14 5 15)
      (.conj (coversAt 14 13)
        (.boundedAll 13 (entryCertificate.rename entryMap))))

def query (K : Nat) (J : Type v) :=
  (ofConstructibleDeltaZero K J matrix).ex.ex.ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query K J) :=
  .ex (.ex (.ex (.deltaZero (ofConstructibleDeltaZero_isDeltaZero K J matrix))))

end OneYTruth.TowerSigma
