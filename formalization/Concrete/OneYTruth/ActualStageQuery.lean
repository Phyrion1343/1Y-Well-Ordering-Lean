import OneYTruth.OrdinalStageQuery
import OneYTruth.BoundedDefSource

/-! # The actual canonical Sigma-one definition of U = L_a

All local Def, satisfaction, syntax, assignment, and witness-bound inputs
of the abstract history skeleton are instantiated here. The four raw
parameters are a, omega, zero, and U.
-/

namespace OneYTruth.ActualStageQuery

open Constructible Constructible.Model Constructible.Delta0Formula
open OrdinalStageHistory RootSemantics InternalClosure

universe u v

noncomputable def query (K : Nat) (J : Type v) :=
  stageQuery K J BoundedDefSource.formula.{u}

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  stageQuery_isSigmaOne K J _

theorem query_sound {K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (hVL : ∀ x ∈ V, x ∈ L)
    (N : Interpretation K J (ZFCarrier V)) (hmem : N.mem = zfCarrierMem V)
    (a : Ordinal.{u}) (p : Fin 4 → ZFCarrier V)
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) (h : realize N (query.{u,v} K J) Empty.elim p) :
    (p 3).val = LStageZF a := by
  apply stageQuery_sound BoundedDefSource.formula hV N hmem a p ha hOmega hZero ?_ h
  intro S hS D hD B hB hδ
  let q : Fin 4 → ZFCarrier V := ![⟨S,hS⟩,p 1,p 2,⟨D,hD⟩]
  apply BoundedDefSource.sound hV hVL q ⟨B,hB⟩ hOmega hZero
  have he : snoc (fun i => (q i).val) B = ![S,Ordinal.omega0.toZFSet,∅,D,B] := by
    funext i
    fin_cases i <;> first | exact hOmega | exact hZero | rfl
  rw [he]
  exact hδ

theorem realize_query_iff {K : Nat} {J : Type v} {β : Ordinal.{u}}
    (hβ : Adequate β) (N : Interpretation K J (ZFCarrier (LStageZF β)))
    (hmem : N.mem = zfCarrierMem (LStageZF β)) (a : Ordinal.{u})
    (p : Fin 4 → ZFCarrier (LStageZF β))
    (ha : (p 0).val = a.toZFSet) (hOmega : (p 1).val = Ordinal.omega0.toZFSet)
    (hZero : (p 2).val = ∅) :
    realize N (query.{u,v} K J) Empty.elim p ↔ (p 3).val = LStageZF a := by
  have hV : (LStageZF β).IsTransitive := LStageZF_isTransitive β
  have hVL : ∀ x ∈ LStageZF β, x ∈ L := fun _ hx => mem_L_of_mem hx (LStageZF_mem_L β)
  constructor
  · exact query_sound hV hVL N hmem a p ha hOmega hZero
  · intro hU
    have haβ : a < β :=
      MostowskiCollapse.BareStageCondensation.ordinal_lt_of_toZFSet_mem_LStageZF (ha ▸ (p 0).property)
    apply stageQuery_complete BoundedDefSource.formula hβ N hmem a haβ p ha hOmega hZero hU
    · intro S D B C hBC hδ
      have he (W : ZFSet.{u}) : snoc ![S,Ordinal.omega0.toZFSet,∅,D] W =
          ![S,Ordinal.omega0.toZFSet,∅,D,W] := by funext i; fin_cases i <;> rfl
      have hh := BoundedDefSource.monotone ![S,Ordinal.omega0.toZFSet,∅,D] hBC
      rw [he,he] at hh
      exact hh hδ
    · intro i hia
      have hiβ := hia.trans haβ
      have hsiβ : Order.succ i < β := (Order.succ_le_iff.mpr hia).trans_lt haβ
      let q : Fin 4 → ZFCarrier (LStageZF β) :=
        ![⟨LStageZF i,LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 hiβ⟩,p 1,p 2,
          ⟨LStageZF (Order.succ i),LStageZF_mem_LStageZF_of_lt_isSuccLimit hβ.2.1 hsiβ⟩]
      let N0 := ExternalTower.interpretation (κ := β) (LStageZF β) (0, ⟨0,zero_le⟩)
      have hs := hβ.2.2 0 0 zero_le
      obtain ⟨B,hB⟩ := BoundedDefSource.complete hV hVL N0 rfl hs.2 hs.1
        (fun _ hx _ hy => orderedPair_mem_LStageZF_of_isSuccLimit hβ.2.1 hx hy)
        (fun _ hx => sUnion_mem_LStageZF_of_isSuccLimit hβ.2.1 hx)
        q hOmega hZero (LStageZF_succ i)
      refine ⟨B.val,B.property,?_⟩
      have he : snoc (fun j => (q j).val) B.val =
          ![LStageZF i,Ordinal.omega0.toZFSet,∅,LStageZF (Order.succ i),B.val] := by
        funext j
        fin_cases j <;> first | exact hOmega | exact hZero | rfl
      rwa [he] at hB

end OneYTruth.ActualStageQuery

#print axioms OneYTruth.ActualStageQuery.query_isSigmaOne
#print axioms OneYTruth.ActualStageQuery.query_sound
#print axioms OneYTruth.ActualStageQuery.realize_query_iff
