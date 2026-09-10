import OneYTruth.EndpointComparison
import OneYTruth.ConstructibleCodes

/-! The two permitted endpoint queries express the actual root relation. -/

namespace OneYTruth.EndpointComparison

open Constructible FirstOrder FirstOrder.Language ExternalTower FormulaCode
open SigmaComparison RootSemantics

universe u

def NodesBounded (nodes U : ZFSet.{u}) : Prop :=
  ∀ p ∈ nodes, ∃ e ∈ U, ∃ a ∈ U, ZFSet.pair e a = p

theorem bounded_pair_agree_iff {W : ZFSet.{u}} (hW : W.IsTransitive)
    (U : ZFCarrier W) (nodes S T : ZFSet.{u}) (hb : NodesBounded nodes U.val) :
    (∀ e : ZFCarrier W, e.val ∈ U.val →
      ∀ a : ZFCarrier W, a.val ∈ U.val →
        ZFSet.pair e.val a.val ∈ nodes →
          (ZFSet.pair e.val a.val ∈ S ↔ ZFSet.pair e.val a.val ∈ T)) ↔
      Agree nodes S T := by
  constructor
  · intro h p hp
    obtain ⟨e, he, a, ha, rfl⟩ := hb p hp
    exact h ⟨e, hW.mem_trans he U.property⟩ he ⟨a, hW.mem_trans ha U.property⟩ ha hp
  · intro h e _ a _ hp
    exact h _ hp

theorem canonical_nodesBounded {k : Nat} {η a : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) :
    NodesBounded (sigmaNodes (k := k) (ordinalIndexCode (η := η)) (LStageZF a))
      (LStageZF a) := by
  intro p hp
  obtain ⟨n, φ, _, xs, rfl⟩ := (mem_sigmaNodes_iff _ _ _).mp hp
  exact ⟨packedCode ordinalIndexCode ⟨n, φ⟩,
    packedCode_mem_LStageZF ha (ordinalIndexCode_mem_LStageZF hηa) _,
    assignmentCode xs, assignmentCode_mem_LStageZF ha (fun _ h => h) xs, rfl⟩

theorem named_comparison_iff_R {K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b)
    (hηθ : η < θ) (hθb : θ ≤ b)
    (p : Fin 4 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = LStageZF a)
    (hp1 : (p 1).val = sigmaNodes (k := K) (ordinalIndexCode (η := η)) (LStageZF a))
    (hp2 : (p 2).val = truth (LStageZF a) (K, ⟨η, hηa⟩)) :
    realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (comparison (namedQuery ⟨η, hηθ⟩)) Empty.elim p ↔ R K η a b := by
  haveI : Nonempty (ZFCarrier (LStageZF a)) :=
    ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit ha⟩⟩
  rw [realize_named_comparison (LStageZF_isTransitive b) _ rfl]
  change (∀ e : ZFCarrier (LStageZF b), e.val ∈ (p 0).val →
    ∀ x : ZFCarrier (LStageZF b), x.val ∈ (p 0).val →
      ZFSet.pair e.val x.val ∈ (p 1).val →
        (ZFSet.pair e.val x.val ∈ (p 2).val ↔
          ZFSet.pair e.val x.val ∈ truth (LStageZF b) (K, ⟨η, hηa.trans hab.le⟩))) ↔ _
  have hb : NodesBounded ((p 1).val) ((p 0).val) := by
    rw [hp0, hp1]
    exact canonical_nodesBounded ha hηa
  rw [bounded_pair_agree_iff (LStageZF_isTransitive b) (p 0) _ _ _ hb, hp1, hp2]
  exact (R_iff_truth_agree hηa hab).symm

theorem diagonal_comparison_iff_R {k K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b)
    (hkK : k < K) (hθb : θ ≤ b)
    (p : Fin 4 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = LStageZF a)
    (hp1 : (p 1).val = sigmaNodes (k := k) (ordinalIndexCode (η := η)) (LStageZF a))
    (hp2 : (p 2).val = truth (LStageZF a) (k, ⟨η, hηa⟩))
    (hp3 : (p 3).val = η.toZFSet) :
    realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (comparison (diagonalQuery ⟨k, hkK⟩)) Empty.elim p ↔ R k η a b := by
  haveI : Nonempty (ZFCarrier (LStageZF a)) :=
    ⟨⟨∅, empty_mem_LStageZF_of_isSuccLimit ha⟩⟩
  have hd (e x : ZFCarrier (LStageZF b)) :
      (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)).diagonal ⟨k, hkK⟩ (p 3) e x ↔
        ZFSet.pair e.val x.val ∈ truth (LStageZF b) (k, ⟨η, hηa.trans hab.le⟩) := by
    change (∃ ξ : {ξ : Ordinal.{u} // ξ < b}, (p 3).val = ξ.val.toZFSet ∧ _) ↔ _
    rw [hp3]
    constructor
    · rintro ⟨ξ, hξ, hh⟩
      have he : η = ξ.val := Ordinal.toZFSet_injective hξ
      subst he
      exact hh
    · intro hh
      exact ⟨⟨η, hηa.trans_lt hab⟩, rfl, hh⟩
  rw [realize_diagonal_comparison (LStageZF_isTransitive b) _ rfl]
  simp only [hd]
  have hb : NodesBounded ((p 1).val) ((p 0).val) := by
    rw [hp0, hp1]
    exact canonical_nodesBounded ha hηa
  rw [bounded_pair_agree_iff (LStageZF_isTransitive b) (p 0) _ _ _ hb, hp1, hp2]
  exact (R_iff_truth_agree hηa hab).symm

end OneYTruth.EndpointComparison

#print axioms OneYTruth.EndpointComparison.named_comparison_iff_R
#print axioms OneYTruth.EndpointComparison.diagonal_comparison_iff_R
