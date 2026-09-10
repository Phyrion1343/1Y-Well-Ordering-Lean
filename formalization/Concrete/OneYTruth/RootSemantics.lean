import OneYTruth.TowerTrace
import OneYTruth.Weakening
import OneYTruth.InitialStageSchemas
import OneYTruth.InitialTruthStages

/-!
# The concrete ordinal relations used by root-indexed representations

R uses the canonical mixed towers and actual Sigma-one formula preservation.
Adequate records exactly the limit-level closure and expanded schemas used
by the current internal construction. Initial supply remains conditional
on constructibility of the one actual ambient uniform truth set.
-/

namespace OneYTruth.RootSemantics

open Constructible FirstOrder FirstOrder.Language ExternalTower
open scoped Ordinal

universe u

def R (k : Nat) (η a b : Ordinal.{u}) : Prop :=
  ∃ hηa : η ≤ a, ∃ hab : a < b,
    SigmaOneMap (interpretation (LStageZF a) (k, ⟨η, hηa⟩))
      (interpretation (LStageZF b) (k, ⟨η, hηa.trans hab.le⟩))
      (Auxiliary.inclusion (LStageZF_mono hab.le))

def Adequate (a : Ordinal.{u}) : Prop :=
  Ordinal.omega0 < a ∧ Order.IsSuccLimit a ∧
    ∀ (k : Nat) (η : Ordinal.{u}) (hηa : η ≤ a),
      let N := interpretation (LStageZF a) (k, ⟨η, hηa⟩)
      InternalClosure.HasSeparation N ∧ InternalClosure.HasCollection N

theorem R.strict {k : Nat} {η a b : Ordinal.{u}} (h : R k η a b) : a < b := h.choose_spec.choose

theorem R.index_le {k : Nat} {η a b : Ordinal.{u}} (h : R k η a b) : η ≤ a := h.choose

theorem R.trans {k : Nat} {η a b c : Ordinal.{u}}
    (hab : R k η a b) (hbc : R k η b c) : R k η a c := by
  obtain ⟨hηa, hab, hf⟩ := hab
  obtain ⟨hηb, hbc, hg⟩ := hbc
  refine ⟨hηa, hab.trans hbc, ?_⟩
  intro A n φ hφ v xs
  have hh := hg φ hφ (Auxiliary.inclusion (LStageZF_mono hab.le) ∘ v)
    (Auxiliary.inclusion (LStageZF_mono hab.le) ∘ xs)
  exact hh.trans (hf φ hφ v xs)

theorem R.weaken {k : Nat} {η θ a b : Ordinal.{u}} (hηθ : η ≤ θ)
    (h : R k θ a b) : R k η a b := by
  obtain ⟨hθa, hab, hf⟩ := h
  refine ⟨hηθ.trans hθa, hab, ?_⟩
  let g := fun ξ : {ξ : Ordinal.{u} // ξ < η} =>
    (⟨ξ.val, ξ.property.trans_le hηθ⟩ : {ξ : Ordinal.{u} // ξ < θ})
  have hh : SigmaOneMap ((interpretation (LStageZF a) (k, ⟨θ, hθa⟩)).restrictNames g)
      ((interpretation (LStageZF b) (k, ⟨θ, hθa.trans hab.le⟩)).restrictNames g)
      (Auxiliary.inclusion (LStageZF_mono hab.le)) := hf.restrictNames g
  dsimp only [g] at hh
  rw [restrictNames_interpretation (LStageZF a) k hηθ hθa,
    restrictNames_interpretation (LStageZF b) k hηθ (hθa.trans hab.le)] at hh
  exact @hh

theorem R.lower_block {k K : Nat} {η θ a b : Ordinal.{u}}
    (hK : k < K) (hηa : η ≤ a)
    (h : R K θ a b) : R k η a b := by
  obtain ⟨hθa, hab, hf⟩ := h
  let codeA := traceIndex (k, ⟨η, hηa⟩)
  let codeB := fun i => Auxiliary.inclusion (LStageZF_mono hab.le) (codeA i)
  have hh : SigmaOneMap
      (OneYTruth.diagonalReduct hK (interpretation (LStageZF a) (K, ⟨θ, hθa⟩)) codeA)
      (OneYTruth.diagonalReduct hK (interpretation (LStageZF b) (K, ⟨θ, hθa.trans hab.le⟩)) codeB)
      (Auxiliary.inclusion (LStageZF_mono hab.le)) :=
    hf.diagonalReduct hK codeA codeB (fun _ => rfl)
  rw [diagonalReduct_interpretation (LStageZF a) hK hηa hθa codeA (fun _ => rfl),
    diagonalReduct_interpretation (LStageZF b) hK (hηa.trans hab.le)
      (hθa.trans hab.le) codeB (fun _ => rfl)] at hh
  exact ⟨hηa, hab, hh⟩

end OneYTruth.RootSemantics
