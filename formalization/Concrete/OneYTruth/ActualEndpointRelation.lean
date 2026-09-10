import OneYTruth.ActualEndpointQuery

/-! Exact R semantics of the completely normalized current-endpoint queries.
Named queries use one fixed lower symbol eta<theta. Diagonal queries permit
a variable smaller ordinal index and a fixed lower block k<K. -/

namespace OneYTruth.ActualEndpointQuery

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open ExternalTower RootSemantics EndpointComparison

universe u

theorem namedComparison_sound_R {K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b)
    (hηθ : η < θ) (hθb : θ ≤ b) (p : Fin 5 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = a.toZFSet) (hp1 : (p 1).val = Ordinal.omega0.toZFSet)
    (hp2 : (p 2).val = ∅) (hp3 : (p 3).val = natCode K) (hp4 : (p 4).val = η.toZFSet)
    (h : realize (interpretation (LStageZF b) (K, ⟨θ,hθb⟩))
      (namedComparison.{u} (K := K) ⟨η,hηθ⟩) Empty.elim p) : R K η a b := by
  obtain ⟨U,S,hU,hS,hc⟩ := sound_values (LStageZF_isTransitive b)
    (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L b))
    (interpretation (LStageZF b) (K, ⟨θ,hθb⟩)) rfl
    (namedQuery ⟨η,hηθ⟩) (.rel _ _) a (K,⟨η,hηa⟩) p hp0 hp1 hp2 hp3 hp4 h
  exact SourceEndpointComparison.namedComparison_sound_R ha hηa hab hηθ hθb
    ![p 4,U,p 1,p 2,p 3,S] hp4 hU hp1 hp2 hp3 hS hc

theorem namedComparison_iff_R {K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hb : Adequate b) (hηa : η ≤ a) (hab : a < b)
    (hηθ : η < θ) (hθb : θ ≤ b) (p : Fin 5 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = a.toZFSet) (hp1 : (p 1).val = Ordinal.omega0.toZFSet)
    (hp2 : (p 2).val = ∅) (hp3 : (p 3).val = natCode K) (hp4 : (p 4).val = η.toZFSet) :
    realize (interpretation (LStageZF b) (K, ⟨θ,hθb⟩))
      (namedComparison.{u} (K := K) ⟨η,hηθ⟩) Empty.elim p ↔ R K η a b := by
  constructor
  · exact namedComparison_sound_R ha hηa hab hηθ hθb p hp0 hp1 hp2 hp3 hp4
  · intro hR
    have hs := hb.2.2 K θ hθb
    apply complete_of_comparison hb (interpretation (LStageZF b) (K,⟨θ,hθb⟩)) rfl hs.2 hs.1
      (namedQuery ⟨η,hηθ⟩) (.rel _ _) (K,⟨η,hηa⟩) p hp0 hp1 hp2 hp3 hp4
    intro U S hU hS
    exact (SourceEndpointComparison.namedComparison_iff_R ha hb.2.1 hηa hab hηθ hθb hs.2 hs.1
      ![p 4,U,p 1,p 2,p 3,S] hp4 hU hp1 hp2 hp3 hS).mpr hR

theorem diagonalComparison_sound_R {k K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b)
    (hkK : k < K) (hθb : θ ≤ b) (p : Fin 5 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = a.toZFSet) (hp1 : (p 1).val = Ordinal.omega0.toZFSet)
    (hp2 : (p 2).val = ∅) (hp3 : (p 3).val = natCode k) (hp4 : (p 4).val = η.toZFSet)
    (h : realize (interpretation (LStageZF b) (K, ⟨θ,hθb⟩))
      (diagonalComparison.{u} ⟨k,hkK⟩) Empty.elim p) : R k η a b := by
  obtain ⟨U,S,hU,hS,hc⟩ := sound_values (LStageZF_isTransitive b)
    (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L b))
    (interpretation (LStageZF b) (K, ⟨θ,hθb⟩)) rfl
    (diagonalQuery ⟨k,hkK⟩) (.rel _ _) a (k,⟨η,hηa⟩) p hp0 hp1 hp2 hp3 hp4 h
  exact SourceEndpointComparison.diagonalComparison_sound_R ha hηa hab hkK hθb
    ![p 4,U,p 1,p 2,p 3,S] hp4 hU hp1 hp2 hp3 hS hc

theorem diagonalComparison_iff_R {k K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hb : Adequate b) (hηa : η ≤ a) (hab : a < b)
    (hkK : k < K) (hθb : θ ≤ b) (p : Fin 5 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = a.toZFSet) (hp1 : (p 1).val = Ordinal.omega0.toZFSet)
    (hp2 : (p 2).val = ∅) (hp3 : (p 3).val = natCode k) (hp4 : (p 4).val = η.toZFSet) :
    realize (interpretation (LStageZF b) (K, ⟨θ,hθb⟩))
      (diagonalComparison.{u} ⟨k,hkK⟩) Empty.elim p ↔ R k η a b := by
  constructor
  · exact diagonalComparison_sound_R ha hηa hab hkK hθb p hp0 hp1 hp2 hp3 hp4
  · intro hR
    have hs := hb.2.2 K θ hθb
    apply complete_of_comparison hb (interpretation (LStageZF b) (K,⟨θ,hθb⟩)) rfl hs.2 hs.1
      (diagonalQuery ⟨k,hkK⟩) (.rel _ _) (k,⟨η,hηa⟩) p hp0 hp1 hp2 hp3 hp4
    intro U S hU hS
    exact (SourceEndpointComparison.diagonalComparison_iff_R ha hb.2.1 hηa hab hkK hθb hs.2 hs.1
      ![p 4,U,p 1,p 2,p 3,S] hp4 hU hp1 hp2 hp3 hS).mpr hR

end OneYTruth.ActualEndpointQuery

#print axioms OneYTruth.ActualEndpointQuery.namedComparison_isSigmaOne
#print axioms OneYTruth.ActualEndpointQuery.diagonalComparison_isSigmaOne
#print axioms OneYTruth.ActualEndpointQuery.namedComparison_sound_R
#print axioms OneYTruth.ActualEndpointQuery.namedComparison_iff_R
#print axioms OneYTruth.ActualEndpointQuery.diagonalComparison_iff_R
