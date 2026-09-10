import OneYTruth.SourceEndpointComparison

/-! Actual R semantics of the node-source-certified endpoint queries.

The only remaining derived satisfaction input is explicitly identified with
the actual smaller truth set. The complete Sigma-node source is no longer an
input or a correctness hypothesis. No arbitrary candidate Sat is accepted.
-/

namespace OneYTruth.SourceEndpointComparison

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open ExternalTower RootSemantics SigmaComparison EndpointComparison InternalClosure FormulaCode

universe u v

noncomputable def ordinalAlphabet (η : Ordinal.{u}) : LCarrier.{u} := ⟨η.toZFSet, ordinal_toZFSet_mem_L η⟩
noncomputable def stageDomain (a : Ordinal.{u}) : LCarrier.{u} := ⟨LStageZF a, LStageZF_mem_L a⟩

theorem ordinalAlphabet_eq_range (η : Ordinal.{u}) :
    (ordinalAlphabet η).val = ZFSet.range (ordinalIndexCode (η := η)) :=
  (ordinalIndexCode_range η).symm

theorem ordinalNodes_mem {k K : Nat} {J : Type v} {V : ZFSet.{u}}
    (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V)
    (hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (η a : Ordinal.{u}) (hA : η.toZFSet ∈ V) (hU : LStageZF a ∈ V)
    (hW : Ordinal.omega0.toZFSet ∈ V) :
    sigmaNodes (k := k) (ordinalIndexCode (η := η)) (LStageZF a) ∈ V :=
  (InternalSourceSets.sourceSets_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty hW
    (ordinalIndexCode (η := η)) (ordinalAlphabet η) (stageDomain a)
    (ordinalAlphabet_eq_range η) hA hU).2.2.2

theorem namedComparison_sound_R {K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b)
    (hηθ : η < θ) (hθb : θ ≤ b) (p : Fin 6 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅)
    (hp4 : (p 4).val = natCode K)
    (hSmallSat : (p 5).val = truth (LStageZF a) (K, ⟨η, hηa⟩))
    (h : realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (namedComparison.{u+1} (K := K) ⟨η, hηθ⟩) Empty.elim p) : R K η a b := by
  obtain ⟨nodes, hn, hc⟩ := query_sound (LStageZF_isTransitive b)
    (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)) rfl (namedQuery ⟨η, hηθ⟩) (.rel _ _)
    (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η) p hp0 hp1 hp2 hp3 hp4 h
  exact (named_comparison_iff_R ha hηa hab hηθ hθb ![p 1, nodes, p 5, p 0]
    hp1 hn hSmallSat).mp hc

theorem namedComparison_iff_R {K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hb : Order.IsSuccLimit b) (hηa : η ≤ a) (hab : a < b)
    (hηθ : η < θ) (hθb : θ ≤ b)
    (hCol : HasCollection (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)))
    (hSep : HasSeparation (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)))
    (p : Fin 6 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅)
    (hp4 : (p 4).val = natCode K)
    (hSmallSat : (p 5).val = truth (LStageZF a) (K, ⟨η, hηa⟩)) :
    realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (namedComparison.{u+1} (K := K) ⟨η, hηθ⟩) Empty.elim p ↔ R K η a b := by
  constructor
  · exact namedComparison_sound_R ha hηa hab hηθ hθb p hp0 hp1 hp2 hp3 hp4 hSmallSat
  · intro hR
    have hpair : ∀ x ∈ LStageZF b, ∀ y ∈ LStageZF b, ZFSet.pair x y ∈ LStageZF b :=
      fun x hx y hy => orderedPair_mem_LStageZF_of_isSuccLimit hb hx hy
    have hUnion : ∀ x ∈ LStageZF b, ZFSet.sUnion x ∈ LStageZF b :=
      fun x hx => sUnion_mem_LStageZF_of_isSuccLimit hb hx
    have hZero := empty_mem_LStageZF_of_isSuccLimit hb
    have hn := ordinalNodes_mem (k := K) (LStageZF_isTransitive b)
      (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)) rfl hCol hSep hpair hUnion hZero η a
      (hp0 ▸ (p 0).property) (hp1 ▸ (p 1).property) (hp2 ▸ (p 2).property)
    let nodes : ZFCarrier (LStageZF b) := ⟨_, hn⟩
    apply query_complete (LStageZF_isTransitive b) (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      rfl hCol hSep hpair hUnion hZero (namedQuery ⟨η, hηθ⟩) (.rel _ _)
      (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η) p hp0 hp1 hp2 hp3 hp4 nodes rfl
    exact (named_comparison_iff_R ha hηa hab hηθ hθb ![p 1, nodes, p 5, p 0] hp1 rfl hSmallSat).mpr hR

theorem diagonalComparison_sound_R {k K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hηa : η ≤ a) (hab : a < b) (hkK : k < K) (hθb : θ ≤ b)
    (p : Fin 6 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅) (hp4 : (p 4).val = natCode k)
    (hSmallSat : (p 5).val = truth (LStageZF a) (k, ⟨η, hηa⟩))
    (h : realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (diagonalComparison.{u+1} ⟨k, hkK⟩) Empty.elim p) : R k η a b := by
  obtain ⟨nodes, hn, hc⟩ := query_sound (LStageZF_isTransitive b)
    (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)) rfl (diagonalQuery ⟨k, hkK⟩) (.rel _ _)
    (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η) p hp0 hp1 hp2 hp3 hp4 h
  exact (diagonal_comparison_iff_R ha hηa hab hkK hθb ![p 1, nodes, p 5, p 0]
    hp1 hn hSmallSat hp0).mp hc

theorem diagonalComparison_iff_R {k K : Nat} {η θ a b : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) (hb : Order.IsSuccLimit b) (hηa : η ≤ a) (hab : a < b)
    (hkK : k < K) (hθb : θ ≤ b)
    (hCol : HasCollection (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)))
    (hSep : HasSeparation (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)))
    (p : Fin 6 → ZFCarrier (LStageZF b))
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅) (hp4 : (p 4).val = natCode k)
    (hSmallSat : (p 5).val = truth (LStageZF a) (k, ⟨η, hηa⟩)) :
    realize (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      (diagonalComparison.{u+1} ⟨k, hkK⟩) Empty.elim p ↔ R k η a b := by
  constructor
  · exact diagonalComparison_sound_R ha hηa hab hkK hθb p hp0 hp1 hp2 hp3 hp4 hSmallSat
  · intro hR
    have hpair : ∀ x ∈ LStageZF b, ∀ y ∈ LStageZF b, ZFSet.pair x y ∈ LStageZF b :=
      fun x hx y hy => orderedPair_mem_LStageZF_of_isSuccLimit hb hx hy
    have hUnion : ∀ x ∈ LStageZF b, ZFSet.sUnion x ∈ LStageZF b :=
      fun x hx => sUnion_mem_LStageZF_of_isSuccLimit hb hx
    have hZero := empty_mem_LStageZF_of_isSuccLimit hb
    have hn := ordinalNodes_mem (k := k) (LStageZF_isTransitive b)
      (interpretation (LStageZF b) (K, ⟨θ, hθb⟩)) rfl hCol hSep hpair hUnion hZero η a
      (hp0 ▸ (p 0).property) (hp1 ▸ (p 1).property) (hp2 ▸ (p 2).property)
    let nodes : ZFCarrier (LStageZF b) := ⟨_, hn⟩
    apply query_complete (LStageZF_isTransitive b) (interpretation (LStageZF b) (K, ⟨θ, hθb⟩))
      rfl hCol hSep hpair hUnion hZero (diagonalQuery ⟨k, hkK⟩) (.rel _ _)
      (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η) p hp0 hp1 hp2 hp3 hp4 nodes rfl
    exact (diagonal_comparison_iff_R ha hηa hab hkK hθb ![p 1, nodes, p 5, p 0]
      hp1 rfl hSmallSat hp0).mpr hR

end OneYTruth.SourceEndpointComparison

#print axioms OneYTruth.SourceEndpointComparison.namedComparison_sound_R
#print axioms OneYTruth.SourceEndpointComparison.namedComparison_iff_R
#print axioms OneYTruth.SourceEndpointComparison.diagonalComparison_iff_R
