import OneYTruth.SourceEndpointRelation
import OneYTruth.RootComparison

/-! Comparison for two internal endpoints. The complete Sigma-node source
is existentially normalized; the actual two truth parameters remain explicit
until the tower certificate is attached. -/

namespace OneYTruth.SourcePairComparison

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open FirstOrder FirstOrder.Language InternalClosure SigmaComparison
open SourceEndpointComparison RootSemantics ExternalTower FormulaCode

universe u v

/-- Alphabet, small domain, omega, zero, k, small Sat, large Sat; nodes. -/
noncomputable def nodesAt (K : Nat) (J : Type v) :=
  renameScope ![0,1,2,3,4,(7 : Fin 8)] (SigmaNodeSourceCertificate.query.{u,v} K J)
def comparisonAt (K : Nat) (J : Type v) :=
  renameScope ![7,5,(6 : Fin 8)] (mixedComparisonFormula K J)

theorem nodesAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (nodesAt.{u,v} K J) :=
  (SigmaNodeSourceCertificate.query_isSigmaOne K J).renameScope _
theorem comparisonAt_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (comparisonAt K J) :=
  .deltaZero ((mixedComparisonFormula_isDeltaZero K J).renameScope _)

noncomputable def query (K : Nat) (J : Type v) : (language K J).BoundedFormula Empty 7 :=
  (sigmaConjFormula.{v,u} (nodesAt.{u,v} K J) (comparisonAt K J)
    (nodesAt_isSigmaOne K J) (comparisonAt_isSigmaOne K J)).ex

theorem query_isSigmaOne (K : Nat) (J : Type v) : IsSigmaOne (query.{u,v} K J) :=
  .ex (sigmaConjFormula_isSigmaOne _ _ _ _)

theorem realize_query {K : Nat} {J : Type v} {A : Type u}
    (N : Interpretation K J A) (p : Fin 7 → A) :
    realize N (query.{u,v} K J) Empty.elim p ↔ ∃ nodes : A,
      realize N (SigmaNodeSourceCertificate.query.{u,v} K J) Empty.elim
        ![p 0,p 1,p 2,p 3,p 4,nodes] ∧
      realize N (mixedComparisonFormula K J) Empty.elim ![nodes,p 5,p 6] := by
  rw [query,realize_scoped_ex]
  apply exists_congr
  intro nodes
  rw [realize_sigmaConjFormula,nodesAt,comparisonAt,realize_renameScope,realize_renameScope]
  have hn : Fin.snoc p nodes ∘ ![0,1,2,3,4,(7 : Fin 8)] = ![p 0,p 1,p 2,p 3,p 4,nodes] := by
    funext i; fin_cases i <;> rfl
  have hc : Fin.snoc p nodes ∘ ![7,5,(6 : Fin 8)] = ![nodes,p 5,p 6] := by
    funext i; fin_cases i <;> rfl
  rw [hn,hc]

theorem sound_R {k K : Nat} {J : Type v} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (p : Fin 7 → ZFCarrier V)
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅)
    (hp4 : (p 4).val = natCode k)
    (hSmall : (p 5).val = truth (LStageZF a) (k,⟨η,hηa⟩))
    (hLarge : (p 6).val = truth (LStageZF b) (k,⟨η,hηa.trans hab.le⟩))
    (h : realize N (query.{u+1,v} K J) Empty.elim p) : R k η a b := by
  obtain ⟨nodes,hn,hc⟩ := (realize_query N p).mp h
  have hnodes := SigmaNodeSourceCertificate.query_sound hV N hmem
    (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η)
    ![p 0,p 1,p 2,p 3,p 4,nodes] hp0 hp1 hp2 hp3 hp4 hn
  apply (realize_comparison_iff_R hηa hab hV N hmem ![nodes,p 5,p 6] ?_).mp hc
  intro i
  fin_cases i <;> first | exact hnodes | exact hSmall | exact hLarge

theorem realize_iff_R {k K : Nat} {J : Type v} {η a b : Ordinal.{u}}
    [Nonempty (ZFCarrier (LStageZF a))] (hηa : η ≤ a) (hab : a < b)
    {V : ZFSet.{u}} (hV : V.IsTransitive) (N : Interpretation K J (ZFCarrier V))
    (hmem : N.mem = zfCarrierMem V) (hCol : HasCollection N) (hSep : HasSeparation N)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, ZFSet.pair x y ∈ V)
    (hUnion : ∀ x ∈ V, ZFSet.sUnion x ∈ V) (hempty : (∅ : ZFSet.{u}) ∈ V)
    (p : Fin 7 → ZFCarrier V)
    (hp0 : (p 0).val = η.toZFSet) (hp1 : (p 1).val = LStageZF a)
    (hp2 : (p 2).val = Ordinal.omega0.toZFSet) (hp3 : (p 3).val = ∅)
    (hp4 : (p 4).val = natCode k)
    (hSmall : (p 5).val = truth (LStageZF a) (k,⟨η,hηa⟩))
    (hLarge : (p 6).val = truth (LStageZF b) (k,⟨η,hηa.trans hab.le⟩)) :
    realize N (query.{u+1,v} K J) Empty.elim p ↔ R k η a b := by
  constructor
  · exact sound_R hηa hab hV N hmem p hp0 hp1 hp2 hp3 hp4 hSmall hLarge
  · intro hR
    have hn := ordinalNodes_mem (k := k) hV N hmem hCol hSep hpair hUnion hempty
      η a (hp0 ▸ (p 0).property) (hp1 ▸ (p 1).property) (hp2 ▸ (p 2).property)
    let nodes : ZFCarrier V := ⟨_,hn⟩
    apply (realize_query N p).mpr
    refine ⟨nodes,?_,?_⟩
    · exact (SigmaNodeSourceCertificate.realize_query_iff hV N hmem hCol hSep hpair hUnion hempty
        (ordinalAlphabet η) (stageDomain a) (ordinalAlphabet_eq_range η)
        ![p 0,p 1,p 2,p 3,p 4,nodes] hp0 hp1 hp2 hp3 hp4).mpr rfl
    · apply (realize_comparison_iff_R hηa hab hV N hmem ![nodes,p 5,p 6] ?_).mpr hR
      intro i
      fin_cases i <;> first | exact hSmall | exact hLarge | rfl

end OneYTruth.SourcePairComparison

#print axioms OneYTruth.SourcePairComparison.query_isSigmaOne
#print axioms OneYTruth.SourcePairComparison.realize_iff_R
