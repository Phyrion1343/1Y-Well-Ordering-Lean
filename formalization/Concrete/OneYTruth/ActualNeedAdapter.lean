import OneYTruth.ActualEndpointRelation
import OneYTruth.FiniteQuerySemantics

/-! Guarded semantics for actual top-demand queries. A lower block may
move its root; a same-block demand uses its admissible fixed-prefix root.
The ambient endpoint remains external to the parameter tuple. -/

namespace OneYTruth.ActualNeedAdapter

open Constructible OneY.RootIndexed RootSemantics ExternalTower FiniteLabelAssembly
open FirstOrder FirstOrder.Language Constructible.FiniteSequenceZF

universe u

def rootIndex {n : Nat} (d : TopAtom) (hd : d.Valid n) : Fin n :=
  ⟨d.root,hd.1.trans_lt hd.2⟩

def parentIndex {n : Nat} (d : TopAtom) (hd : d.Valid n) : Fin n := ⟨d.parent,hd.2⟩

def slots {n scope : Nat} (label : Fin n → Fin scope) (omega zero : Fin scope)
    (natSlot : Nat → Fin scope) (d : TopAtom) (hd : d.Valid n) : Fin 5 → Fin scope :=
  ![label (parentIndex d hd),omega,zero,natSlot d.layer,label (rootIndex d hd)]

noncomputable def formula {n scope : Nat} (label : Fin n → Fin scope) (omega zero : Fin scope)
    (natSlot : Nat → Fin scope) (K cut : Nat) (θ : Ordinal.{u}) (f : Nat → Ordinal.{u})
    (d : TopAtom) (hd : d.Valid n) (ha : Admissible (· < ·) K cut θ f d) :
    (language K {ξ : Ordinal.{u} // ξ < θ}).BoundedFormula Empty scope :=
  if hLow : d.layer < K then
    renameScope (slots label omega zero natSlot d hd)
      (ActualEndpointQuery.diagonalComparison.{u} ⟨d.layer,hLow⟩)
  else
    renameScope (slots label omega zero natSlot d hd)
      (ActualEndpointQuery.namedComparison.{u} ⟨f d.root,(ha.resolve_left hLow).2.2⟩)

theorem formula_isSigmaOne {n scope : Nat} (label : Fin n → Fin scope) (omega zero : Fin scope)
    (natSlot : Nat → Fin scope) (K cut : Nat) (θ : Ordinal.{u}) (f : Nat → Ordinal.{u})
    (d : TopAtom) (hd : d.Valid n) (ha : Admissible (· < ·) K cut θ f d) :
    IsSigmaOne (formula label omega zero natSlot K cut θ f d hd ha) := by
  unfold formula
  split
  · exact (ActualEndpointQuery.diagonalComparison_isSigmaOne _).renameScope _
  · exact (ActualEndpointQuery.namedComparison_isSigmaOne _).renameScope _

theorem fixed_root {n scope cut : Nat} (label : Fin n → Fin scope)
    (f : Nat → Ordinal.{u}) {top : Ordinal.{u}} (p : Fin scope → ZFCarrier (LStageZF top))
    (v : Fin n → Ordinal.{u}) (hc : ∀ i, (v i).toZFSet = (p (label i)).val)
    (hfix : ∀ i : Fin n, i.val < cut → (p (label i)).val = (f i.val).toZFSet)
    (d : TopAtom) (hd : d.Valid n) (hr : d.root < cut) :
    v (rootIndex d hd) = f d.root :=
  Ordinal.toZFSet_injective ((hc (rootIndex d hd)).trans (hfix (rootIndex d hd) hr))

theorem formula_sound {n scope K cut : Nat} {θ top : Ordinal.{u}}
    (label : Fin n → Fin scope) (omega zero : Fin scope) (natSlot : Nat → Fin scope)
    (f : Nat → Ordinal.{u}) (d : TopAtom) (hd : d.Valid n)
    (ha : Admissible (· < ·) K cut θ f d) (hθtop : θ ≤ top)
    (p : Fin scope → ZFCarrier (LStageZF top)) (v : Fin n → Ordinal.{u})
    (hc : ∀ i, (v i).toZFSet = (p (label i)).val) (hm : StrictMono v)
    (hD : ∀ i, Adequate (v i)) (hb : ∀ i, v i < top)
    (hfix : ∀ i : Fin n, i.val < cut → (p (label i)).val = (f i.val).toZFSet)
    (hOmega : (p omega).val = Ordinal.omega0.toZFSet) (hZero : (p zero).val = ∅)
    (hNat : (p (natSlot d.layer)).val = natCode d.layer)
    (h : realize (interpretation (LStageZF top) (K,⟨θ,hθtop⟩))
      (formula label omega zero natSlot K cut θ f d hd ha) Empty.elim p) :
    NeedFinHolds R v top d hd := by
  let q := p ∘ slots label omega zero natSlot d hd
  have h0 : (q 0).val = (v (parentIndex d hd)).toZFSet := (hc _).symm
  have h4 : (q 4).val = (v (rootIndex d hd)).toZFSet := (hc _).symm
  have hle : v (rootIndex d hd) ≤ v (parentIndex d hd) := hm.monotone hd.1
  have hp := (hD (parentIndex d hd)).2.1
  change R d.layer (v (rootIndex d hd)) (v (parentIndex d hd)) top
  by_cases hLow : d.layer < K
  · rw [formula,dif_pos hLow,realize_renameScope] at h
    exact ActualEndpointQuery.diagonalComparison_sound_R hp hle (hb _) hLow hθtop
      q h0 hOmega hZero hNat h4 h
  · have hs := ha.resolve_left hLow
    have hr := fixed_root label f p v hc hfix d hd hs.2.1
    have hIndex : f d.root ≤ v (parentIndex d hd) := hr ▸ hle
    have hN : (q 3).val = natCode K := hNat.trans (congrArg natCode hs.1)
    have hη : (q 4).val = (f d.root).toZFSet := h4.trans (congrArg Ordinal.toZFSet hr)
    rw [formula,dif_neg hLow,realize_renameScope] at h
    have hh := ActualEndpointQuery.namedComparison_sound_R hp hIndex (hb _) hs.2.2 hθtop
      q h0 hOmega hZero hN hη h
    simpa only [hs.1,hr] using hh

theorem formula_complete {n scope K cut : Nat} {θ top : Ordinal.{u}}
    (label : Fin n → Fin scope) (omega zero : Fin scope) (natSlot : Nat → Fin scope)
    (f : Nat → Ordinal.{u}) (d : TopAtom) (hd : d.Valid n)
    (ha : Admissible (· < ·) K cut θ f d) (hθtop : θ ≤ top) (hTop : Adequate top)
    (p : Fin scope → ZFCarrier (LStageZF top)) (v : Fin n → Ordinal.{u})
    (hc : ∀ i, (v i).toZFSet = (p (label i)).val) (hm : StrictMono v)
    (hD : ∀ i, Adequate (v i)) (hb : ∀ i, v i < top)
    (hfix : ∀ i : Fin n, i.val < cut → (p (label i)).val = (f i.val).toZFSet)
    (hOmega : (p omega).val = Ordinal.omega0.toZFSet) (hZero : (p zero).val = ∅)
    (hNat : (p (natSlot d.layer)).val = natCode d.layer)
    (h : NeedFinHolds R v top d hd) :
    realize (interpretation (LStageZF top) (K,⟨θ,hθtop⟩))
      (formula label omega zero natSlot K cut θ f d hd ha) Empty.elim p := by
  let q := p ∘ slots label omega zero natSlot d hd
  have h0 : (q 0).val = (v (parentIndex d hd)).toZFSet := (hc _).symm
  have h4 : (q 4).val = (v (rootIndex d hd)).toZFSet := (hc _).symm
  have hle : v (rootIndex d hd) ≤ v (parentIndex d hd) := hm.monotone hd.1
  have hp := (hD (parentIndex d hd)).2.1
  change R d.layer (v (rootIndex d hd)) (v (parentIndex d hd)) top at h
  by_cases hLow : d.layer < K
  · rw [formula,dif_pos hLow,realize_renameScope]
    exact (ActualEndpointQuery.diagonalComparison_iff_R hp hTop hle (hb _) hLow hθtop
      q h0 hOmega hZero hNat h4).mpr h
  · have hs := ha.resolve_left hLow
    have hr := fixed_root label f p v hc hfix d hd hs.2.1
    have hIndex : f d.root ≤ v (parentIndex d hd) := hr ▸ hle
    have hN : (q 3).val = natCode K := hNat.trans (congrArg natCode hs.1)
    have hη : (q 4).val = (f d.root).toZFSet := h4.trans (congrArg Ordinal.toZFSet hr)
    rw [formula,dif_neg hLow,realize_renameScope]
    apply (ActualEndpointQuery.namedComparison_iff_R hp hTop hIndex (hb _) hs.2.2 hθtop
      q h0 hOmega hZero hN hη).mpr
    simpa only [hs.1,hr] using h

end OneYTruth.ActualNeedAdapter

#print axioms OneYTruth.ActualNeedAdapter.formula_isSigmaOne
#print axioms OneYTruth.ActualNeedAdapter.formula_sound
#print axioms OneYTruth.ActualNeedAdapter.formula_complete
