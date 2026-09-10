import OneYTruth.ActualQueryMetadata
import OneYTruth.ActualDomainAtomAdapter
import OneYTruth.ActualNeedAdapter

/-! The actual finite family of Adequate, internal R, and endpoint R queries.
Their semantics are proved from decoded ordinal and domain guards. No
formula, truth set, or local relation correctness remains as an assumption. -/

namespace OneYTruth.ActualDiagramQueries

open Constructible Constructible.FiniteSequenceZF OneY.RootIndexed
open RootSemantics FiniteLabelAssembly ExternalTower

universe u

def omegaSlot (G : Diagram) (needs : List TopAtom) :=
  Fin.castAdd G.size (omegaIndex (tags G needs))

def zeroSlot (G : Diagram) (needs : List TopAtom) :=
  Fin.castAdd G.size (zeroIndex (tags G needs))

def labelSlot (G : Diagram) (needs : List TopAtom) :
    Fin G.size → Fin (arity (tags G needs)+G.size) := Fin.natAdd (arity (tags G needs))

def natSlot (G : Diagram) (needs : List TopAtom) (k : Nat) :=
  Fin.castAdd G.size (natIndex (tags G needs) k)

noncomputable def family (G : Diagram) (needs : List TopAtom)
    (hnv : ∀ d ∈ needs, d.Valid G.size) (K cut : Nat) (θ : Ordinal.{u})
    (f : Nat → Ordinal.{u}) (hAdm : ∀ d ∈ needs, Admissible (· < ·) K cut θ f d) :
    QueryFamily K {ξ : Ordinal.{u} // ξ < θ} G needs (arity (tags G needs)+G.size) := by
  classical
  exact {
    domain := ActualDomainAtomAdapter.domainFormula.{u,u+1} K _
      (omegaSlot G needs) (zeroSlot G needs) (labelSlot G needs)
    atom := fun e => if he : e ∈ G.atoms then
      ActualDomainAtomAdapter.atomFormula.{u,u+1} K _ (omegaSlot G needs)
        (zeroSlot G needs) (labelSlot G needs) (natSlot G needs) e (G.valid e he)
      else .falsum
    need := fun d => if hd : d ∈ needs then
      ActualNeedAdapter.formula (labelSlot G needs) (omegaSlot G needs) (zeroSlot G needs)
        (natSlot G needs) K cut θ f d (hnv d hd) (hAdm d hd)
      else .falsum
    domain_sigma := fun i => ActualDomainAtomAdapter.domainFormula_isSigmaOne K _ _ _ _ i
    atom_sigma := by
      intro e he
      rw [dif_pos he]
      exact ActualDomainAtomAdapter.atomFormula_isSigmaOne K _ _ _ _ _ e _
    need_sigma := by
      intro d hd
      rw [dif_pos hd]
      exact ActualNeedAdapter.formula_isSigmaOne _ _ _ _ K cut θ f d _ _ }

theorem family_sound (G : Diagram) (needs : List TopAtom)
    (hnv : ∀ d ∈ needs, d.Valid G.size) (K cut : Nat) (θ : Ordinal.{u})
    (f : Nat → Ordinal.{u}) (hAdm : ∀ d ∈ needs, Admissible (· < ·) K cut θ f d)
    {top : Ordinal.{u}} (hθtop : θ ≤ top)
    (pars : Fin (arity (tags G needs)) → ZFCarrier (LStageZF top))
    (hMeta : MetadataCorrect (tags G needs) pars) :
    QuerySound Adequate R G needs hnv cut f pars
      (interpretation (LStageZF top) (K,⟨θ,hθtop⟩)) (family G needs hnv K cut θ f hAdm) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro p v hc i h
    exact ActualDomainAtomAdapter.domain_sound _ rfl (omegaSlot G needs) (zeroSlot G needs)
      (labelSlot G needs) p v hc.codes (hMeta.at_omega hc) (hMeta.at_zero hc) i h
  · intro p v hc hD e he h
    simp only [family,dif_pos he] at h
    exact ActualDomainAtomAdapter.atom_sound _ rfl (omegaSlot G needs) (zeroSlot G needs)
      (labelSlot G needs) (natSlot G needs) p v hc.codes hc.ordered hD
      (hMeta.at_omega hc) (hMeta.at_zero hc) e (G.valid e he)
      (hMeta.at_nat hc e.layer (atom_tag he)) h
  · intro p v hc hD d hd h
    simp only [family,dif_pos hd] at h
    exact ActualNeedAdapter.formula_sound (labelSlot G needs) (omegaSlot G needs)
      (zeroSlot G needs) (natSlot G needs) f d (hnv d hd) (hAdm d hd) hθtop
      p v hc.codes hc.ordered hD hc.bounded hc.fixed
      (hMeta.at_omega hc) (hMeta.at_zero hc) (hMeta.at_nat hc d.layer (need_tag hd)) h

theorem family_complete (G : Diagram) (needs : List TopAtom)
    (hnv : ∀ d ∈ needs, d.Valid G.size) (K cut : Nat) (θ : Ordinal.{u})
    (f : Nat → Ordinal.{u}) (hAdm : ∀ d ∈ needs, Admissible (· < ·) K cut θ f d)
    {top : Ordinal.{u}} (hθtop : θ ≤ top) (hTop : Adequate top)
    (pars : Fin (arity (tags G needs)) → ZFCarrier (LStageZF top))
    (hMeta : MetadataCorrect (tags G needs) pars) :
    QueryComplete Adequate R G needs hnv cut f pars
      (interpretation (LStageZF top) (K,⟨θ,hθtop⟩)) (family G needs hnv K cut θ f hAdm) := by
  classical
  have hs := hTop.2.2 K θ hθtop
  refine ⟨?_,?_,?_⟩
  · intro p v hc i hD
    exact ActualDomainAtomAdapter.domain_complete hTop _ rfl hs.2 hs.1
      (omegaSlot G needs) (zeroSlot G needs) (labelSlot G needs) p v hc.codes
      (hMeta.at_omega hc) (hMeta.at_zero hc) i hD
  · intro p v hc hD e he hR
    simp only [family,dif_pos he]
    exact ActualDomainAtomAdapter.atom_complete hTop _ rfl hs.2 hs.1
      (omegaSlot G needs) (zeroSlot G needs) (labelSlot G needs) (natSlot G needs)
      p v hc.codes hc.ordered hD (hMeta.at_omega hc) (hMeta.at_zero hc)
      e (G.valid e he) (hMeta.at_nat hc e.layer (atom_tag he)) hR
  · intro p v hc hD d hd hR
    simp only [family,dif_pos hd]
    exact ActualNeedAdapter.formula_complete (labelSlot G needs) (omegaSlot G needs)
      (zeroSlot G needs) (natSlot G needs) f d (hnv d hd) (hAdm d hd) hθtop hTop
      p v hc.codes hc.ordered hD hc.bounded hc.fixed
      (hMeta.at_omega hc) (hMeta.at_zero hc) (hMeta.at_nat hc d.layer (need_tag hd)) hR

end OneYTruth.ActualDiagramQueries

#print axioms OneYTruth.ActualDiagramQueries.family_sound
#print axioms OneYTruth.ActualDiagramQueries.family_complete
