import OneYTruth.FiniteLabelAssembly

/-! # Complete recovery of finite-reflection output from an internal tuple

Ordinal bounds come from the actual smaller carrier. Domain and relation
facts are supplied as decoded code predicates, ready for the independently
constructed genuine Sigma-one queries.
-/

namespace OneYTruth.FiniteLabelAssembly

open Constructible OneY.RootIndexed

universe u v

def CodeAtomHolds (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (q : Fin n → ZFSet.{u}) (e : Atom) (he : e.Valid n) : Prop :=
  CodeRelation R e.layer (q ⟨e.root,by rcases he with ⟨_,_,_⟩; omega⟩)
    (q ⟨e.parent,by rcases he with ⟨_,_,_⟩; omega⟩) (q ⟨e.child,he.2.2⟩)

def CodeNeedHolds (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (q : Fin n → ZFSet.{u}) (top : Ordinal.{u})
    (d : TopAtom) (hd : d.Valid n) : Prop :=
  CodeTopRelation R top d.layer (q ⟨d.root,by rcases hd with ⟨_,_⟩; omega⟩)
    (q ⟨d.parent,hd.2⟩)

theorem atom_from_codes (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (v : Fin n → Ordinal.{u}) (q : Fin n → ZFSet.{u})
    (hc : ∀ i, (v i).toZFSet = q i) (e : Atom) (he : e.Valid n)
    (h : CodeAtomHolds R q e he) : AtomFinHolds R v e he := by
  unfold CodeAtomHolds at h
  rw [← hc _,← hc _,← hc _] at h
  exact (codeRelation_codes R _ _ _ _).mp h

theorem need_from_codes (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    {n : Nat} (v : Fin n → Ordinal.{u}) (q : Fin n → ZFSet.{u})
    (hc : ∀ i, (v i).toZFSet = q i) (top : Ordinal.{u})
    (d : TopAtom) (hd : d.Valid n) (h : CodeNeedHolds R q top d hd) :
    NeedFinHolds R v top d hd := by
  unfold CodeNeedHolds at h
  rw [← hc _,← hc _] at h
  exact (codeTopRelation_codes R _ _ _ _).mp h

/-- This supplies every component of the finite-reflection conclusion,
once one internal reflected tuple satisfies the literal finite code facts.
No semantic reflection principle is assumed in this decoding theorem. -/
theorem assemble_from_carrier_tuple {K : Nat} {J : Type v} {α : Ordinal.{u}}
    (N : Interpretation K J (ZFCarrier (LStageZF α))) (hmem : N.mem = zfCarrierMem (LStageZF α))
    (D : Ordinal.{u} → Prop) (R : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop)
    (G : Diagram) (cut : Nat) (hcut : cut ≤ G.size) (f : Nat → Ordinal.{u})
    (needs : List TopAtom) (hnv : ∀ d ∈ needs, d.Valid G.size)
    (p : Fin (G.size+1) → ZFCarrier (LStageZF α))
    (hord : realize N (OrdinalTupleCertificate.mixedFormula K J G.size) Empty.elim p)
    (hD : ∀ i : Fin G.size, CodeDomain D (p i.castSucc).val)
    (hR : ∀ e, ∀ he : e ∈ G.atoms,
      CodeAtomHolds R (fun i : Fin G.size => (p i.castSucc).val) e (G.valid e he))
    (hfixed : ∀ i : Fin G.size, i.val < cut → (p i.castSucc).val = (f i.val).toZFSet)
    (hneeds : ∀ d, ∀ hd : d ∈ needs,
      CodeNeedHolds R (fun i : Fin G.size => (p i.castSucc).val) α d (hnv d hd)) :
    ∃ g : Nat → Ordinal.{u}, Representation (· < ·) D R G g ∧
      (∀ i, i < cut → g i = f i) ∧ Bounded (· < ·) G.size g α ∧
      (∀ d ∈ needs, d.Holds R g α) := by
  obtain ⟨v,hv,hm,hb⟩ := (OrdinalTupleCertificate.realize_in_stage N hmem p).mp hord
  refine ⟨extend v,?_,?_,bounded_of_finite v α hb,?_⟩
  · refine representation_of_finite D R G v ?_ hm ?_
    · intro i
      exact (codeDomain_codes D (v i)).mp ((hv i).symm ▸ hD i)
    · intro e he
      exact atom_from_codes R v _ hv e (G.valid e he) (hR e he)
  · exact fixed_of_finite hcut v f (fun i hi => (hv i).trans (hfixed i hi))
  · apply needs_of_finite R v α needs hnv
    intro d hd
    exact need_from_codes R v _ hv α d (hnv d hd) (hneeds d hd)

end OneYTruth.FiniteLabelAssembly

#print axioms OneYTruth.FiniteLabelAssembly.assemble_from_carrier_tuple

