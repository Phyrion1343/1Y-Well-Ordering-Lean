import OneYTruth.ActualAdequateQuery
import OneYTruth.ActualRelationQuery
import OneYTruth.FiniteLabelAssembly

/-! Actual domain and internal-atom formulas in an arbitrary finite scope.
The guards are decoded ordinal codes and their order; no canonical source
or satisfaction assumptions are introduced by this adapter. -/

namespace OneYTruth.ActualDomainAtomAdapter

open Constructible Constructible.Model Constructible.FiniteSequenceZF
open OneY.RootIndexed FiniteLabelAssembly RootSemantics InternalClosure

universe u v

def rootIndex {n : Nat} (e : Atom) (he : e.Valid n) : Fin n :=
  ⟨e.root, by rcases he with ⟨_,_,_⟩; omega⟩

def parentIndex {n : Nat} (e : Atom) (he : e.Valid n) : Fin n :=
  ⟨e.parent, he.2.1.trans he.2.2⟩

def childIndex {n : Nat} (e : Atom) (he : e.Valid n) : Fin n := ⟨e.child, he.2.2⟩

noncomputable def domainFormula {n scope : Nat} (K : Nat) (J : Type v)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (i : Fin n) :=
  renameScope ![label i,omega,zero] (ActualAdequateQuery.query.{u,v} K J)

noncomputable def atomFormula {n scope : Nat} (K : Nat) (J : Type v)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (natSlot : Nat → Fin scope)
    (e : Atom) (he : e.Valid n) :=
  renameScope ![label (rootIndex e he),label (parentIndex e he),label (childIndex e he),
    omega,zero,natSlot e.layer] (ActualRelationQuery.query.{u,v} K J)

theorem domainFormula_isSigmaOne {n scope : Nat} (K : Nat) (J : Type v)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (i : Fin n) :
    IsSigmaOne (domainFormula.{u,v} K J omega zero label i) :=
  (ActualAdequateQuery.query_isSigmaOne K J).renameScope _

theorem atomFormula_isSigmaOne {n scope : Nat} (K : Nat) (J : Type v)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (natSlot : Nat → Fin scope)
    (e : Atom) (he : e.Valid n) :
    IsSigmaOne (atomFormula.{u,v} K J omega zero label natSlot e he) :=
  (ActualRelationQuery.query_isSigmaOne K J).renameScope _

theorem realize_domainFormula {n scope K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (omega zero : Fin scope) (label : Fin n → Fin scope)
    (p : Fin scope → ZFCarrier V) (i : Fin n) :
    realize N (domainFormula.{u,v} K J omega zero label i) Empty.elim p ↔
      realize N (ActualAdequateQuery.query.{u,v} K J) Empty.elim ![p (label i),p omega,p zero] := by
  rw [domainFormula,realize_renameScope]
  have he : p ∘ ![label i,omega,zero] = ![p (label i),p omega,p zero] := by
    funext j; fin_cases j <;> rfl
  rw [he]

theorem realize_atomFormula {n scope K : Nat} {J : Type v} {V : ZFSet.{u}}
    (N : Interpretation K J (ZFCarrier V)) (omega zero : Fin scope) (label : Fin n → Fin scope)
    (natSlot : Nat → Fin scope) (p : Fin scope → ZFCarrier V) (e : Atom) (he : e.Valid n) :
    realize N (atomFormula.{u,v} K J omega zero label natSlot e he) Empty.elim p ↔
      realize N (ActualRelationQuery.query.{u,v} K J) Empty.elim
        ![p (label (rootIndex e he)),p (label (parentIndex e he)),p (label (childIndex e he)),
          p omega,p zero,p (natSlot e.layer)] := by
  rw [atomFormula,realize_renameScope]
  have hmap : p ∘ ![label (rootIndex e he),label (parentIndex e he),label (childIndex e he),
      omega,zero,natSlot e.layer] =
      ![p (label (rootIndex e he)),p (label (parentIndex e he)),p (label (childIndex e he)),
        p omega,p zero,p (natSlot e.layer)] := by
    funext j; fin_cases j <;> rfl
  rw [hmap]

theorem domain_sound {n scope K : Nat} {J : Type v} {top : Ordinal.{u}}
    (N : Interpretation K J (ZFCarrier (LStageZF top))) (hmem : N.mem = zfCarrierMem (LStageZF top))
    (omega zero : Fin scope) (label : Fin n → Fin scope) (p : Fin scope → ZFCarrier (LStageZF top))
    (v : Fin n → Ordinal.{u}) (hcodes : ∀ i, (v i).toZFSet = (p (label i)).val)
    (hOmega : (p omega).val = Ordinal.omega0.toZFSet) (hZero : (p zero).val = ∅)
    (i : Fin n) (h : realize N (domainFormula.{u,v} K J omega zero label i) Empty.elim p) :
    Adequate (v i) := by
  exact ActualAdequateQuery.query_sound (LStageZF_isTransitive top)
    (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L top)) N hmem (v i)
    ![p (label i),p omega,p zero] (hcodes i).symm hOmega hZero
    ((realize_domainFormula N omega zero label p i).mp h)

theorem domain_complete {n scope K : Nat} {J : Type v} {top : Ordinal.{u}}
    (hTop : Adequate top) (N : Interpretation K J (ZFCarrier (LStageZF top)))
    (hmem : N.mem = zfCarrierMem (LStageZF top)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (p : Fin scope → ZFCarrier (LStageZF top))
    (v : Fin n → Ordinal.{u}) (hcodes : ∀ i, (v i).toZFSet = (p (label i)).val)
    (hOmega : (p omega).val = Ordinal.omega0.toZFSet) (hZero : (p zero).val = ∅)
    (i : Fin n) (hD : Adequate (v i)) :
    realize N (domainFormula.{u,v} K J omega zero label i) Empty.elim p := by
  apply (realize_domainFormula N omega zero label p i).mpr
  exact (ActualAdequateQuery.realize_query_iff hTop N hmem hCol hSep (v i)
    ![p (label i),p omega,p zero] (hcodes i).symm hOmega hZero).mpr hD

theorem atom_sound {n scope K : Nat} {J : Type v} {top : Ordinal.{u}}
    (N : Interpretation K J (ZFCarrier (LStageZF top))) (hmem : N.mem = zfCarrierMem (LStageZF top))
    (omega zero : Fin scope) (label : Fin n → Fin scope) (natSlot : Nat → Fin scope)
    (p : Fin scope → ZFCarrier (LStageZF top)) (v : Fin n → Ordinal.{u})
    (hcodes : ∀ i, (v i).toZFSet = (p (label i)).val) (hmono : StrictMono v)
    (hD : ∀ i, Adequate (v i)) (hOmega : (p omega).val = Ordinal.omega0.toZFSet)
    (hZero : (p zero).val = ∅) (e : Atom) (he : e.Valid n)
    (hNat : (p (natSlot e.layer)).val = natCode e.layer)
    (h : realize N (atomFormula.{u,v} K J omega zero label natSlot e he) Empty.elim p) :
    AtomFinHolds R v e he := by
  change R e.layer (v (rootIndex e he)) (v (parentIndex e he)) (v (childIndex e he))
  have hrp : rootIndex e he ≤ parentIndex e he := he.1
  have hpc : parentIndex e he < childIndex e he := he.2.1
  haveI : Nonempty (ZFCarrier (LStageZF (v (parentIndex e he)))) :=
    ⟨⟨∅,empty_mem_LStageZF_of_isSuccLimit (hD (parentIndex e he)).2.1⟩⟩
  exact ActualRelationQuery.query_sound (hmono.monotone hrp) (hmono hpc)
    (LStageZF_isTransitive top) (fun _ hx => mem_L_of_mem hx (LStageZF_mem_L top)) N hmem
    ![p (label (rootIndex e he)),p (label (parentIndex e he)),p (label (childIndex e he)),
      p omega,p zero,p (natSlot e.layer)]
    (hcodes (rootIndex e he)).symm (hcodes (parentIndex e he)).symm (hcodes (childIndex e he)).symm
    hOmega hZero hNat ((realize_atomFormula N omega zero label natSlot p e he).mp h)

theorem atom_complete {n scope K : Nat} {J : Type v} {top : Ordinal.{u}}
    (hTop : Adequate top) (N : Interpretation K J (ZFCarrier (LStageZF top)))
    (hmem : N.mem = zfCarrierMem (LStageZF top)) (hCol : HasCollection N) (hSep : HasSeparation N)
    (omega zero : Fin scope) (label : Fin n → Fin scope) (natSlot : Nat → Fin scope)
    (p : Fin scope → ZFCarrier (LStageZF top)) (v : Fin n → Ordinal.{u})
    (hcodes : ∀ i, (v i).toZFSet = (p (label i)).val) (hmono : StrictMono v)
    (hD : ∀ i, Adequate (v i)) (hOmega : (p omega).val = Ordinal.omega0.toZFSet)
    (hZero : (p zero).val = ∅) (e : Atom) (he : e.Valid n)
    (hNat : (p (natSlot e.layer)).val = natCode e.layer) (hR : AtomFinHolds R v e he) :
    realize N (atomFormula.{u,v} K J omega zero label natSlot e he) Empty.elim p := by
  have hrp : rootIndex e he ≤ parentIndex e he := he.1
  have hpc : parentIndex e he < childIndex e he := he.2.1
  haveI : Nonempty (ZFCarrier (LStageZF (v (parentIndex e he)))) :=
    ⟨⟨∅,empty_mem_LStageZF_of_isSuccLimit (hD (parentIndex e he)).2.1⟩⟩
  apply (realize_atomFormula N omega zero label natSlot p e he).mpr
  exact (ActualRelationQuery.realize_query_iff (hmono.monotone hrp) (hmono hpc)
    hTop N hmem hCol hSep
    ![p (label (rootIndex e he)),p (label (parentIndex e he)),p (label (childIndex e he)),
      p omega,p zero,p (natSlot e.layer)]
    (hcodes (rootIndex e he)).symm (hcodes (parentIndex e he)).symm (hcodes (childIndex e he)).symm
    hOmega hZero hNat).mpr hR

end OneYTruth.ActualDomainAtomAdapter

#print axioms OneYTruth.ActualDomainAtomAdapter.domain_sound
#print axioms OneYTruth.ActualDomainAtomAdapter.domain_complete
#print axioms OneYTruth.ActualDomainAtomAdapter.atom_sound
#print axioms OneYTruth.ActualDomainAtomAdapter.atom_complete
