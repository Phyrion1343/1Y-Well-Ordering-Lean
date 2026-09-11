/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Model

/-!
# Textbook local recursion domains over L

This is the proper-class `LCarrier` counterpart of
`satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain`.  It retains the
same exact class semantics, relation semantics, relation-on-class,
set-likeness, predecessor closure, and represented-local-domain hypotheses.
The only change is that transitivity is supplied by the already proved
transitivity of `L` rather than by an ambient set `M : ZFSet`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-- Over `LCarrier`, the least downward-closed-set formula denotes the
concrete textbook local recursion domain whenever that domain is represented
by an actual member of `L`. -/
theorem satisfies_localDomainFormula_lCarrier_iff_eq_localRecursionDomain
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : ∀ z : LCarrier.{u},
      FOFormula.Satisfies LMem classFormula (snoc params z) ↔ z.1 ∈ A)
    (hrelationFormula : ∀ y z : LCarrier.{u},
      FOFormula.Satisfies LMem relationFormula
          (snoc (snoc params y) z) ↔ ClassRel R y.1 z.1)
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (L : Set ZFSet.{u}) A R)
    {x domain : LCarrier.{u}} (hxA : x.1 ∈ A)
    (hlocalL : localRecursionDomain A R hsetLike x.1 ∈ L) :
    FOFormula.Satisfies LMem
        (localDomainFormula classFormula relationFormula)
        (snoc (snoc params x) domain) ↔
      domain.1 = localRecursionDomain A R hsetLike x.1 := by
  let paramsRaw : Tuple ZFSet.{u} n := fun i => (params i).1
  have hclassRaw (z : ZFSet.{u}) (hzL : z ∈ L) :
      SatisfiesIn (L : Set ZFSet.{u}) classFormula
          (snoc paramsRaw z) ↔ z ∈ A := by
    let zL : LCarrier.{u} := ⟨z, hzL⟩
    have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
      classFormula (snoc params zL)
    have hassign :
        (fun i => (snoc params zL i).1) = snoc paramsRaw z := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last, zL]
      · simp only [snoc_castSucc, paramsRaw]
    rw [hassign] at hbridge
    exact hbridge.symm.trans (hclass zL)
  have hrelationRaw (y : ZFSet.{u}) (hyL : y ∈ L)
      (z : ZFSet.{u}) (hzL : z ∈ L) :
      SatisfiesIn (L : Set ZFSet.{u}) relationFormula
          (snoc (snoc paramsRaw y) z) ↔ ClassRel R y z := by
    let yL : LCarrier.{u} := ⟨y, hyL⟩
    let zL : LCarrier.{u} := ⟨z, hzL⟩
    have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
      relationFormula (snoc (snoc params yL) zL)
    have hassign :
        (fun i => (snoc (snoc params yL) zL i).1) =
          snoc (snoc paramsRaw y) z := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last, zL]
      · refine Fin.lastCases ?_ (fun k => ?_) j
        · simp only [snoc_castSucc, snoc_last, yL]
        · simp only [snoc_castSucc, paramsRaw]
    rw [hassign] at hbridge
    exact hbridge.symm.trans (hrelationFormula yL zL)
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
    (localDomainFormula classFormula relationFormula)
    (snoc (snoc params x) domain)
  have hassignment :
      (fun i => (snoc (snoc params x) domain i).1) =
        snoc (snoc paramsRaw x.1) domain.1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [snoc_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [snoc_castSucc, snoc_last]
      · simp only [snoc_castSucc, paramsRaw]
  rw [hassignment] at hbridge
  rw [hbridge]
  let dlocal := localRecursionDomain A R hsetLike x.1
  have hlocalSubsetA : (dlocal : Set ZFSet.{u}) ⊆ A :=
    localRecursionDomain_subset hsetLike hxA
  have hlocalClosed : ∀ t, t ∈ dlocal → ∀ y,
      y ∈ A → ClassRel R y t → y ∈ dlocal := by
    intro t ht y _hyA hyt
    exact localRecursionDomain_predecessorClosed
      hrelation hsetLike hxA ht hyt
  constructor
  · intro hformula
    rcases (satisfiesIn_localDomainFormula_iff
      (L : Set ZFSet.{u}) classFormula relationFormula
      paramsRaw x.1 domain.1).mp hformula with
      ⟨_hxFormula, hxDomain, hdomainSubset, hdomainClosed, hleast⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hzDomain
      have hzL : z ∈ L := mem_L_of_mem hzDomain domain.2
      exact hleast dlocal hlocalL
        (mem_localRecursionDomain_iff.mpr (Or.inl rfl))
        (by
          intro w hwL hwLocal
          exact (hclassRaw w hwL).mpr (hlocalSubsetA hwLocal))
        (by
          intro t htL htLocal y hyL hyFormula hyRelFormula
          have hyA : y ∈ A := (hclassRaw y hyL).mp hyFormula
          have hyt : ClassRel R y t :=
            (hrelationRaw y hyL t htL).mp hyRelFormula
          exact hlocalClosed t htLocal y hyA hyt)
        z hzL hzDomain
    · intro hzLocal
      have hdomainSubsetA : (domain.1 : Set ZFSet.{u}) ⊆ A := by
        intro w hwDomain
        have hwL : w ∈ L := mem_L_of_mem hwDomain domain.2
        exact (hclassRaw w hwL).mp
          (hdomainSubset w hwL hwDomain)
      have hdomainClosedAmbient : ∀ t, t ∈ domain.1 → ∀ y,
          y ∈ A → ClassRel R y t → y ∈ domain.1 := by
        intro t htDomain y hyA hyt
        have htL : t ∈ L := mem_L_of_mem htDomain domain.2
        have hyL : y ∈ L := hclosedIn t htL y hyA hyt
        exact hdomainClosed t htL htDomain y hyL
          ((hclassRaw y hyL).mpr hyA)
          ((hrelationRaw y hyL t htL).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxDomain
        hdomainClosedAmbient hzLocal
  · intro hdomain
    apply (satisfiesIn_localDomainFormula_iff
      (L : Set ZFSet.{u}) classFormula relationFormula
      paramsRaw x.1 domain.1).mpr
    rw [hdomain]
    refine ⟨(hclassRaw x.1 x.2).mpr hxA,
      mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_, ?_, ?_⟩
    · intro z hzL hzLocal
      exact (hclassRaw z hzL).mpr (hlocalSubsetA hzLocal)
    · intro t htL htLocal y hyL hyFormula hyRelFormula
      have hyA : y ∈ A := (hclassRaw y hyL).mp hyFormula
      have hyt : ClassRel R y t :=
        (hrelationRaw y hyL t htL).mp hyRelFormula
      exact hlocalClosed t htLocal y hyA hyt
    · intro candidate hcandidateL hxCandidate hcandidateSubset
        hcandidateClosed z hzL hzLocal
      have hcandidateClosedAmbient : ∀ t, t ∈ candidate → ∀ y,
          y ∈ A → ClassRel R y t → y ∈ candidate := by
        intro t htCandidate y hyA hyt
        have htL : t ∈ L := mem_L_of_mem htCandidate hcandidateL
        have hyL : y ∈ L := hclosedIn t htL y hyA hyt
        exact hcandidateClosed t htL htCandidate y hyL
          ((hclassRaw y hyL).mpr hyA)
          ((hrelationRaw y hyL t htL).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxCandidate
        hcandidateClosedAmbient hzLocal

end

end Constructible.Model
