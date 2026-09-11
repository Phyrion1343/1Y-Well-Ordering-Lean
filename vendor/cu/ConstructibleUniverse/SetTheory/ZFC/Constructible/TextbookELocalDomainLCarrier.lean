/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomainLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalDomainLCarrier

/-!
# Local domains for the textbook E recursion in L

The textbook recursion relation compares only the first natural coordinate.
Consequently every iterated predecessor of `<m,n>` is already an immediate
predecessor, and its predecessor closure is exactly `m x omega`.  This file
identifies the generic local recursion domain with the concrete set
`{<m,n>} union (m x omega)` and proves that it belongs to `L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Transitivity of the textbook relation -/

theorem textbookERelation_transitive
    {left middle right : ZFSet.{u}}
    (hlm : ClassRel TextbookERelation left middle)
    (hmr : ClassRel TextbookERelation middle right) :
    ClassRel TextbookERelation left right := by
  rw [classRel_textbookERelation_iff] at hlm hmr ⊢
  rcases hlm with
    ⟨i, k, m, n, hi, hk, hm, hn, hleft, hmiddle, him⟩
  rcases hmr with
    ⟨m', n', r, s, hm', hn', hr, hs, hmiddle', hright, hmr'⟩
  have hcoordinates : m = m' ∧ n = n' := by
    apply ZFSet.pair_inj.mp
    exact hmiddle.symm.trans hmiddle'
  have hrOrdinal : r.IsOrdinal :=
    (ZFSet.isOrdinal_toZFSet (Ordinal.omega0 : Ordinal.{u})).mem hr
  have hir : i ∈ r := by
    exact hrOrdinal.isTransitive.mem_trans him
      (by simpa only [hcoordinates.1] using hmr')
  exact ⟨i, k, r, s, hi, hk, hr, hs, hleft, hright, hir⟩

/-! ## Collapse of all finite predecessor layers -/

private theorem textbookE_predecessorLayer_subset_first
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    ∀ stage : Nat,
      predecessorLayer TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) stage ⊆
        ZFSet.prod m textbookEOmegaZF := by
  intro stage
  induction stage with
  | zero =>
      intro z hz
      rw [predecessorLayer_zero] at hz
      have hzSpec :=
        (displayedPredecessors_spec
          textbookERelation_hasSetPredecessorsOn
          (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩) z).mp hz
      exact (textbookE_predecessorSet hm hn z).mpr hzSpec
  | succ stage ih =>
      intro z hz
      rcases (mem_predecessorLayer_succ_iff
          textbookERelation_hasSetPredecessorsOn
          (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩)
          stage).mp hz with
        ⟨y, hyLayer, hzDomain, hzy⟩
      have hyFirst : y ∈ ZFSet.prod m textbookEOmegaZF := ih hyLayer
      have hySpec := (textbookE_predecessorSet hm hn y).mp hyFirst
      exact (textbookE_predecessorSet hm hn z).mpr
        ⟨hzDomain, textbookERelation_transitive hzy hySpec.2⟩

/-- For the textbook relation, all iterated predecessors are already in the
first predecessor set `m x omega`. -/
theorem textbookE_predecessorClosure_eq
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    predecessorClosure TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) =
      ZFSet.prod m textbookEOmegaZF := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_predecessorClosure_iff.mp hz with ⟨stage, hzStage⟩
    exact textbookE_predecessorLayer_subset_first hm hn stage hzStage
  · intro hz
    apply mem_predecessorClosure_iff.mpr
    refine ⟨0, ?_⟩
    rw [predecessorLayer_zero]
    apply (displayedPredecessors_spec
      textbookERelation_hasSetPredecessorsOn
      (mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩) z).mpr
    exact (textbookE_predecessorSet hm hn z).mp hz

/-- The generic local domain at `<m,n>` is the concrete one-point extension
of `m x omega`. -/
theorem textbookE_localRecursionDomain_eq
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn (ZFSet.pair m n) =
      insert (ZFSet.pair m n) (ZFSet.prod m textbookEOmegaZF) := by
  apply ZFSet.ext
  intro z
  rw [mem_localRecursionDomain_iff,
    textbookE_predecessorClosure_eq hm hn,
    ZFSet.mem_insert_iff]

/-! ## Constructibility of the local domain -/

/-- The local recursion domain at every standard coded key is an actual
member of `L`. -/
theorem textbookE_localRecursionDomain_natCode_mem_L
    (m n : Nat) :
    localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m : ZFSet.{u})
          (natCode n : ZFSet.{u})) ∈ L := by
  have hm : (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  have hn : (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)
  have hdomain := textbookE_localRecursionDomain_eq
    (m := (natCode m : ZFSet.{u}))
    (n := (natCode n : ZFSet.{u})) hm hn
  rw [hdomain]
  have hkey : ZFSet.pair (natCode m) (natCode n) ∈ L :=
    orderedPair_mem_L (natCode_mem_L m) (natCode_mem_L n)
  let mL : Model.LCarrier.{u} := ⟨natCode m, natCode_mem_L m⟩
  have hproduct : ZFSet.prod (natCode m) textbookEOmegaZF ∈ L := by
    simpa only [mL, Model.prodLCarrier_val, Model.omegaLCarrier,
      textbookEOmegaZF] using
      (Model.prodLCarrier mL Model.omegaLCarrier).2
  rw [ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L hkey) hproduct

namespace Model

local notation "LMem" => lCarrierMem

/-! ## Packaged keys and local domains -/

/-- The standard textbook recursion key `<m,n>` as an actual element of
`L`. -/
def textbookEKeyLCarrier (m n : Nat) : LCarrier.{u} :=
  orderedPairLCarrier
    ⟨natCode m, natCode_mem_L m⟩
    ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem textbookEKeyLCarrier_val (m n : Nat) :
    (textbookEKeyLCarrier m n : LCarrier.{u}).1 =
      ZFSet.pair (natCode m) (natCode n) :=
  rfl

theorem textbookEKeyLCarrier_mem_domain (m n : Nat) :
    (textbookEKeyLCarrier m n : LCarrier.{u}).1 ∈ TextbookEDomain := by
  apply mem_textbookEDomain_iff.mpr
  refine ⟨natCode m, ?_, natCode n, ?_, rfl⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 m)
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)

/-- The concrete local domain at a standard textbook key, packaged as an
actual member of `L`. -/
def textbookELocalDomainLCarrier (m n : Nat) : LCarrier.{u} :=
  ⟨localRecursionDomain TextbookEDomain TextbookERelation
      textbookERelation_hasSetPredecessorsOn
      (ZFSet.pair (natCode m) (natCode n)),
    textbookE_localRecursionDomain_natCode_mem_L m n⟩

@[simp]
theorem textbookELocalDomainLCarrier_val (m n : Nat) :
    (textbookELocalDomainLCarrier m n : LCarrier.{u}).1 =
      localRecursionDomain TextbookEDomain TextbookERelation
        textbookERelation_hasSetPredecessorsOn
        (ZFSet.pair (natCode m) (natCode n)) :=
  rfl

/-! ## Exact semantics of the least-closed-set formula -/

@[simp]
theorem satisfies_textbookELocalDomainFormula_lCarrier
    (a domain : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (localDomainFormula
          TextbookEFormula.textbookEDomainWithParamFormula
          TextbookEFormula.textbookERelationWithParamFormula)
        ![a, textbookEKeyLCarrier m n, domain] ↔
      domain.1 = (textbookELocalDomainLCarrier m n).1 := by
  let key : LCarrier.{u} := textbookEKeyLCarrier m n
  have hclass : ∀ z : LCarrier.{u},
      FOFormula.Satisfies LMem
          TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a] z) ↔ z.1 ∈ TextbookEDomain := by
    intro z
    have hassign : snoc ![a] z = ![a, z] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_textbookEDomainWithParamFormula_lCarrier]
  have hrelationFormula : ∀ y z : LCarrier.{u},
      FOFormula.Satisfies LMem
          TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a] y) z) ↔
        ClassRel TextbookERelation y.1 z.1 := by
    intro y z
    have hassign : snoc (snoc ![a] y) z = ![a, y, z] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_textbookERelationWithParamFormula_lCarrier]
  have hsemantic :=
    satisfies_localDomainFormula_lCarrier_iff_eq_localRecursionDomain
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      ![a] hclass hrelationFormula
      textbookERelation_isRelationOn
      textbookERelation_hasSetPredecessorsOn
      textbookERelation_predecessorsClosedIn_L
      (x := key) (domain := domain)
      (textbookEKeyLCarrier_mem_domain m n)
      (textbookE_localRecursionDomain_natCode_mem_L m n)
  have hassign : snoc (snoc ![a] key) domain =
      ![a, textbookEKeyLCarrier m n, domain] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hassign, key, textbookEKeyLCarrier_val,
    textbookELocalDomainLCarrier_val] using
    hsemantic

end Model

end

end Constructible
