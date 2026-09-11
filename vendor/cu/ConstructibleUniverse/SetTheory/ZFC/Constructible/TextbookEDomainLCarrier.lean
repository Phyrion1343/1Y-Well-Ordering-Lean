/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEParameterizedDomain
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph

/-!
# The textbook E recursion domain in the constructible universe

This file proves the exact `LCarrier` semantics of the object-language
formulas for the textbook recursion domain `omega x omega` and its
well-founded relation.  These are the class and relation inputs needed before
the textbook recursion theorem can be replayed directly in `L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The standard omega formula -/

@[simp]
theorem satisfies_transitiveZFEmptyAt_lCarrier {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (transitiveZFEmptyAt i) s <->
      s i = emptyLCarrier := by
  simp only [transitiveZFEmptyAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact (h z hz).elim
    · intro hz
      exact (not_mem_emptyLCarrier z hz).elim
  · intro h z hz
    rw [h] at hz
    exact not_mem_emptyLCarrier z hz

@[simp]
theorem satisfies_transitiveZFSuccessorAt_lCarrier {n : Nat}
    (successor index : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (transitiveZFSuccessorAt successor index) s <->
      s successor = successorLCarrier (s index) := by
  simp only [transitiveZFSuccessorAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hforward, hbackward⟩
    apply lCarrier_extensionality
    intro z
    rw [successorLCarrier_val, ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases hforward z hz with hzIndex | hzEq
      · exact Or.inr hzIndex
      · exact Or.inl (congrArg Subtype.val hzEq)
    · rintro (hzEq | hz)
      · have hzEq' : z = s index := Subtype.ext hzEq
        subst z
        exact hindex
      · exact hbackward z hz
  · intro hsuccessor
    rw [hsuccessor]
    constructor
    · change (s index).1 ∈ (successorLCarrier (s index)).1
      rw [successorLCarrier_val, ZFSet.mem_insert_iff]
      exact Or.inl rfl
    · constructor
      · intro z hz
        change z.1 ∈ (successorLCarrier (s index)).1 at hz
        rw [successorLCarrier_val, ZFSet.mem_insert_iff] at hz
        rcases hz with hzEq | hzIndex
        · exact Or.inr (Subtype.ext hzEq)
        · exact Or.inl hzIndex
      · intro z hz
        change z.1 ∈ (successorLCarrier (s index)).1
        rw [successorLCarrier_val, ZFSet.mem_insert_iff]
        exact Or.inr hz

@[simp]
theorem satisfies_transitiveZFInductiveAt_lCarrier {n : Nat}
    (i : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (transitiveZFInductiveAt i) s <->
      IsInductiveSet (s i) := by
  simp only [transitiveZFInductiveAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_transitiveZFEmptyAt_lCarrier,
    satisfies_transitiveZFSuccessorAt_lCarrier,
    snoc_last, snoc_castSucc, IsInductiveSet]
  constructor
  · rintro ⟨⟨empty, hempty, hemptyMem⟩, hsuccessor⟩
    constructor
    · simpa only [hempty] using hemptyMem
    · intro x hx
      rcases hsuccessor x hx with ⟨next, hnext, hnextMem⟩
      simpa only [hnext] using hnextMem
  · rintro ⟨hempty, hsuccessor⟩
    refine ⟨⟨emptyLCarrier, rfl, hempty⟩, ?_⟩
    · intro x hx
      exact ⟨successorLCarrier x, rfl, hsuccessor x hx⟩

@[simp]
theorem satisfies_standardOmegaAt_lCarrier {n : Nat} (i : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (standardOmegaAt i) s <->
      s i = omegaLCarrier := by
  simp only [standardOmegaAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_boundedAll,
    satisfies_transitiveZFInductiveAt_lCarrier,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨homegaInductive, hminimal⟩
    apply lCarrier_extensionality
    intro z
    constructor
    · intro hz
      exact hminimal omegaLCarrier omegaLCarrier_isInductiveSet z hz
    · intro hz
      exact omegaLCarrier_subset_of_isInductiveSet homegaInductive z hz
  · intro homega
    rw [homega]
    refine ⟨omegaLCarrier_isInductiveSet, ?_⟩
    intro w hw x hx
    exact omegaLCarrier_subset_of_isInductiveSet hw x hx

/-! ## The parameter-free domain and relation -/

@[simp]
theorem satisfies_textbookEDomainFormula_lCarrier
    (x : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.domainFormula ![x] <->
      x.1 ∈ TextbookEDomain := by
  simp only [TextbookEFormula.domainFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homegaFormula, hxProductFormula⟩
    have homega : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 1)
        ![x, omega]).mp homegaFormula
    subst omega
    have hdelta :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.productMemberDeltaAt
          (0 : Fin 2) (Fin.last 1) (Fin.last 1))
        ![x, omegaLCarrier]).mp hxProductFormula
    have hassign :
        (fun i => (![x, omegaLCarrier] i).1) =
          ![x.1, omegaLCarrier.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign, Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_productMemberDeltaAt] at hdelta
    change x.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1 at hdelta
    change x.1 ∈ textbookEDomainZF
    simpa only [textbookEDomainZF, omegaLCarrier] using hdelta
  · intro hxDomain
    refine ⟨omegaLCarrier, ?_, ?_⟩
    · exact (satisfies_standardOmegaAt_lCarrier (Fin.last 1)
        ![x, omegaLCarrier]).mpr rfl
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.productMemberDeltaAt
          (0 : Fin 2) (Fin.last 1) (Fin.last 1))
        ![x, omegaLCarrier]).mpr
      have hassign :
          (fun i => (![x, omegaLCarrier] i).1) =
            ![x.1, omegaLCarrier.1] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign, Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_productMemberDeltaAt]
      change x.1 ∈ ZFSet.prod omegaLCarrier.1 omegaLCarrier.1
      change x.1 ∈ textbookEDomainZF at hxDomain
      simpa only [textbookEDomainZF, omegaLCarrier] using hxDomain

@[simp]
theorem satisfies_textbookERelationFormula_lCarrier
    (left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.relationFormula
        ![left, right] <->
      ClassRel TextbookERelation left.1 right.1 := by
  simp only [TextbookEFormula.relationFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homegaFormula, hrelationFormula⟩
    have homega : omega = omegaLCarrier :=
      (satisfies_standardOmegaAt_lCarrier (Fin.last 2)
        ![left, right, omega]).mp homegaFormula
    subst omega
    have hdelta :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookEFormula.relationDeltaAt
          (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
        ![left, right, omegaLCarrier]).mp hrelationFormula
    have hassign :
        (fun i => (![left, right, omegaLCarrier] i).1) =
          ![left.1, right.1, omegaLCarrier.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign, Delta0Formula.satisfies_toFO,
      TextbookEFormula.satisfies_relationDeltaAt] at hdelta
    change
      (∃ i : ZFSet.{u}, i ∈ omegaLCarrier.1 ∧
        ∃ k : ZFSet.{u}, k ∈ omegaLCarrier.1 ∧
          ∃ m : ZFSet.{u}, m ∈ omegaLCarrier.1 ∧
            ∃ n : ZFSet.{u}, n ∈ omegaLCarrier.1 ∧
              left.1 = ZFSet.pair i k ∧
              right.1 = ZFSet.pair m n ∧ i ∈ m) at hdelta
    rw [classRel_textbookERelation_iff]
    rcases hdelta with
      ⟨i, hi, k, hk, m, hm, n, hn, hleft, hright, him⟩
    exact ⟨i, k, m, n,
      by simpa only [omegaLCarrier] using hi,
      by simpa only [omegaLCarrier] using hk,
      by simpa only [omegaLCarrier] using hm,
      by simpa only [omegaLCarrier] using hn,
      hleft, hright, him⟩
  · intro hrelation
    refine ⟨omegaLCarrier, ?_, ?_⟩
    · exact (satisfies_standardOmegaAt_lCarrier (Fin.last 2)
        ![left, right, omegaLCarrier]).mpr rfl
    · apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookEFormula.relationDeltaAt
          (0 : Fin 3) (1 : Fin 3) (Fin.last 2))
        ![left, right, omegaLCarrier]).mpr
      have hassign :
          (fun i => (![left, right, omegaLCarrier] i).1) =
            ![left.1, right.1, omegaLCarrier.1] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign, Delta0Formula.satisfies_toFO,
        TextbookEFormula.satisfies_relationDeltaAt]
      change
        ∃ i : ZFSet.{u}, i ∈ omegaLCarrier.1 ∧
          ∃ k : ZFSet.{u}, k ∈ omegaLCarrier.1 ∧
            ∃ m : ZFSet.{u}, m ∈ omegaLCarrier.1 ∧
              ∃ n : ZFSet.{u}, n ∈ omegaLCarrier.1 ∧
                left.1 = ZFSet.pair i k ∧
                right.1 = ZFSet.pair m n ∧ i ∈ m
      rw [classRel_textbookERelation_iff] at hrelation
      rcases hrelation with
        ⟨i, k, m, n, hi, hk, hm, hn, hleft, hright, him⟩
      exact ⟨i, by simpa only [omegaLCarrier] using hi,
        k, by simpa only [omegaLCarrier] using hk,
        m, by simpa only [omegaLCarrier] using hm,
        n, by simpa only [omegaLCarrier] using hn,
        hleft, hright, him⟩

/-! ## The dummy-parameter presentation used by recursion -/

@[simp]
theorem satisfies_textbookEDomainWithParamFormula_lCarrier
    (a key : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookEFormula.textbookEDomainWithParamFormula ![a, key] <->
      key.1 ∈ TextbookEDomain := by
  rw [TextbookEFormula.textbookEDomainWithParamFormula,
    FOFormula.satisfies_rename]
  have hassign :
      (fun i => ![a, key]
        (TextbookEFormula.textbookEDomainWithParamRename i)) =
        ![key] := by
    funext i
    fin_cases i
    rfl
  rw [hassign, satisfies_textbookEDomainFormula_lCarrier]

@[simp]
theorem satisfies_textbookERelationWithParamFormula_lCarrier
    (a left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookEFormula.textbookERelationWithParamFormula
        ![a, left, right] <->
      ClassRel TextbookERelation left.1 right.1 := by
  rw [TextbookEFormula.textbookERelationWithParamFormula,
    FOFormula.satisfies_rename]
  have hassign :
      (fun i => ![a, left, right]
        (TextbookEFormula.textbookERelationWithParamRename i)) =
        ![left, right] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_textbookERelationFormula_lCarrier]

/-! ## Raw/subtype bridge forms -/

@[simp]
theorem satisfiesIn_L_textbookEDomainWithParamFormula_iff
    (a key : LCarrier.{u}) :
    SatisfiesIn (L : Set ZFSet.{u})
        TextbookEFormula.textbookEDomainWithParamFormula
        ![a.1, key.1] <->
      key.1 ∈ TextbookEDomain := by
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
    TextbookEFormula.textbookEDomainWithParamFormula ![a, key]
  have hassign :
      (fun i => (![a, key] i).1) = ![a.1, key.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign] at hbridge
  exact hbridge.symm.trans
    (satisfies_textbookEDomainWithParamFormula_lCarrier a key)

@[simp]
theorem satisfiesIn_L_textbookERelationWithParamFormula_iff
    (a left right : LCarrier.{u}) :
    SatisfiesIn (L : Set ZFSet.{u})
        TextbookEFormula.textbookERelationWithParamFormula
        ![a.1, left.1, right.1] <->
      ClassRel TextbookERelation left.1 right.1 := by
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
    TextbookEFormula.textbookERelationWithParamFormula
    ![a, left, right]
  have hassign :
      (fun i => (![a, left, right] i).1) =
        ![a.1, left.1, right.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign] at hbridge
  exact hbridge.symm.trans
    (satisfies_textbookERelationWithParamFormula_lCarrier
      a left right)

/-- Every textbook predecessor of a constructible key is constructible.
For `<m,n>` all predecessors lie in the constructible set `m x omega`. -/
theorem textbookERelation_predecessorsClosedIn_L :
    PredecessorsClosedIn (L : Set ZFSet.{u})
      TextbookEDomain TextbookERelation := by
  intro x _hxL y hyDomain hyRelation
  rcases mem_textbookEDomain_iff.mp
      (textbookERelation_isRelationOn.right_mem hyRelation) with
    ⟨m, hm, n, hn, hxPair⟩
  have hyProduct : y ∈ ZFSet.prod m textbookEOmegaZF := by
    apply (textbookE_predecessorSet hm hn y).mpr
    simpa only [hxPair] using And.intro hyDomain hyRelation
  let mL : LCarrier.{u} :=
    ⟨m, mem_L_of_mem hm omegaLCarrier.2⟩
  have hproductL : ZFSet.prod m textbookEOmegaZF ∈ L := by
    simpa only [mL, prodLCarrier_val, omegaLCarrier] using
      (prodLCarrier mL omegaLCarrier).2
  exact mem_L_of_mem hyProduct hproductL

/-! ## Set-likeness inside `L` -/

/-- The formula defining the textbook relation verifies set-likeness in
`L`.  At `<m,n>` its displayed predecessor set is the actual constructible
product `m x omega`. -/
theorem satisfies_textbookESetLikeRelationOnFormula_withParam_lCarrier
    (a : LCarrier.{u}) :
    FOFormula.Satisfies LMem
      (setLikeRelationOnFormula
        TextbookEFormula.textbookEDomainWithParamFormula
        TextbookEFormula.textbookERelationWithParamFormula)
      ![a] := by
  apply (satisfies_lCarrier_iff_satisfiesIn_L
    (setLikeRelationOnFormula
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula)
    ![a]).mpr
  have hparameter : (fun i => (![a] i).1) = ![a.1] := by
    funext i
    fin_cases i
    rfl
  rw [hparameter, satisfiesIn_setLikeRelationOnFormula_iff]
  constructor
  · intro y hyL x hxL hrelationFormula
    let yL : LCarrier.{u} := ⟨y, hyL⟩
    let xL : LCarrier.{u} := ⟨x, hxL⟩
    have hrelationAssignment :
        snoc (snoc ![a.1] y) x = ![a.1, y, x] := by
      funext i
      fin_cases i <;> rfl
    have hrelation : ClassRel TextbookERelation y x := by
      apply (satisfiesIn_L_textbookERelationWithParamFormula_iff
        a yL xL).mp
      simpa only [yL, xL, hrelationAssignment] using hrelationFormula
    rw [classRel_textbookERelation_iff] at hrelation
    rcases hrelation with
      ⟨i, k, m, n, hi, hk, hm, hn, hyPair, hxPair, him⟩
    have hyDomain : y ∈ TextbookEDomain :=
      mem_textbookEDomain_iff.mpr ⟨i, hi, k, hk, hyPair⟩
    have hxDomain : x ∈ TextbookEDomain :=
      mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, hxPair⟩
    have hyFormula :=
      (satisfiesIn_L_textbookEDomainWithParamFormula_iff a yL).mpr
        hyDomain
    have hxFormula :=
      (satisfiesIn_L_textbookEDomainWithParamFormula_iff a xL).mpr
        hxDomain
    have hyAssignment : snoc ![a.1] y = ![a.1, y] := by
      funext j
      fin_cases j <;> rfl
    have hxAssignment : snoc ![a.1] x = ![a.1, x] := by
      funext j
      fin_cases j <;> rfl
    exact ⟨by simpa only [yL, hyAssignment] using hyFormula,
      by simpa only [xL, hxAssignment] using hxFormula⟩
  · intro x hxL hxFormula
    let xL : LCarrier.{u} := ⟨x, hxL⟩
    have hxAssignment : snoc ![a.1] x = ![a.1, x] := by
      funext i
      fin_cases i <;> rfl
    have hxDomain : x ∈ TextbookEDomain :=
      (satisfiesIn_L_textbookEDomainWithParamFormula_iff a xL).mp
        (by simpa only [xL, hxAssignment] using hxFormula)
    rcases mem_textbookEDomain_iff.mp hxDomain with
      ⟨m, hm, n, hn, hxPair⟩
    let mL : LCarrier.{u} :=
      ⟨m, mem_L_of_mem hm omegaLCarrier.2⟩
    let predecessors : LCarrier.{u} := prodLCarrier mL omegaLCarrier
    refine ⟨predecessors.1, predecessors.2, ?_⟩
    intro y hyL
    let yL : LCarrier.{u} := ⟨y, hyL⟩
    have hyAssignment : snoc ![a.1] y = ![a.1, y] := by
      funext i
      fin_cases i <;> rfl
    have hrelationAssignment :
        snoc (snoc ![a.1] y) x = ![a.1, y, x] := by
      funext i
      fin_cases i <;> rfl
    rw [show
      SatisfiesIn (L : Set ZFSet.{u})
          TextbookEFormula.textbookEDomainWithParamFormula
          (snoc ![a.1] y) <-> y ∈ TextbookEDomain by
        simpa only [yL, hyAssignment] using
          (satisfiesIn_L_textbookEDomainWithParamFormula_iff a yL)]
    rw [show
      SatisfiesIn (L : Set ZFSet.{u})
          TextbookEFormula.textbookERelationWithParamFormula
          (snoc (snoc ![a.1] y) x) <->
            ClassRel TextbookERelation y x by
        simpa only [yL, xL, hrelationAssignment] using
          (satisfiesIn_L_textbookERelationWithParamFormula_iff
            a yL xL)]
    change y ∈ ZFSet.prod m textbookEOmegaZF <->
      y ∈ TextbookEDomain ∧ ClassRel TextbookERelation y x
    rw [hxPair]
    exact textbookE_predecessorSet hm hn y

end

end Constructible.Model
