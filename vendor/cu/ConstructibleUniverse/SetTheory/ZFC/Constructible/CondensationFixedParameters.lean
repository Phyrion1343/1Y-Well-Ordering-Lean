/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistory
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefZFCollapse
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiCollapseOrdinals

/-!
# Canonical parameters in elementary substructures of constructible levels

The thirteen constants used by the internal stage recursion are not extra
parameters in the Condensation Lemma.  They are uniquely characterized by a
parameter-free first-order assertion: there are thirteen objects satisfying
`canonicalStageParametersFormula`.

This file first checks the exact semantics of the open matrix over every
limit level `L_theta` above `omega`.  It then existentially closes all thirteen
variables, transfers that closed sentence by full elementarity, and uses the
same semantic characterization to identify the witnesses in the elementary
substructure with the canonical constants.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Model

noncomputable section

private theorem satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

/-- In a transitive carrier, the formula `emptySetAt i` says exactly that
coordinate `i` is the ambient empty set. -/
theorem satisfiesIn_emptySetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (emptySetAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  rw [emptySetAt, satisfiesIn_all_iff]
  simp only [SatisfiesIn, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h z (hU.mem_trans hz (hs i)) hz).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · intro h z _hzU hz
    rw [h] at hz
    exact (ZFSet.notMem_empty z hz).elim

/-- The bounded successor formula is absolute to a transitive carrier. -/
theorem satisfiesIn_successorSetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive) {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt successor index) s <->
      s successor = insert (s index) (s index) := by
  let sU : Tuple (ZFCarrier U) n := fun j => ⟨s j, hs j⟩
  have hbridge := satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) (successorSetAt successor index) sU
  have hvalues : (fun j => (sU j).1) = s := by
    funext j
    rfl
  rw [hvalues] at hbridge
  change
    (FOFormula.Satisfies (zfCarrierMem U)
        (successorSetAt successor index) sU <->
      SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt successor index) s) at hbridge
  have habsolute := Delta0Formula.satisfies_toFO_absolute hU
    (Delta0Formula.successorAt successor index) sU
  change
    (FOFormula.Satisfies (zfCarrierMem U)
        (successorSetAt successor index) sU <->
      FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
        (successorSetAt successor index) (fun j => (sU j).1))
      at habsolute
  rw [hvalues] at habsolute
  have hambient :
      FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
          (successorSetAt successor index) s <->
        s successor = insert (s index) (s index) := by
    simpa only [successorSetAt, Delta0Formula.ZFMem] using
      (Delta0Formula.satisfies_successorFOAt_ambient
        successor index s)
  exact hbridge.symm.trans (habsolute.trans hambient)

/-- Raw external meaning of being inductive inside a carrier. -/
def IsInductiveSetIn (U w : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ w /\
    forall x : ZFSet.{u}, x ∈ U -> x ∈ w -> insert x x ∈ w

/-- Over a transitive carrier containing the empty set and closed under von
Neumann successor, `inductiveSetAt` has its ordinary set-theoretic meaning. -/
theorem satisfiesIn_inductiveSetAt_iff
    {U : ZFSet.{u}} (hU : U.IsTransitive)
    (hemptyU : (∅ : ZFSet.{u}) ∈ U)
    (hsuccU : forall x : ZFSet.{u}, x ∈ U -> insert x x ∈ U)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ U) :
    SatisfiesIn (U : Set ZFSet.{u}) (inductiveSetAt i) s <->
      IsInductiveSetIn U (s i) := by
  simp only [inductiveSetAt, SatisfiesIn, satisfiesIn_all_iff,
    satisfiesIn_imp_iff, snoc_last, snoc_castSucc, IsInductiveSetIn]
  constructor
  · rintro ⟨⟨e, heU, heEmpty, heMem⟩, hsucc⟩
    have he : e = (∅ : ZFSet.{u}) := by
      simpa only [snoc_last] using
        (satisfiesIn_emptySetAt_iff hU (Fin.last n) (snoc s e) (by
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa using heU
        · simpa using hs k)).mp heEmpty
    constructor
    · simpa only [he] using heMem
    · intro x hxU hxw
      rcases hsucc x hxU hxw with ⟨next, hnextU, hnext, hnextMem⟩
      have hnextEq : next = insert x x := by
        simpa only [snoc_last, snoc_castSucc] using
          (satisfiesIn_successorSetAt_iff hU
          (Fin.last (n + 1)) (Fin.last n).castSucc
          (snoc (snoc s x) next) (by
            intro j
            refine Fin.lastCases ?_ (fun j' => ?_) j
            · simpa using hnextU
            · refine Fin.lastCases ?_ (fun k => ?_) j'
              · simpa using hxU
              · simpa using hs k)).mp hnext
      simpa only [hnextEq] using hnextMem
  · rintro ⟨hempty, hsucc⟩
    constructor
    · refine ⟨∅, hemptyU, ?_, hempty⟩
      apply (satisfiesIn_emptySetAt_iff hU (Fin.last n)
        (snoc s (∅ : ZFSet.{u})) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hemptyU
          · simpa using hs k)).mpr
      simp only [snoc_last]
    · intro x hxU hxw
      refine ⟨insert x x, hsuccU x hxU, ?_, hsucc x hxU hxw⟩
      apply (satisfiesIn_successorSetAt_iff hU
        (Fin.last (n + 1)) (Fin.last n).castSucc
        (snoc (snoc s x) (insert x x)) (by
          intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · simpa using hsuccU x hxU
          · refine Fin.lastCases ?_ (fun k => ?_) j'
            · simpa using hxU
            · simpa using hs k)).mpr
      simp only [snoc_last, snoc_castSucc]

/-- The standard `omega` is internally inductive in every transitive carrier
that contains it and is closed under von Neumann successor. -/
theorem omega_isInductiveSetIn (U : ZFSet.{u}) :
    IsInductiveSetIn U Ordinal.omega0.toZFSet := by
  constructor
  · rw [Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro x _hxU hxOmega
    rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
    rw [← Ordinal.toZFSet_add_one]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (by
        rw [← Order.succ_eq_add_one]
        exact Ordinal.isSuccLimit_omega0.succ_lt halpha)

/-- Every standard natural-number ordinal belongs to an internally inductive
set. -/
theorem natOrdinal_mem_of_isInductiveSetIn
    {U w : ZFSet.{u}} (hw : IsInductiveSetIn U w)
    (hnU : forall n : Nat, (n : Ordinal.{u}).toZFSet ∈ U)
    (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ w := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (n : Ordinal.{u}).toZFSet (hnU n) ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hnext

/-- In `L_theta` for `omega < theta`, the least-inductive-set formula denotes
the actual von Neumann `omega`, not merely an internally nonstandard object. -/
theorem satisfiesIn_omegaSetAt_iff
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ LStageZF theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u}) (omegaSetAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  let U : ZFSet.{u} := LStageZF theta
  have htrans : U.IsTransitive := LStageZF_isTransitive theta
  have hemptyU : (∅ : ZFSet.{u}) ∈ U :=
    empty_mem_LStageZF_of_isSuccLimit htheta
  have hsuccU : forall x : ZFSet.{u}, x ∈ U -> insert x x ∈ U :=
    fun x hx => MostowskiCollapse.insert_self_mem_LStageZF_of_isSuccLimit
      htheta hx
  have homegaU : Ordinal.omega0.toZFSet ∈ U :=
    ordinal_toZFSet_mem_LStageZF_of_lt homega
  have hnU : forall k : Nat, (k : Ordinal.{u}).toZFSet ∈ U := by
    intro k
    exact ordinal_toZFSet_mem_LStageZF_of_lt
      ((Ordinal.natCast_lt_omega0 k).trans homega)
  rw [omegaSetAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff,
    satisfiesIn_imp_iff, Model.satisfiesIn_boundedAll_iff,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hInd, hminimal⟩
    have hIndRaw : IsInductiveSetIn U (s i) :=
      (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU i s hs).mp hInd
    have hOmegaFormula :
        SatisfiesIn (U : Set ZFSet.{u})
          (inductiveSetAt (Fin.last n))
          (snoc s Ordinal.omega0.toZFSet) :=
      (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU
        (Fin.last n) (snoc s Ordinal.omega0.toZFSet) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [U] using homegaU
          · simpa [U] using hs k)).mpr (by
            simpa only [snoc_last] using omega_isInductiveSetIn U)
    have hsubsetOmega := hminimal Ordinal.omega0.toZFSet homegaU hOmegaFormula
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact hsubsetOmega z (htrans.mem_trans hz (hs i)) hz
    · intro hz
      rcases Ordinal.mem_toZFSet_iff.mp hz with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_isInductiveSetIn hIndRaw hnU k
  · intro hsi
    constructor
    · apply (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU i s hs).mpr
      simpa only [hsi] using omega_isInductiveSetIn U
    · intro w hwU hwFormula z hzU hzOmega
      have hwInd : IsInductiveSetIn U w := by
        simpa only [snoc_last] using
          (satisfiesIn_inductiveSetAt_iff htrans hemptyU hsuccU
          (Fin.last n) (snoc s w) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa [U] using hwU
            · simpa [U] using hs k)).mp hwFormula
      rw [hsi] at hzOmega
      rcases Ordinal.mem_toZFSet_iff.mp hzOmega with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_isInductiveSetIn hwInd hnU k

/-- Exact `L_theta` semantics of the canonical thirteen-parameter matrix.
The quantifier hypotheses are explicit: all free coordinates must be elements
of the stage in which the formula is evaluated. -/
theorem satisfiesIn_canonicalStageParametersFormula_iff
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (s : Tuple ZFSet.{u} 13)
    (hs : forall i, s i ∈ LStageZF theta) :
    SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula s <->
      s = stageHistoryFixedParametersRaw := by
  simp only [canonicalStageParametersFormula, SatisfiesIn]
  rw [satisfiesIn_emptySetAt_iff (LStageZF_isTransitive theta)
      (0 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (1 : Fin 13) (0 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (4 : Fin 13) (3 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (5 : Fin 13) (4 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (6 : Fin 13) (5 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (7 : Fin 13) (6 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (8 : Fin 13) (7 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (9 : Fin 13) (8 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (10 : Fin 13) (9 : Fin 13) s hs]
  rw [satisfiesIn_successorSetAt_iff (LStageZF_isTransitive theta)
      (11 : Fin 13) (10 : Fin 13) s hs]
  rw [satisfiesIn_omegaSetAt_iff htheta homega (12 : Fin 13) s hs]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12⟩
    let sL : Tuple LCarrier.{u} 13 :=
      fun i => ⟨s i, mem_L_of_mem (hs i) (LStageZF_mem_L theta)⟩
    have hsLFormula :
        FOFormula.Satisfies lCarrierMem
          canonicalStageParametersFormula sL := by
      simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
        satisfies_emptySetAt, satisfies_successorSetAt,
        satisfies_omegaSetAt]
      simpa only [sL, Subtype.ext_iff, successorLCarrier_val,
        emptyLCarrier, omegaLCarrier] using
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12⟩
    have hsLEq : sL = stageHistoryFixedParameters :=
      (satisfies_canonicalStageParametersFormula sL).mp hsLFormula
    funext i
    have hi := congrArg (fun t : Tuple LCarrier.{u} 13 => (t i).1) hsLEq
    simpa only [sL, stageHistoryFixedParametersRaw] using hi
  · intro hsEq
    rw [hsEq]
    have hfixedFormula :
        FOFormula.Satisfies lCarrierMem
          canonicalStageParametersFormula
          (stageHistoryFixedParameters : Tuple LCarrier.{u} 13) :=
      (satisfies_canonicalStageParametersFormula
        stageHistoryFixedParameters).mpr rfl
    simp only [canonicalStageParametersFormula, FOFormula.Satisfies,
      satisfies_emptySetAt, satisfies_successorSetAt,
      satisfies_omegaSetAt] at hfixedFormula
    simpa only [stageHistoryFixedParametersRaw, Subtype.ext_iff,
      successorLCarrier_val, emptyLCarrier, omegaLCarrier] using
      hfixedFormula

/-!
The next definition is the actual sentence used for the Tarski--Vaught
transfer.  It has arity zero: none of the thirteen constants occurs as a free
parameter.  The conversion through Mathlib syntax is only a hygienic way of
binding the complete tuple with `exs`.
-/

/-- A closed, parameter-free existential assertion that the thirteen
canonical evaluator constants exist. -/
def canonicalStageParametersExistFormula : FOFormula 0 :=
  fromBoundedFormula
    ((toBoundedFormula canonicalStageParametersFormula).exs)

/-- Full elementarity pulls every canonical evaluator constant into the
smaller domain.  No reflection-level hypothesis and no canonical constant as
a free formula parameter is used. -/
theorem stageHistoryFixedParameters_mem_of_elementary_limit
    {theta : Ordinal.{u}} {domain : ZFSet.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta)
    (hsubset : domain ⊆ LStageZF theta)
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})) :
    forall i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ domain := by
  let fixed : Tuple ZFSet.{u} 13 := stageHistoryFixedParametersRaw
  have hfixedTheta : forall i, fixed i ∈ LStageZF theta := by
    intro i
    exact stageHistoryFixedParameters_mem_LStageZF_of_omega_lt homega i
  let FixedTheta : Tuple (StageCarrier theta) 13 :=
    fun i => ⟨fixed i, hfixedTheta i⟩
  letI stageStructure :
      FirstOrder.Language.setTheory.Structure (StageCarrier theta) :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
  have hcanonicalTheta :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula fixed :=
    (satisfiesIn_canonicalStageParametersFormula_iff
      htheta homega fixed hfixedTheta).mpr rfl
  have hcanonicalThetaTyped :
      FOFormula.Satisfies
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        canonicalStageParametersFormula FixedTheta := by
    apply (satisfies_stageCarrier_iff_satisfiesIn
      canonicalStageParametersFormula FixedTheta).mpr
    simpa only [FixedTheta, fixed] using hcanonicalTheta
  have hboundedTheta :
      realizes
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        (toBoundedFormula canonicalStageParametersFormula) FixedTheta :=
    (realizes_toBoundedFormula
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
      canonicalStageParametersFormula FixedTheta).mpr
      hcanonicalThetaTyped
  let emptyTheta : Tuple (StageCarrier theta) 0 := fun i => Fin.elim0 i
  have hexBoundedTheta :
      realizes
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        ((toBoundedFormula canonicalStageParametersFormula).exs)
        emptyTheta := by
    change ((toBoundedFormula canonicalStageParametersFormula).exs).Realize
      Empty.elim
    rw [FirstOrder.Language.BoundedFormula.realize_exs]
    exact ⟨FixedTheta, hboundedTheta⟩
  have hclosedThetaTyped :
      FOFormula.Satisfies
        (fun x y : StageCarrier theta => x.1 ∈ y.1)
        canonicalStageParametersExistFormula emptyTheta := by
    exact (realize_fromBoundedFormula
      (fun x y : StageCarrier theta => x.1 ∈ y.1)
      ((toBoundedFormula canonicalStageParametersFormula).exs)
      emptyTheta).mp hexBoundedTheta
  let emptyRaw : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  have hclosedTheta :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersExistFormula emptyRaw := by
    apply (satisfies_stageCarrier_iff_satisfiesIn
      canonicalStageParametersExistFormula emptyTheta).mp
    simpa only [emptyTheta, emptyRaw] using hclosedThetaTyped
  have hclosedDomain :
      SatisfiesIn (domain : Set ZFSet.{u})
        canonicalStageParametersExistFormula emptyRaw :=
    (helem canonicalStageParametersExistFormula emptyRaw
      (fun i => Fin.elim0 i)).mpr hclosedTheta
  let DomainCarrier := ClassCarrier (domain : Set ZFSet.{u})
  letI domainStructure :
      FirstOrder.Language.setTheory.Structure DomainCarrier :=
    FirstOrder.Language.setTheoryStructure
      (fun x y : DomainCarrier => x.1 ∈ y.1)
  let emptyDomain : Tuple DomainCarrier 0 := fun i => Fin.elim0 i
  have hclosedDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        canonicalStageParametersExistFormula emptyDomain := by
    apply (satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) canonicalStageParametersExistFormula
      emptyDomain).mpr
    rw [show (fun i => (emptyDomain i).1) = emptyRaw by
      exact Subsingleton.elim _ _]
    exact hclosedDomain
  have hexBoundedDomain :
      realizes
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        ((toBoundedFormula canonicalStageParametersFormula).exs)
        emptyDomain := by
    exact (realize_fromBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      ((toBoundedFormula canonicalStageParametersFormula).exs)
      emptyDomain).mpr hclosedDomainTyped
  change ((toBoundedFormula canonicalStageParametersFormula).exs).Realize
    Empty.elim at hexBoundedDomain
  rw [FirstOrder.Language.BoundedFormula.realize_exs] at hexBoundedDomain
  rcases hexBoundedDomain with ⟨sDomain, hsDomainBounded⟩
  have hsDomainTyped :
      FOFormula.Satisfies
        (fun x y : DomainCarrier => x.1 ∈ y.1)
        canonicalStageParametersFormula sDomain := by
    exact (realizes_toBoundedFormula
      (fun x y : DomainCarrier => x.1 ∈ y.1)
      canonicalStageParametersFormula sDomain).mp hsDomainBounded
  let sRaw : Tuple ZFSet.{u} 13 := fun i => (sDomain i).1
  have hsDomainRaw :
      SatisfiesIn (domain : Set ZFSet.{u})
        canonicalStageParametersFormula sRaw := by
    exact (satisfies_subtype_iff_satisfiesIn
      (domain : Set ZFSet.{u}) canonicalStageParametersFormula
      sDomain).mp hsDomainTyped
  have hsThetaRaw :
      SatisfiesIn (LStageZF theta : Set ZFSet.{u})
        canonicalStageParametersFormula sRaw :=
    (helem canonicalStageParametersFormula sRaw
      (fun i => (sDomain i).2)).mp hsDomainRaw
  have hsEq : sRaw = stageHistoryFixedParametersRaw :=
    (satisfiesIn_canonicalStageParametersFormula_iff
      htheta homega sRaw (fun i => hsubset (sDomain i).2)).mp hsThetaRaw
  intro i
  have hvalue :
      (sDomain i).1 = (stageHistoryFixedParameters.{u} i).1 := by
    exact congrArg (fun t : Tuple ZFSet.{u} 13 => t i) hsEq
  rw [← hvalue]
  exact (sDomain i).2

end

end Model

end Constructible
