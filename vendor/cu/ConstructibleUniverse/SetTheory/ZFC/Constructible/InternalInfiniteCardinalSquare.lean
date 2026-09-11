/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrdinalProductOrder
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOmegaProductAbsorption
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalProductInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.HartogsLimit
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GCHReduction

/-!
# Squares of internal infinite cardinals

This file completes the standard maximum-lexicographic proof that an infinite
initial ordinal absorbs its square.  The induction is taken over the ambient
presentation of the ordinal, but every injection used in the conclusion and
in every induction step is witnessed by an actual Kuratowski graph in `L`.

For a point of the maximum-lexicographic order on `kappa x kappa`, its strict
initial segment lies in `bound x bound` for some `bound < kappa`.  In the
uncountable step, an internal cardinal representative `lambda` of
`bound union omega` is still below `kappa`; the induction hypothesis absorbs
`lambda x lambda`.  Initiality of `kappa` then prevents the order type of the
whole square from exceeding `kappa`.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

private theorem omegaLCarrier_eq_ordinalLCarrier :
    (omegaLCarrier : LCarrier.{u}) = ordinalLCarrier Ordinal.omega0 := by
  apply Subtype.ext
  rfl

private theorem ordinal_le_of_subset_lCarrier
    {alpha beta : Ordinal.{u}}
    (hsubset : IsSubsetOf LMem
      (ordinalLCarrier alpha) (ordinalLCarrier beta)) :
    alpha <= beta := by
  apply Ordinal.toZFSet_subset_toZFSet_iff.mp
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, Constructible.mem_L_of_mem hz (ordinalLCarrier alpha).2⟩
  exact hsubset zL hz

private theorem ordinal_subset_lCarrier_of_le
    {alpha beta : Ordinal.{u}} (h : alpha <= beta) :
    IsSubsetOf LMem (ordinalLCarrier alpha) (ordinalLCarrier beta) := by
  intro z hz
  exact Ordinal.toZFSet_monotone h hz

private theorem ordinal_isSuccLimit_of_cardinal_and_omega_lt
    (alpha : Ordinal.{u})
    (hcardinal : IsCardinal LMem (ordinalLCarrier alpha))
    (homega : Ordinal.omega0 < alpha) :
    Order.IsSuccLimit alpha := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit alpha with
    hzero | ⟨beta, hsuccessor⟩ | hlimit
  · rw [hzero] at homega
    exact (not_lt_of_ge (bot_le : (0 : Ordinal.{u}) <= Ordinal.omega0)
      homega).elim
  · have homegaBeta : Ordinal.omega0 <= beta := by
      rw [← Order.lt_succ_iff, hsuccessor]
      exact homega
    have homegaSubset : IsSubsetOf LMem
        (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier beta) := by
      rw [omegaLCarrier_eq_ordinalLCarrier]
      exact ordinal_subset_lCarrier_of_le homegaBeta
    have hbetaSelf : Injects LMem
        (ordinalLCarrier beta) (ordinalLCarrier beta) :=
      injects_of_subset_lCarrier (fun _ hz => hz)
    have hsuccessorBeta : Injects LMem
        (ordinalLCarrier (Order.succ beta)) (ordinalLCarrier beta) :=
      injects_successorOrdinal_of_omega_subset_lCarrier
        homegaSubset hbetaSelf
    have halphaBeta : Injects LMem
        (ordinalLCarrier alpha) (ordinalLCarrier beta) := by
      rw [← hsuccessor]
      exact hsuccessorBeta
    have hbetaMem :
        (ordinalLCarrier beta).1 ∈ (ordinalLCarrier alpha).1 := by
      apply (ordinalLCarrier_mem_ordinalLCarrier_iff alpha beta).mpr
      rw [← hsuccessor]
      exact Order.lt_succ beta
    exact ((hcardinal.not_injects_of_mem_lCarrier hbetaMem
      internalInjectionAntisymm_lCarrier) halphaBeta).elim
  · exact hlimit

private theorem exists_smaller_cardinal_square_bound
    (alpha : Ordinal.{u})
    (hcardinal : IsCardinal LMem (ordinalLCarrier alpha))
    (homegaLt : Ordinal.omega0 < alpha)
    (hlimit : Order.IsSuccLimit alpha)
    (ih : forall beta : Ordinal.{u}, beta < alpha ->
      IsCardinal LMem (ordinalLCarrier beta) ->
      IsSubsetOf LMem (omegaLCarrier : LCarrier.{u})
        (ordinalLCarrier beta) ->
      Injects LMem
        (prodLCarrier (ordinalLCarrier beta) (ordinalLCarrier beta))
        (ordinalLCarrier beta))
    {bound : LCarrier.{u}}
    (hbound : bound.1 ∈ (ordinalLCarrier alpha).1) :
    exists lambda : LCarrier.{u},
      lambda.1 ∈ (ordinalLCarrier alpha).1 /\
        IsCardinal LMem lambda /\
          Injects LMem (prodLCarrier bound bound) lambda := by
  rcases exists_eq_ordinalLCarrier_of_mem hbound with
    ⟨beta, hbeta, rfl⟩
  let gamma : Ordinal.{u} := max beta Ordinal.omega0
  have hgamma : gamma < alpha := by
    exact max_lt hbeta homegaLt
  have hupper : Order.succ gamma < alpha := hlimit.succ_lt hgamma
  let upper : LCarrier.{u} := ordinalLCarrier (Order.succ gamma)
  have hupperMem : upper.1 ∈ (ordinalLCarrier alpha).1 := by
    exact (ordinalLCarrier_mem_ordinalLCarrier_iff
      alpha (Order.succ gamma)).mpr hupper
  let joined : LCarrier.{u} :=
    unionLCarrier (ordinalLCarrier beta) omegaLCarrier
  have hjoinedUpper : forall z : LCarrier.{u},
      z.1 ∈ joined.1 -> z.1 ∈ upper.1 := by
    intro z hz
    rcases (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mp hz with hz | hz
    · exact Ordinal.toZFSet_monotone
        (le_trans (le_max_left beta Ordinal.omega0)
          (Order.le_succ gamma)) hz
    · exact Ordinal.toZFSet_monotone
        (le_trans (le_max_right beta Ordinal.omega0)
          (Order.le_succ gamma)) hz
  rcases hasInternalCardinalRepresentatives_lCarrier joined with
    ⟨lambda, hlambdaCardinal, hjoinedLambda⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      lambda hlambdaCardinal.1 with
    ⟨mu, hlambdaEq⟩
  subst lambda
  have hmuAlpha : mu < alpha := by
    by_contra hnot
    have halphaMu : alpha <= mu := le_of_not_gt hnot
    have halphaToMu : Injects LMem
        (ordinalLCarrier alpha) (ordinalLCarrier mu) :=
      injects_of_subset_lCarrier
        (ordinal_subset_lCarrier_of_le halphaMu)
    have hmuToJoined : Injects LMem
        (ordinalLCarrier mu) joined :=
      hjoinedLambda.symm_lCarrier.injects
    have hjoinedToUpper : Injects LMem joined upper :=
      injects_of_subset_lCarrier hjoinedUpper
    have halphaToUpper :=
      (halphaToMu.trans_lCarrier hmuToJoined).trans_lCarrier
        hjoinedToUpper
    exact (hcardinal.not_injects_of_mem_lCarrier hupperMem
      internalInjectionAntisymm_lCarrier) halphaToUpper
  have homegaToJoined : Injects LMem
      (omegaLCarrier : LCarrier.{u}) joined := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mpr (Or.inr hz)
  have homegaMuLe : Ordinal.omega0 <= mu := by
    by_contra hnot
    have hmuOmega : mu < Ordinal.omega0 := lt_of_not_ge hnot
    have hmuMemOmega :
        (ordinalLCarrier mu).1 ∈ omegaLCarrier.1 := by
      exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        Ordinal.omega0 mu).mpr hmuOmega
    have homegaToMu : Injects LMem
        (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier mu) :=
      homegaToJoined.trans_lCarrier hjoinedLambda.injects
    exact (omegaLCarrier_isCardinal.not_injects_of_mem_lCarrier
      hmuMemOmega internalInjectionAntisymm_lCarrier) homegaToMu
  have homegaMu : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) (ordinalLCarrier mu) := by
    rw [omegaLCarrier_eq_ordinalLCarrier]
    exact ordinal_subset_lCarrier_of_le homegaMuLe
  have hmuSquare : Injects LMem
      (prodLCarrier (ordinalLCarrier mu) (ordinalLCarrier mu))
      (ordinalLCarrier mu) :=
    ih mu hmuAlpha hlambdaCardinal homegaMu
  have hboundToJoined : Injects LMem
      (ordinalLCarrier beta) joined := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact (mem_unionLCarrier_iff
      (ordinalLCarrier beta) omegaLCarrier z).mpr (Or.inl hz)
  have hboundToMu : Injects LMem
      (ordinalLCarrier beta) (ordinalLCarrier mu) :=
    hboundToJoined.trans_lCarrier hjoinedLambda.injects
  have hboundSquareToMuSquare : Injects LMem
      (prodLCarrier (ordinalLCarrier beta) (ordinalLCarrier beta))
      (prodLCarrier (ordinalLCarrier mu) (ordinalLCarrier mu)) :=
    injects_prod_of_injects_lCarrier hboundToMu hboundToMu
  exact ⟨ordinalLCarrier mu,
    (ordinalLCarrier_mem_ordinalLCarrier_iff alpha mu).mpr hmuAlpha,
    hlambdaCardinal,
    hboundSquareToMuSquare.trans_lCarrier hmuSquare⟩

private theorem injects_infiniteCardinalSquare_ordinalLCarrier :
    forall alpha : Ordinal.{u},
      IsCardinal LMem (ordinalLCarrier alpha) ->
      IsSubsetOf LMem (omegaLCarrier : LCarrier.{u})
        (ordinalLCarrier alpha) ->
      Injects LMem
        (prodLCarrier (ordinalLCarrier alpha) (ordinalLCarrier alpha))
        (ordinalLCarrier alpha) := by
  intro alpha
  apply (IsWellFounded.wf :
    WellFounded ((· < ·) : Ordinal.{u} -> Ordinal.{u} -> Prop)).induction
      alpha
  intro alpha ih hcardinal homega
  by_cases halphaOmega : alpha = Ordinal.omega0
  · subst alpha
    simpa only [omegaLCarrier_eq_ordinalLCarrier] using
      injects_omegaProduct_omega_lCarrier
  · have homegaLe : Ordinal.omega0 <= alpha := by
      apply ordinal_le_of_subset_lCarrier
      simpa only [omegaLCarrier_eq_ordinalLCarrier] using homega
    have homegaNe : Not (Ordinal.omega0 = alpha) := by
      intro h
      exact halphaOmega h.symm
    have homegaLt : Ordinal.omega0 < alpha :=
      lt_of_le_of_ne homegaLe homegaNe
    have hlimit : Order.IsSuccLimit alpha :=
      ordinal_isSuccLimit_of_cardinal_and_omega_lt
        alpha hcardinal homegaLt
    let relation := ordinalPairMaximumLexGraph (ordinalLCarrier alpha)
    let domain := prodLCarrier
      (ordinalLCarrier alpha) (ordinalLCarrier alpha)
    let hwell : InternallyWellOrders relation domain :=
      ordinalPairMaximumLexGraph_internallyWellOrders
        (ordinalLCarrier alpha) hcardinal.1
    let tau := canonicalOrderType relation domain hwell
    have hsuccessor : forall bound : LCarrier.{u},
        bound.1 ∈ (ordinalLCarrier alpha).1 ->
          (successorLCarrier bound).1 ∈ (ordinalLCarrier alpha).1 := by
      intro bound hbound
      rcases exists_eq_ordinalLCarrier_of_mem hbound with
        ⟨beta, hbeta, rfl⟩
      rw [successorLCarrier_ordinalLCarrier]
      exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        alpha (Order.succ beta)).mpr (hlimit.succ_lt hbeta)
    have htauLe : tau <= alpha := by
      by_contra hnot
      have halphaTau : alpha < tau := lt_of_not_ge hnot
      rcases exists_member_canonicalOrderType_eq_of_lt
          relation domain hwell halphaTau with
        ⟨point, hpoint, hpointType⟩
      rcases canonicalMemberOrderType_injects_smaller_ordinalSquare
          hcardinal.1 hsuccessor hpoint with
        ⟨bound, hbound, htypeBound⟩
      rcases exists_smaller_cardinal_square_bound
          alpha hcardinal homegaLt hlimit ih hbound with
        ⟨lambda, hlambda, _hlambdaCardinal, hboundLambda⟩
      have halphaBound : Injects LMem
          (ordinalLCarrier alpha) (prodLCarrier bound bound) := by
        simpa only [relation, domain, hwell,
          canonicalMemberOrderTypeLCarrier, hpointType] using htypeBound
      have halphaLambda :=
        halphaBound.trans_lCarrier hboundLambda
      exact (hcardinal.not_injects_of_mem_lCarrier hlambda
        internalInjectionAntisymm_lCarrier) halphaLambda
    let witness := canonicalInternalOrderTypeWitness relation domain hwell
    rcases internalEquinumerous_ordinal_of_orderTypeWitness witness with
      ⟨graph, hgraph⟩
    have hdomainTau : Equinumerous LMem domain (ordinalLCarrier tau) := by
      simpa only [witness, canonicalInternalOrderTypeWitness, tau] using
        (show Equinumerous LMem domain witness.ordinal from ⟨graph, hgraph⟩)
    have htauAlpha : Injects LMem
        (ordinalLCarrier tau) (ordinalLCarrier alpha) :=
      injects_of_subset_lCarrier
        (ordinal_subset_lCarrier_of_le htauLe)
    exact hdomainTau.injects.trans_lCarrier htauAlpha

/-- Every internally infinite initial ordinal has an internally represented
injection from its Cartesian square into itself. -/
theorem injects_infiniteCardinalSquare_lCarrier
    {kappa : LCarrier.{u}}
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem (prodLCarrier kappa kappa) kappa := by
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      kappa hcardinal.1 with
    ⟨alpha, rfl⟩
  exact injects_infiniteCardinalSquare_ordinalLCarrier
    alpha hcardinal homega

/-- If `kappa` is internally infinite, its Hartogs cardinal absorbs
`Hartogs(kappa) x kappa`. -/
theorem injects_internalHartogsProduct_internalHartogs_lCarrier
    (kappa : LCarrier.{u})
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem
      (prodLCarrier (internalHartogsLCarrier kappa) kappa)
      (internalHartogsLCarrier kappa) := by
  let hartogs := internalHartogsLCarrier kappa
  have hhartogsCardinal : IsCardinal LMem hartogs :=
    internalHartogsLCarrier_isCardinal kappa
  have hkappaHartogs : kappa.1 ∈ hartogs.1 :=
    (internalHartogsLCarrier_isHartogsNumber kappa).base_mem_lCarrier
      hcardinal
  have homegaHartogs : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) hartogs := by
    intro z hz
    exact hhartogsCardinal.1.1 kappa hkappaHartogs z (homega z hz)
  have hhartogsSquare : Injects LMem
      (prodLCarrier hartogs hartogs) hartogs :=
    injects_infiniteCardinalSquare_lCarrier
      hhartogsCardinal homegaHartogs
  have hhartogsSelf : Injects LMem hartogs hartogs :=
    injects_of_subset_lCarrier (fun _ hz => hz)
  have hkappaToHartogs : Injects LMem kappa hartogs := by
    apply injects_of_subset_lCarrier
    intro z hz
    exact hhartogsCardinal.1.1 kappa hkappaHartogs z hz
  exact (injects_prod_of_injects_lCarrier
    hhartogsSelf hkappaToHartogs).trans_lCarrier hhartogsSquare

end

end Constructible.ContinuumFormula
