/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StandardCondensation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GCHReduction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCantor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalMostowskiCollapse

/-!
# The condensation-to-GCH bridge

This file isolates the exact use of Condensation in the usual proof of GCH
in `L`.  A cardinal-controlled elementary hull containing a subset `x` of an
internal cardinal `kappa` collapses to a level `L_beta`.  If the hull contains
every member of `kappa`, then the collapse fixes `x`; if the hull internally
injects into `kappa`, then `beta` is below the internal Hartogs successor of
`kappa`.  Consequently `x` belongs to that successor-indexed level.

The construction of the full all-formula Skolem hull and the cardinal bound
on the successor-indexed level are deliberately exposed as interfaces.  No
ambient `ZFSet.card` comparison is used as an internal graph witness.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- Collapse fixes every member of a transitive set included in its domain.
The collapse domain itself need not be transitive. -/
theorem collapse_eq_self_of_mem_of_transitive_subset
    {domain bound : ZFSet.{u}}
    (hboundTransitive : bound.IsTransitive)
    (hboundDomain : bound ⊆ domain) :
    ∀ x : ZFSet.{u}, x ∈ bound → collapse domain x = x := by
  intro x
  refine ZFSet.inductionOn
    (p := fun x => x ∈ bound → collapse domain x = x) x ?_
  intro x ih hxBound
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _hyDomain, hyz⟩
    have hyBound : y ∈ bound :=
      hboundTransitive.mem_trans hyx hxBound
    have hyFixed : collapse domain y = y := ih y hyx hyBound
    have hyEq : y = z := hyFixed.symm.trans hyz
    simpa only [hyEq] using hyx
  · intro hzx
    have hzBound : z ∈ bound :=
      hboundTransitive.mem_trans hzx hxBound
    exact ⟨z, hzx, hboundDomain hzBound, ih z hzx hzBound⟩

/-- If every member of `x` lies in a transitive part of the collapse domain,
then collapse fixes `x` as well.  Membership of `x` in the domain is not
needed for this pointwise statement. -/
theorem collapse_eq_self_of_subset_of_transitive_subset
    {domain bound x : ZFSet.{u}}
    (hboundTransitive : bound.IsTransitive)
    (hboundDomain : bound ⊆ domain)
    (hxBound : x ⊆ bound) :
    collapse domain x = x := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨y, hyx, _hyDomain, hyz⟩
    have hyBound : y ∈ bound := hxBound hyx
    have hyFixed := collapse_eq_self_of_mem_of_transitive_subset
      hboundTransitive hboundDomain y hyBound
    have hyEq : y = z := hyFixed.symm.trans hyz
    simpa only [hyEq] using hyx
  · intro hzx
    have hzBound : z ∈ bound := hxBound hzx
    exact ⟨z, hzx, hboundDomain hzBound,
      collapse_eq_self_of_mem_of_transitive_subset
        hboundTransitive hboundDomain z hzBound⟩

end

end MostowskiCollapse

namespace ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Choosing the ambient reflection level -/

/-- Any two constructible parameters occur together in a condensation
reflection level.  The later Skolem construction starts inside this level. -/
theorem exists_condensationReflectionLevel_containing_pair
    (x y : LCarrier.{u}) :
    ∃ theta : Ordinal.{u},
      IsCondensationReflectionLevel theta ∧
        x.1 ∈ LStageZF theta ∧ y.1 ∈ LStageZF theta := by
  let bound := max
    (stageOf x.1 x.2) (stageOf y.1 y.2)
  rcases exists_condensationReflectionLevel bound with
    ⟨theta, hboundTheta, htheta⟩
  refine ⟨theta, htheta, ?_, ?_⟩
  · exact LStageZF_mono
      ((le_max_left (stageOf x.1 x.2) (stageOf y.1 y.2)).trans
        hboundTheta)
      (mem_LStageZF_stageOf x.1 x.2)
  · exact LStageZF_mono
      ((le_max_right (stageOf x.1 x.2) (stageOf y.1 y.2)).trans
        hboundTheta)
      (mem_LStageZF_stageOf y.1 y.2)

/-! ## Cardinal-controlled hulls -/

/-- The precise hull data consumed by the condensation argument for one
subset `x` of `kappa`.

`bound_subset` makes collapse fix subsets of `kappa`.  `small` is an
internally represented injection, not an ambient cardinal inequality.
`collapseData` records that the collapse range and graph are actual members
of `L`. -/
structure CardinalControlledHull
    (kappa x : LCarrier.{u}) where
  theta : Ordinal.{u}
  domain : LCarrier.{u}
  hull : CondensationHull theta domain.1
  collapseData : InternalizedCollapse domain
  bound_subset : kappa.1 ⊆ domain.1
  element_mem : x.1 ∈ domain.1
  small : Injects LMem domain kappa

namespace CardinalControlledHull

variable {kappa x : LCarrier.{u}}

/-- The ordinal index supplied by Condensation for this hull. -/
noncomputable def collapsedHeight (h : CardinalControlledHull kappa x) :
    Ordinal.{u} :=
  ordinalHeight (range h.domain.1)

/-- The standard Condensation Lemma identifies the external collapse range
with the level indexed by its ordinal height.  The reflection-level data in
`h.hull` supplies the ordinary nonzero-limit and full-elementarity premises;
it is not an additional premise of this theorem. -/
theorem range_eq_LStageZF_collapsedHeight
    (h : CardinalControlledHull kappa x) :
    range h.domain.1 = LStageZF h.collapsedHeight :=
  condensation_of_elementary_isSuccLimit
    h.hull.reflection.1 h.hull.subset_stage
      h.hull.satisfactionAbsolute

/-- The represented collapse range is exactly the level supplied by the
Condensation Lemma. -/
theorem rangeCarrier_eq_stageLCarrier
    (h : CardinalControlledHull kappa x) :
    h.collapseData.rangeCarrier = stageLCarrier h.collapsedHeight := by
  apply Subtype.ext
  exact h.collapseData.range_val.trans h.range_eq_LStageZF_collapsedHeight

/-- The collapse range internally injects into the controlling cardinal. -/
theorem range_injects_cardinal
    (h : CardinalControlledHull kappa x) :
    Injects LMem h.collapseData.rangeCarrier kappa := by
  have hcollapse : Equinumerous LMem
      h.domain h.collapseData.rangeCarrier :=
    h.collapseData.equinumerous h.hull.isExtensional
  exact (hcollapse.symm_lCarrier.injects).trans_lCarrier h.small

/-- The height `beta` of the collapsed level internally injects into
`kappa`. -/
theorem height_injects_cardinal
    (h : CardinalControlledHull kappa x) :
    Injects LMem (ordinalLCarrier h.collapsedHeight) kappa := by
  have hheightRange : Injects LMem
      (ordinalLCarrier h.collapsedHeight)
      h.collapseData.rangeCarrier := by
    apply injects_of_subset_lCarrier
    intro z hz
    rw [h.collapseData.range_val, h.hull.condensation]
    exact (ordinal_stage_invariants h.collapsedHeight).2 hz
  exact hheightRange.trans_lCarrier h.range_injects_cardinal

/-- The height of a cardinal-controlled collapse is below the internal
Hartogs successor. -/
theorem collapsedHeight_lt_internalHartogsOrdinal
    (h : CardinalControlledHull kappa x) :
    h.collapsedHeight < internalHartogsOrdinal kappa := by
  let hartogs := internalHartogsLCarrier kappa
  have hhartogs : IsHartogsNumber LMem kappa hartogs :=
    internalHartogsLCarrier_isHartogsNumber kappa
  by_contra hnot
  have hle : internalHartogsOrdinal kappa ≤ h.collapsedHeight :=
    le_of_not_gt hnot
  have hhartogsHeight : Injects LMem hartogs
      (ordinalLCarrier h.collapsedHeight) := by
    apply injects_of_subset_lCarrier
    intro z hz
    change z.1 ∈ h.collapsedHeight.toZFSet
    apply (Ordinal.toZFSet_subset_toZFSet_iff.mpr hle)
    simpa only [hartogs, internalHartogsLCarrier,
      ordinalLCarrier_val] using hz
  exact hhartogs.2.1
    (hhartogsHeight.trans_lCarrier h.height_injects_cardinal)

/-- A subset of `kappa` contained in the hull is fixed by collapse and hence
belongs to the collapsed level. -/
theorem element_mem_collapsedStage
    (h : CardinalControlledHull kappa x)
    (hkappa : IsCardinal LMem kappa)
    (hx : IsSubsetOf LMem x kappa) :
    x.1 ∈ LStageZF h.collapsedHeight := by
  have hkappaOrdinal : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa.1
  have hxRaw : x.1 ⊆ kappa.1 := by
    intro z hz
    let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz x.2⟩
    exact hx zL hz
  have hfixed : collapse h.domain.1 x.1 = x.1 :=
    collapse_eq_self_of_subset_of_transitive_subset
      hkappaOrdinal.isTransitive h.bound_subset hxRaw
  change x.1 ∈ LStageZF h.collapsedHeight
  rw [← h.range_eq_LStageZF_collapsedHeight]
  exact mem_range_iff.mpr ⟨x.1, h.element_mem, hfixed⟩

/-- The subset captured by the hull already occurs before the Hartogs-indexed
constructible level. -/
theorem element_mem_internalHartogsStage
    (h : CardinalControlledHull kappa x)
    (hkappa : IsCardinal LMem kappa)
    (hx : IsSubsetOf LMem x kappa) :
    x.1 ∈ LStageZF (internalHartogsOrdinal kappa) := by
  exact LStageZF_mono
    h.collapsedHeight_lt_internalHartogsOrdinal.le
    (h.element_mem_collapsedStage hkappa hx)

end CardinalControlledHull

/-- Every constructible subset of `kappa` admits a fully elementary,
cardinality-controlled, internally collapsible hull.  Constructing this
object is the remaining all-formula Skolem-hull obligation. -/
def HasCardinalControlledHulls (kappa : LCarrier.{u}) : Prop :=
  ∀ x : LCarrier.{u}, IsSubsetOf LMem x kappa →
    Nonempty (CardinalControlledHull kappa x)

/-- Full controlled hulls put the entire internal powerset below the
Hartogs-indexed constructible stage. -/
theorem powerSet_subset_internalHartogsStage
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa) :
    ∀ x : LCarrier.{u}, x.1 ∈ power.1 →
      x.1 ∈ LStageZF (internalHartogsOrdinal kappa) := by
  intro x hxPower
  have hxSubset : IsSubsetOf LMem x kappa :=
    (hpower x).mp hxPower
  rcases hhulls x hxSubset with ⟨hull⟩
  exact hull.element_mem_internalHartogsStage hkappa hxSubset

/-- The preceding containment is represented by an actual constructible
identity graph. -/
theorem powerSet_injects_internalHartogsStage
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa) :
    Injects LMem power
      (stageLCarrier (internalHartogsOrdinal kappa)) := by
  apply injects_of_subset_lCarrier
  exact powerSet_subset_internalHartogsStage hkappa hpower hhulls

/-! ## The two remaining cardinal interfaces -/

/-- The internal version of `|L_(kappa^+)| <= kappa^+`.  Its proof is the
transfinite cardinal-union argument using the canonical stage order. -/
def HartogsStageBound (kappa : LCarrier.{u}) : Prop :=
  Injects LMem (stageLCarrier (internalHartogsOrdinal kappa))
    (internalHartogsLCarrier kappa)

/-- Every set is internally equinumerous with an internal cardinal.  This is
the cardinal-representative consequence of the internal well-ordering
theorem. -/
def HasInternalCardinalRepresentatives : Prop :=
  ∀ a : LCarrier.{u}, ∃ cardinal : LCarrier.{u},
    IsCardinal LMem cardinal ∧ Equinumerous LMem a cardinal

/-- Condensation plus the stage bound gives the GCH upper injection. -/
theorem powerSet_injects_internalHartogs
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa)
    (hstage : HartogsStageBound kappa) :
    Injects LMem power (internalHartogsLCarrier kappa) :=
  (powerSet_injects_internalHartogsStage hkappa hpower hhulls).trans_lCarrier
    hstage

/-- Internal cardinal representatives and Cantor's theorem give the reverse
injection from `kappa^+` into the powerset. -/
theorem internalHartogs_injects_powerSet_of_cardinalRepresentatives
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power) :
    Injects LMem (internalHartogsLCarrier kappa) power := by
  rcases hrepresentatives power with
    ⟨cardinal, hcardinal, hpowerCardinal⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal kappa hkappa.1 with
    ⟨alpha, hkappaEq⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      cardinal hcardinal.1 with
    ⟨gamma, hcardinalEq⟩
  subst kappa
  subst cardinal
  have hkappaPower : Injects LMem (ordinalLCarrier alpha) power :=
    injects_powerSet_lCarrier hpower
  have hpowerGamma : Injects LMem power (ordinalLCarrier gamma) :=
    hpowerCardinal.injects
  have halphaGamma : alpha < gamma := by
    have hnotGammaAlpha : ¬ gamma < alpha := by
      intro hgammaAlpha
      have hforbidden : Injects LMem
          (ordinalLCarrier alpha) (ordinalLCarrier gamma) :=
        hkappaPower.trans_lCarrier hpowerGamma
      exact (hkappa.not_injects_of_mem_lCarrier
        ((ordinalLCarrier_mem_ordinalLCarrier_iff alpha gamma).mpr
          hgammaAlpha)
        internalInjectionAntisymm_lCarrier) hforbidden
    have halphaLeGamma : alpha ≤ gamma := le_of_not_gt hnotGammaAlpha
    exact lt_of_le_of_ne halphaLeGamma (by
      intro halphaEq
      subst gamma
      exact not_equinumerous_powerSet_lCarrier hpower
        hpowerCardinal.symm_lCarrier)
  let delta := internalHartogsOrdinal (ordinalLCarrier alpha)
  have hdeltaLeGamma : delta ≤ gamma := by
    by_contra hnot
    have hgammaDelta : gamma < delta := lt_of_not_ge hnot
    have hsuccessor := internalHartogsLCarrier_isSuccessorCardinal
      (ordinalLCarrier alpha) hkappa
    apply hsuccessor.2.2.2
    refine ⟨ordinalLCarrier gamma, hcardinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff gamma alpha).mpr
        halphaGamma, ?_⟩
    simpa only [internalHartogsLCarrier, delta] using
      (ordinalLCarrier_mem_ordinalLCarrier_iff delta gamma).mpr
        hgammaDelta
  have hhartogsGamma : Injects LMem
      (internalHartogsLCarrier (ordinalLCarrier alpha))
      (ordinalLCarrier gamma) := by
    apply injects_of_subset_lCarrier
    intro z hz
    apply (Ordinal.toZFSet_subset_toZFSet_iff.mpr hdeltaLeGamma)
    simpa only [delta, internalHartogsLCarrier,
      ordinalLCarrier_val] using hz
  exact hhartogsGamma.trans_lCarrier
    hpowerCardinal.symm_lCarrier.injects

/-- The exact condensation route to the powerset/Hartogs equinumerosity
required by `GCHReduction`. -/
theorem powerSet_equinumerous_internalHartogs_of_condensation
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    {kappa power : LCarrier.{u}}
    (hkappa : IsCardinal LMem kappa)
    (hpower : IsPowerSetOf LMem kappa power)
    (hhulls : HasCardinalControlledHulls kappa)
    (hstage : HartogsStageBound kappa) :
    Equinumerous LMem power (internalHartogsLCarrier kappa) := by
  exact injects_antisymm_lCarrier
    (powerSet_injects_internalHartogs hkappa hpower hhulls hstage)
    (internalHartogs_injects_powerSet_of_cardinalRepresentatives
      hrepresentatives hkappa hpower)

/-- Once the Skolem-hull and stage-cardinality interfaces are discharged for
all internal infinite cardinals, the existing reduction yields GCH in `L`. -/
theorem modelsGCH_lCarrier_of_condensation_interfaces
    (hrepresentatives : HasInternalCardinalRepresentatives.{u})
    (hhulls : ∀ kappa : LCarrier.{u},
      IsCardinal LMem kappa →
      IsSubsetOf LMem omegaLCarrier kappa →
      HasCardinalControlledHulls kappa)
    (hstage : ∀ kappa : LCarrier.{u},
      IsCardinal LMem kappa →
      IsSubsetOf LMem omegaLCarrier kappa →
      HartogsStageBound kappa) :
    ModelsGCH (A := LCarrier.{u}) LMem := by
  apply modelsGCH_lCarrier_of_powerSet_equinumerous_hartogs
  intro kappa power hkappa hinfinite hpower
  exact powerSet_equinumerous_internalHartogs_of_condensation
    hrepresentatives hkappa hpower
      (hhulls kappa hkappa hinfinite)
      (hstage kappa hkappa hinfinite)

end

end ContinuumFormula

end Constructible
