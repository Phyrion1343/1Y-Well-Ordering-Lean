/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationCore
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ContinuumHypothesis
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.MostowskiElementarity

/-!
# Ordinals through the Mostowski collapse

This file records the order-theoretic part of constructible condensation.
Restricting membership to an arbitrary domain and collapsing an ambient von
Neumann ordinal still produces a von Neumann ordinal.  If the ordinal itself
belongs to the domain, collapse also commutes with ordinal successor.

The final part packages these structural facts for the three hypotheses used
by `CondensationCore`.  Full satisfaction absoluteness is used only to reflect
the assertion that a preimage is an ordinal; no external cardinal or choice
argument occurs here.
-/

@[expose] public section

open Set
open Constructible.ContinuumFormula

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

/-- The restricted collapse of an ambient ordinal is transitive.  No
extensionality or closure assumption on the restricting domain is needed. -/
theorem collapse_isTransitive_of_isOrdinal {domain x : ZFSet.{u}}
    (hx : x.IsOrdinal) :
    (collapse domain x).IsTransitive := by
  intro z hz w hw
  rcases mem_collapse_iff.mp hz with ⟨y, hyx, hydomain, rfl⟩
  rcases mem_collapse_iff.mp hw with ⟨v, hvy, hvdomain, rfl⟩
  exact mem_collapse_iff.mpr
    ⟨v, hx.mem_trans hvy hyx, hvdomain, rfl⟩

/-- Restricting an ordinal to any collection of predecessors and taking its
Mostowski collapse again gives a von Neumann ordinal. -/
theorem collapse_isOrdinal_of_isOrdinal {domain x : ZFSet.{u}}
    (hx : x.IsOrdinal) :
    (collapse domain x).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  refine ⟨collapse_isTransitive_of_isOrdinal hx, ?_⟩
  intro z hz
  rcases mem_collapse_iff.mp hz with ⟨y, hyx, _hydomain, rfl⟩
  exact collapse_isTransitive_of_isOrdinal (hx.mem hyx)

/-- The ordinal represented by the restricted collapse of `alpha`. -/
noncomputable def collapseOrdinal (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  (collapse domain alpha.toZFSet).rank

/-- The collapse of an ordinal code is the code of `collapseOrdinal`. -/
@[simp]
theorem collapseOrdinal_toZFSet (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) :
    (collapseOrdinal domain alpha).toZFSet =
      collapse domain alpha.toZFSet := by
  exact (collapse_isOrdinal_of_isOrdinal
    (ZFSet.isOrdinal_toZFSet alpha)).toZFSet_rank_eq

/-- Collapse commutes with adjoining a domain element to itself.  This is the
set-theoretic operation underlying ordinal successor. -/
theorem collapse_insert_self {domain x : ZFSet.{u}}
    (hxdomain : x ∈ domain) :
    collapse domain (insert x x) =
      insert (collapse domain x) (collapse domain x) := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  simp only [ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨y, hy, hydomain, rfl⟩
    rcases hy with rfl | hyx
    · exact Or.inl rfl
    · exact Or.inr (mem_collapse_iff.mpr
        ⟨y, hyx, hydomain, rfl⟩)
  · intro hz
    rcases hz with rfl | hz
    · exact ⟨x, Or.inl rfl, hxdomain, rfl⟩
    · rcases mem_collapse_iff.mp hz with
        ⟨y, hyx, hydomain, rfl⟩
      exact ⟨y, Or.inr hyx, hydomain, rfl⟩

/-- If an ordinal belongs to the restricting domain, collapse commutes with
its von Neumann successor. -/
theorem collapse_toZFSet_succ {domain : ZFSet.{u}}
    {alpha : Ordinal.{u}} (halpha : alpha.toZFSet ∈ domain) :
    collapse domain (Order.succ alpha).toZFSet =
      (Order.succ (collapseOrdinal domain alpha)).toZFSet := by
  calc
    collapse domain (Order.succ alpha).toZFSet =
        collapse domain (insert alpha.toZFSet alpha.toZFSet) := by
      rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
    _ = insert (collapse domain alpha.toZFSet)
        (collapse domain alpha.toZFSet) := collapse_insert_self halpha
    _ = insert (collapseOrdinal domain alpha).toZFSet
        (collapseOrdinal domain alpha).toZFSet := by
      rw [collapseOrdinal_toZFSet]
    _ = ((collapseOrdinal domain alpha) + 1).toZFSet := by
      rw [Ordinal.toZFSet_add_one]
    _ = (Order.succ (collapseOrdinal domain alpha)).toZFSet := by
      rw [Order.succ_eq_add_one]

/-- Ordinal-valued formulation of `collapse_toZFSet_succ`. -/
theorem collapseOrdinal_succ {domain : ZFSet.{u}}
    {alpha : Ordinal.{u}} (halpha : alpha.toZFSet ∈ domain) :
    collapseOrdinal domain (Order.succ alpha) =
      Order.succ (collapseOrdinal domain alpha) := by
  apply Ordinal.toZFSet_injective
  rw [collapseOrdinal_toZFSet, collapse_toZFSet_succ halpha]

/-- On domain ordinals, extensionality makes `collapseOrdinal` preserve and
reflect strict order. -/
theorem collapseOrdinal_lt_iff {domain : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    {alpha beta : Ordinal.{u}}
    (halpha : alpha.toZFSet ∈ domain)
    (hbeta : beta.toZFSet ∈ domain) :
    collapseOrdinal domain alpha < collapseOrdinal domain beta ↔
      alpha < beta := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff,
    collapseOrdinal_toZFSet, collapseOrdinal_toZFSet,
    collapse_mem_collapse_iff hextensional halpha hbeta,
    Ordinal.toZFSet_mem_toZFSet_iff]

/-! ## Ordinal reflection through full elementarity -/

/-- Raw restricted satisfaction of the ordinal formula in a transitive set
has its ambient von Neumann meaning. -/
theorem satisfiesIn_isOrdinal_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {x : ZFSet.{u}}
    (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        OrdinalFormula.isOrdinal ![x] ↔ x.IsOrdinal := by
  let xU : ZFCarrier U := ⟨x, hxU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u}) OrdinalFormula.isOrdinal ![xU]
  have hsemantic := OrdinalFormula.satisfies_isOrdinal htransitive xU
  have hvalues : (fun i => (![(xU : ZFCarrier U)] i).1) = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hvalues] at hbridge
  exact hbridge.symm.trans hsemantic

/-- Full elementarity identifies ambient ordinals in the source hull with
ambient ordinals in its transitive collapse. -/
theorem isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    {x : ZFSet.{u}} (hxdomain : x ∈ domain) :
    x.IsOrdinal ↔ (collapse domain x).IsOrdinal := by
  let sx : Tuple {y : ZFSet.{u} // y ∈ domain} 1 :=
    ![⟨x, hxdomain⟩]
  have hcollapse := satisfiesIn_collapse_iff hextensional
    OrdinalFormula.isOrdinal sx
  have hsourceValues : (fun i => (sx i).1) = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have htargetValues :
      (fun i => collapse domain (sx i).1) =
        ![collapse domain x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hsourceValues, htargetValues] at hcollapse
  have hparams : ∀ i, ![x] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hxdomain
  have habs := habsolute OrdinalFormula.isOrdinal ![x] hparams
  have hbigSem := satisfiesIn_isOrdinal_iff hbigTransitive
    (hsubset hxdomain)
  have hrangeSem := satisfiesIn_isOrdinal_iff
    (range_isTransitive domain)
    (mem_range_iff.mpr ⟨x, hxdomain, rfl⟩)
  exact hbigSem.symm.trans
    (habs.symm.trans (hcollapse.trans hrangeSem))

/-- A source-domain closure assumption stated directly in terms of ambient
von Neumann successor. -/
def SourceOrdinalSuccessorClosed (domain : ZFSet.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x.IsOrdinal → insert x x ∈ domain

/-- The one-parameter formula asserting that the von Neumann successor of
the parameter exists. -/
def successorExistsFormula : FOFormula 1 :=
  .ex (successorSetAt (Fin.last 1) (0 : Fin 2))

/-- In a transitive carrier, the generic successor-set formula has its
ambient set-theoretic meaning. -/
theorem satisfiesIn_successorSetAt_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {x y : ZFSet.{u}}
    (hxU : x ∈ U) (hyU : y ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![x, y] ↔
      y = insert x x := by
  let xU : ZFCarrier U := ⟨x, hxU⟩
  let yU : ZFCarrier U := ⟨y, hyU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u})
    (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![xU, yU]
  have hvalues :
      (fun i => (![(xU : ZFCarrier U), yU] i).1) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hvalues] at hbridge
  have hsemantic := satisfies_successorSetAt
    (fun a b : ZFCarrier U => a.1 ∈ b.1)
    (1 : Fin 2) (0 : Fin 2) ![xU, yU]
  have hmeaning :
      IsSuccessorSetOf
          (fun a b : ZFCarrier U => a.1 ∈ b.1) yU xU ↔
        y = insert x x := by
    constructor
    · intro h
      apply ZFSet.ext
      intro z
      constructor
      · intro hzy
        have hzU : z ∈ U := htransitive.mem_trans hzy hyU
        have hz : z ∈ y ↔ z ∈ x ∨ z = x := by
          simpa only [xU, yU, Subtype.ext_iff] using h ⟨z, hzU⟩
        exact ZFSet.mem_insert_iff.mpr (Or.comm.mp (hz.mp hzy))
      · intro hzsucc
        rcases ZFSet.mem_insert_iff.mp hzsucc with hzx | hzx
        · subst z
          have hz : x ∈ y ↔ x ∈ x ∨ x = x := by
            simpa only [xU, yU, Subtype.ext_iff] using h xU
          exact hz.mpr (Or.inr rfl)
        · have hzU : z ∈ U := htransitive.mem_trans hzx hxU
          have hz : z ∈ y ↔ z ∈ x ∨ z = x := by
            simpa only [xU, yU, Subtype.ext_iff] using h ⟨z, hzU⟩
          exact hz.mpr (Or.inl hzx)
    · intro hyEq
      subst y
      intro z
      simp only [xU, yU, Subtype.ext_iff]
      rw [ZFSet.mem_insert_iff, or_comm]
  exact hbridge.symm.trans (hsemantic.trans hmeaning)

/-- The von Neumann successor operation on well-founded sets is injective. -/
theorem insert_self_injective :
    Function.Injective (fun x : ZFSet.{u} => insert x x) := by
  intro x y hxy
  change insert x x = insert y y at hxy
  have hx : x ∈ insert y y := by
    rw [← hxy]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  have hy : y ∈ insert x x := by
    rw [hxy]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases ZFSet.mem_insert_iff.mp hx with h | h
  · exact h
  · rcases ZFSet.mem_insert_iff.mp hy with h' | h'
    · exact h'.symm
    · exact (ZFSet.mem_wf.asymmetric x y h h').elim

/-- Swapped-coordinate form of `satisfiesIn_successorSetAt_iff`. -/
theorem satisfiesIn_successorSetAt_swap_iff {U : ZFSet.{u}}
    (htransitive : U.IsTransitive) {successor x : ZFSet.{u}}
    (hsuccessorU : successor ∈ U) (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] ↔
      successor = insert x x := by
  let successorU : ZFCarrier U := ⟨successor, hsuccessorU⟩
  let xU : ZFCarrier U := ⟨x, hxU⟩
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (U : Set ZFSet.{u})
    (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successorU, xU]
  have hvalues :
      (fun i => (![(successorU : ZFCarrier U), xU] i).1) =
        ![successor, x] := by
    funext i
    fin_cases i <;> rfl
  rw [hvalues] at hbridge
  have hsemantic := satisfies_successorSetAt
    (fun a b : ZFCarrier U => a.1 ∈ b.1)
    (0 : Fin 2) (1 : Fin 2) ![successorU, xU]
  have hmeaning :
      IsSuccessorSetOf
          (fun a b : ZFCarrier U => a.1 ∈ b.1) successorU xU ↔
        successor = insert x x := by
    constructor
    · intro h
      apply ZFSet.ext
      intro z
      constructor
      · intro hzSuccessor
        have hzU : z ∈ U :=
          htransitive.mem_trans hzSuccessor hsuccessorU
        have hz : z ∈ successor ↔ z ∈ x ∨ z = x := by
          simpa only [successorU, xU, Subtype.ext_iff] using
            h ⟨z, hzU⟩
        exact ZFSet.mem_insert_iff.mpr
          (Or.comm.mp (hz.mp hzSuccessor))
      · intro hzSucc
        rcases ZFSet.mem_insert_iff.mp hzSucc with hzx | hzx
        · subst z
          have hz : x ∈ successor ↔ x ∈ x ∨ x = x := by
            simpa only [successorU, xU, Subtype.ext_iff] using h xU
          exact hz.mpr (Or.inr rfl)
        · have hzU : z ∈ U := htransitive.mem_trans hzx hxU
          have hz : z ∈ successor ↔ z ∈ x ∨ z = x := by
            simpa only [successorU, xU, Subtype.ext_iff] using
              h ⟨z, hzU⟩
          exact hz.mpr (Or.inl hzx)
    · intro hEq
      subst successor
      intro z
      simp only [successorU, xU, Subtype.ext_iff]
      rw [ZFSet.mem_insert_iff, or_comm]
  exact hbridge.symm.trans (hsemantic.trans hmeaning)

/-- The one-parameter formula asserting that the parameter is a successor
set and returning its predecessor as the existential witness. -/
def predecessorExistsFormula : FOFormula 1 :=
  .ex (successorSetAt (0 : Fin 2) (Fin.last 1))

/-- Full elementarity pulls the predecessor of an ordinal successor back
into the source domain. -/
theorem ordinalPredecessor_mem_of_succ_mem
    {domain big : ZFSet.{u}}
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    {alpha : Ordinal.{u}}
    (hsuccDomain : (Order.succ alpha).toZFSet ∈ domain) :
    alpha.toZFSet ∈ domain := by
  let successor := (Order.succ alpha).toZFSet
  have hsuccessorBig : successor ∈ big := hsubset hsuccDomain
  have halphaSucc : alpha.toZFSet ∈ successor := by
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ alpha)
  have halphaBig : alpha.toZFSet ∈ big :=
    hbigTransitive.mem_trans halphaSucc hsuccessorBig
  have hcanonical : successor = insert alpha.toZFSet alpha.toZFSet := by
    simp only [successor, Order.succ_eq_add_one,
      Ordinal.toZFSet_add_one]
  have hbigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      predecessorExistsFormula ![successor] := by
    simp only [predecessorExistsFormula, Model.SatisfiesIn]
    refine ⟨alpha.toZFSet, halphaBig, ?_⟩
    have hbody := (satisfiesIn_successorSetAt_swap_iff
      hbigTransitive hsuccessorBig halphaBig).mpr hcanonical
    have hsnoc : snoc ![successor] alpha.toZFSet =
        ![successor, alpha.toZFSet] := by
      funext i
      fin_cases i <;> rfl
    rw [hsnoc]
    exact hbody
  have hparams : ∀ i, ![successor] i ∈
      (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hsuccDomain
  have hdomainSat : Model.SatisfiesIn (domain : Set ZFSet.{u})
      predecessorExistsFormula ![successor] :=
    (habsolute predecessorExistsFormula ![successor] hparams).mpr hbigSat
  rcases hdomainSat with ⟨x, hxdomain, hxDomainSat⟩
  have hbodyDomain : Model.SatisfiesIn (domain : Set ZFSet.{u})
      (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] := by
    have hsnoc : snoc ![successor] x = ![successor, x] := by
      funext i
      fin_cases i <;> rfl
    rw [← hsnoc]
    exact hxDomainSat
  have hbodyParams : ∀ i, ![successor, x] i ∈
      (domain : Set ZFSet.{u}) := by
    intro i
    fin_cases i
    · exact hsuccDomain
    · exact hxdomain
  have hbodyBig : Model.SatisfiesIn (big : Set ZFSet.{u})
      (successorSetAt (0 : Fin 2) (1 : Fin 2)) ![successor, x] :=
    (habsolute (successorSetAt (0 : Fin 2) (1 : Fin 2))
      ![successor, x] hbodyParams).mp hbodyDomain
  have hxSuccessor : successor = insert x x :=
    (satisfiesIn_successorSetAt_swap_iff hbigTransitive
      hsuccessorBig (hsubset hxdomain)).mp hbodyBig
  have hxAlpha : x = alpha.toZFSet :=
    insert_self_injective (hxSuccessor.symm.trans hcanonical)
  simpa only [SetLike.mem_coe, hxAlpha] using hxdomain

/-- In a transitive carrier, existential successor satisfaction is exactly
closure under the actual von Neumann successor. -/
theorem satisfiesIn_successorExistsFormula_iff
    {U : ZFSet.{u}} (htransitive : U.IsTransitive)
    {x : ZFSet.{u}} (hxU : x ∈ U) :
    Model.SatisfiesIn (U : Set ZFSet.{u})
        successorExistsFormula ![x] ↔ insert x x ∈ U := by
  simp only [successorExistsFormula, Model.SatisfiesIn]
  constructor
  · rintro ⟨y, hyU, hy⟩
    have heq := (satisfiesIn_successorSetAt_iff
      htransitive hxU hyU).mp hy
    simpa only [SetLike.mem_coe, heq] using hyU
  · intro hsuccU
    refine ⟨insert x x, hsuccU, ?_⟩
    exact (satisfiesIn_successorSetAt_iff
      htransitive hxU hsuccU).mpr rfl

/-- Full satisfaction absoluteness pulls ambient successor witnesses into
the source domain.  The ambient carrier need only be transitive and closed
under successors of the relevant source ordinals. -/
theorem sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    (hbigSucc : ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x.IsOrdinal →
      insert x x ∈ big) :
    SourceOrdinalSuccessorClosed domain := by
  intro x hxdomain hxOrdinal
  have hparams : ∀ i, ![x] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hxdomain
  have hbigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      successorExistsFormula ![x] :=
    (satisfiesIn_successorExistsFormula_iff hbigTransitive
      (hsubset hxdomain)).mpr (hbigSucc hxdomain hxOrdinal)
  have hdomainSat : Model.SatisfiesIn (domain : Set ZFSet.{u})
      successorExistsFormula ![x] :=
    (habsolute successorExistsFormula ![x] hparams).mpr hbigSat
  rcases hdomainSat with ⟨y, hydomain, hySat⟩
  have hxyParams : ∀ i, ![x, y] i ∈ (domain : Set ZFSet.{u}) := by
    intro i
    fin_cases i
    · exact hxdomain
    · exact hydomain
  have hyBigSat : Model.SatisfiesIn (big : Set ZFSet.{u})
      (successorSetAt (1 : Fin 2) (0 : Fin 2)) ![x, y] :=
    (habsolute (successorSetAt (1 : Fin 2) (0 : Fin 2))
      ![x, y] hxyParams).mp hySat
  have hyEq : y = insert x x :=
    (satisfiesIn_successorSetAt_iff hbigTransitive
      (hsubset hxdomain) (hsubset hydomain)).mp hyBigSat
  simpa only [SetLike.mem_coe, ← hyEq] using hydomain

/-- Adjoining a member of a transitive set to itself is a definable subset
of that set. -/
theorem insert_self_mem_DefZF {a x : ZFSet.{u}}
    (ha : a.IsTransitive) (hx : x ∈ a) :
    insert x x ∈ DefZF a := by
  rw [mem_DefZF_iff_exists_satisfies]
  let xA : ZFCarrier a := ⟨x, hx⟩
  let params : Tuple (ZFCarrier a) 1 := ![xA]
  let phi : FOFormula 2 :=
    FOFormula.disj
      (.mem (Fin.last 1) (Fin.castSucc (0 : Fin 1)))
      (.eq (Fin.last 1) (Fin.castSucc (0 : Fin 1)))
  refine ⟨?_, 1, params, phi, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hzx
    · exact hx
    · exact ha.mem_trans hzx hx
  · intro z
    change z.1 ∈ insert x x ↔
      FOFormula.Satisfies (zfCarrierMem a) phi (snoc params z)
    simp only [phi, FOFormula.satisfies_disj, FOFormula.Satisfies,
      snoc_last, snoc_castSucc, params, Matrix.cons_val_zero, xA,
      zfCarrierMem, Subtype.ext_iff]
    rw [ZFSet.mem_insert_iff, or_comm]

/-- Every nonzero limit constructible level is closed under adjoining one of
its members to itself. -/
theorem insert_self_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    insert x x ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxalpha⟩
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ alpha, htheta.succ_lt halpha, ?_⟩
  rw [LStageZF_succ]
  exact insert_self_mem_DefZF (LStageZF_isTransitive alpha) hxalpha

/-- Source closure under ordinal successors descends to the transitive
collapse, provided full elementarity reflects which source elements are
ordinals. -/
theorem ordinalSuccessorClosed_range_of_satisfactionAbsolute
    {domain big : ZFSet.{u}}
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ big)
    (hbigTransitive : big.IsTransitive)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (big : Set ZFSet.{u}))
    (hsucc : SourceOrdinalSuccessorClosed domain) :
    OrdinalSuccessorClosed (range domain) := by
  intro alpha halphaRange
  rcases mem_range_iff.mp halphaRange with
    ⟨x, hxdomain, hcollapse⟩
  have hxOrdinal : x.IsOrdinal :=
    (isOrdinal_iff_collapse_isOrdinal_of_satisfactionAbsolute
      hextensional hsubset hbigTransitive habsolute hxdomain).mpr
      (hcollapse ▸ ZFSet.isOrdinal_toZFSet alpha)
  have hxSuccDomain : insert x x ∈ domain :=
    hsucc hxdomain hxOrdinal
  apply mem_range_iff.mpr
  refine ⟨insert x x, hxSuccDomain, ?_⟩
  rw [collapse_insert_self hxdomain, hcollapse,
    Order.succ_eq_add_one, Ordinal.toZFSet_add_one]

/-- Specialized closure theorem used by constructible condensation: a fully
elementary substructure of a limit `L`-level has a collapse whose ordinals
are closed under successor. -/
theorem ordinalSuccessorClosed_range_of_elementary_LStage
    {domain : ZFSet.{u}} {theta : Ordinal.{u}}
    (htheta : Order.IsSuccLimit theta)
    (hextensional : IsExtensional domain)
    (hsubset : domain ⊆ LStageZF theta)
    (habsolute : SatisfactionAbsolute
      (domain : Set ZFSet.{u}) (LStageZF theta : Set ZFSet.{u})) :
    OrdinalSuccessorClosed (range domain) := by
  apply ordinalSuccessorClosed_range_of_satisfactionAbsolute
    hextensional hsubset (LStageZF_isTransitive theta) habsolute
  apply sourceOrdinalSuccessorClosed_of_satisfactionAbsolute
    hsubset (LStageZF_isTransitive theta) habsolute
  intro x hxdomain _hxOrdinal
  exact insert_self_mem_LStageZF_of_isSuccLimit htheta
    (hsubset hxdomain)

/-- A source limit ordinal remains a nonzero limit after collapse whenever
the source contains zero and is closed under ordinal successor. -/
theorem collapseOrdinal_isSuccLimit_of_source_closed
    {domain : ZFSet.{u}} {limit : Ordinal.{u}}
    (hlimit : Order.IsSuccLimit limit)
    (hempty : (∅ : ZFSet.{u}) ∈ domain)
    (hsucc : SourceOrdinalSuccessorClosed domain) :
    Order.IsSuccLimit (collapseOrdinal domain limit) := by
  rw [Ordinal.isSuccLimit_iff]
  constructor
  · have hlimitNe : limit ≠ 0 :=
      (Ordinal.isSuccLimit_iff.mp hlimit).1
    have hzeroLimit : (0 : Ordinal.{u}) < limit :=
      (bot_lt_iff_ne_bot.mpr hlimitNe)
    have hzeroDomain : (0 : Ordinal.{u}).toZFSet ∈ domain := by
      simpa only [Ordinal.toZFSet_zero] using hempty
    have hzeroMem :
        collapse domain (0 : Ordinal.{u}).toZFSet ∈
          collapse domain limit.toZFSet :=
      mem_collapse_iff.mpr
        ⟨(0 : Ordinal.{u}).toZFSet,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hzeroLimit,
          hzeroDomain, rfl⟩
    have hcollapseZero :
        collapse domain (0 : Ordinal.{u}).toZFSet =
          (0 : Ordinal.{u}).toZFSet := by
      rw [Ordinal.toZFSet_zero]
      apply ZFSet.ext
      intro z
      rw [mem_collapse_iff]
      simp
    have hpositive : (0 : Ordinal.{u}) < collapseOrdinal domain limit := by
      apply Ordinal.toZFSet_mem_toZFSet_iff.mp
      rw [collapseOrdinal_toZFSet]
      rw [← hcollapseZero]
      exact hzeroMem
    exact ne_of_gt hpositive
  · apply Order.isSuccPrelimit_of_succ_lt
    intro gamma hgamma
    have hgammaMem :
        gamma.toZFSet ∈ collapse domain limit.toZFSet := by
      rw [← collapseOrdinal_toZFSet]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hgamma
    rcases mem_collapse_iff.mp hgammaMem with
      ⟨betaCode, hbetaCodeLimit, hbetaCodeDomain,
        hbetaCodeCollapse⟩
    rcases Ordinal.mem_toZFSet_iff.mp hbetaCodeLimit with
      ⟨beta, hbetaLimit, rfl⟩
    have hbetaGamma : collapseOrdinal domain beta = gamma := by
      apply Ordinal.toZFSet_injective
      rw [collapseOrdinal_toZFSet]
      exact hbetaCodeCollapse
    have hbetaSuccDomain : (Order.succ beta).toZFSet ∈ domain := by
      rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
      exact hsucc hbetaCodeDomain (ZFSet.isOrdinal_toZFSet beta)
    have hbetaSuccLimit : Order.succ beta < limit :=
      hlimit.succ_lt hbetaLimit
    have hcollapsedSuccLt :
        collapseOrdinal domain (Order.succ beta) <
          collapseOrdinal domain limit := by
      apply Ordinal.toZFSet_mem_toZFSet_iff.mp
      rw [collapseOrdinal_toZFSet, collapseOrdinal_toZFSet]
      exact mem_collapse_iff.mpr
        ⟨(Order.succ beta).toZFSet,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hbetaSuccLimit,
          hbetaSuccDomain, rfl⟩
    rw [collapseOrdinal_succ hbetaCodeDomain, hbetaGamma] at hcollapsedSuccLt
    exact hcollapsedSuccLt

/-! ## Constructible stages at limit indices -/

/-- Collapse compatibility at one constructible stage. -/
def CollapseStageCompatibleAt (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Prop :=
  collapse domain (LStageZF alpha) =
    LStageZF (collapseOrdinal domain alpha)

/-- The bounded stage-witness property required in the forward direction of
the limit step.  Full elementarity supplies this property by reflecting the
existential assertion `x ∈ L_beta` with `beta ∈ alpha`. -/
def HasSmallerInternalLStageWitnesses (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x ∈ LStageZF alpha →
    ∃ beta : Ordinal.{u}, beta < alpha ∧
      beta.toZFSet ∈ domain ∧ x ∈ LStageZF beta

/-- The collapse of the empty set is empty. -/
@[simp]
theorem collapse_empty (domain : ZFSet.{u}) :
    collapse domain (∅ : ZFSet.{u}) = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  simp

/-- The collapsed ordinal represented by zero is zero. -/
@[simp]
theorem collapseOrdinal_zero (domain : ZFSet.{u}) :
    collapseOrdinal domain 0 = 0 := by
  apply Ordinal.toZFSet_injective
  rw [collapseOrdinal_toZFSet, Ordinal.toZFSet_zero,
    collapse_empty]

/-- Collapse is compatible with the zeroth constructible stage. -/
theorem collapseStageCompatibleAt_zero (domain : ZFSet.{u}) :
    CollapseStageCompatibleAt domain 0 := by
  simp [CollapseStageCompatibleAt]

/-- Limit step for constructible-stage collapse.

The forward inclusion uses bounded internal stage witnesses.  For the reverse
inclusion, every ordinal below the collapsed index is automatically the
collapse of a unique domain ordinal below the source index; this follows
directly from `mem_collapse_iff` and needs no choice principle. -/
theorem collapseStageCompatibleAt_limit
    {domain : ZFSet.{u}} {limit : Ordinal.{u}}
    (himageLimit : Order.IsSuccLimit (collapseOrdinal domain limit))
    (hwitness : HasSmallerInternalLStageWitnesses domain limit)
    (hbelow : ∀ (beta : Ordinal.{u}), beta < limit →
      beta.toZFSet ∈ domain → CollapseStageCompatibleAt domain beta) :
    CollapseStageCompatibleAt domain limit := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_collapse_iff.mp hz with
      ⟨x, hxLimit, hxdomain, rfl⟩
    rcases hwitness hxdomain hxLimit with
      ⟨beta, hbetaLimit, hbetaDomain, hxBeta⟩
    have hxCollapsedBeta :
        collapse domain x ∈ collapse domain (LStageZF beta) :=
      mem_collapse_iff.mpr ⟨x, hxBeta, hxdomain, rfl⟩
    have hxTargetBeta :
        collapse domain x ∈ LStageZF (collapseOrdinal domain beta) := by
      rw [← hbelow beta hbetaLimit hbetaDomain]
      exact hxCollapsedBeta
    apply (mem_LStageZF_limit_iff himageLimit).mpr
    refine ⟨collapseOrdinal domain beta, ?_, hxTargetBeta⟩
    apply Ordinal.toZFSet_mem_toZFSet_iff.mp
    rw [collapseOrdinal_toZFSet, collapseOrdinal_toZFSet]
    exact mem_collapse_iff.mpr
      ⟨beta.toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr hbetaLimit,
        hbetaDomain, rfl⟩
  · intro hz
    rcases (mem_LStageZF_limit_iff himageLimit).mp hz with
      ⟨gamma, hgamma, hzGamma⟩
    have hgammaCollapse :
        gamma.toZFSet ∈ collapse domain limit.toZFSet := by
      rw [← collapseOrdinal_toZFSet]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hgamma
    rcases mem_collapse_iff.mp hgammaCollapse with
      ⟨betaCode, hbetaCodeLimit, hbetaCodeDomain,
        hbetaCodeCollapse⟩
    rcases Ordinal.mem_toZFSet_iff.mp hbetaCodeLimit with
      ⟨beta, hbetaLimit, rfl⟩
    have hbetaGamma : collapseOrdinal domain beta = gamma := by
      apply Ordinal.toZFSet_injective
      rw [collapseOrdinal_toZFSet]
      exact hbetaCodeCollapse
    have hzCollapsedBeta :
        z ∈ collapse domain (LStageZF beta) := by
      rw [hbelow beta hbetaLimit hbetaCodeDomain, hbetaGamma]
      exact hzGamma
    rcases mem_collapse_iff.mp hzCollapsedBeta with
      ⟨x, hxBeta, hxdomain, hcollapse⟩
    exact mem_collapse_iff.mpr
      ⟨x, LStageZF_mono hbetaLimit.le hxBeta, hxdomain, hcollapse⟩

/-- Transfinite recursion principle for collapse compatibility.  The
successor case is an explicit interface, while the limit case is discharged
by `collapseStageCompatibleAt_limit`. -/
theorem collapseStageCompatibleAt_of_zero_succ_limit
    {domain : ZFSet.{u}}
    (hpredecessor : ∀ (alpha : Ordinal.{u}),
      (Order.succ alpha).toZFSet ∈ domain → alpha.toZFSet ∈ domain)
    (hsucc : ∀ (alpha : Ordinal.{u}), alpha.toZFSet ∈ domain →
      (Order.succ alpha).toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha →
        CollapseStageCompatibleAt domain (Order.succ alpha))
    (hlimitImage : ∀ (limit : Ordinal.{u}), Order.IsSuccLimit limit →
      limit.toZFSet ∈ domain →
        Order.IsSuccLimit (collapseOrdinal domain limit))
    (hlimitWitness : ∀ (limit : Ordinal.{u}), Order.IsSuccLimit limit →
      limit.toZFSet ∈ domain →
        HasSmallerInternalLStageWitnesses domain limit) :
    ∀ (alpha : Ordinal.{u}), alpha.toZFSet ∈ domain →
      CollapseStageCompatibleAt domain alpha := by
  intro alpha
  induction alpha using Ordinal.limitRecOn with
  | zero =>
      intro _hzero
      exact collapseStageCompatibleAt_zero domain
  | add_one alpha ih =>
      intro hsuccessor
      have halpha : alpha.toZFSet ∈ domain :=
        hpredecessor alpha hsuccessor
      exact hsucc alpha halpha hsuccessor (ih halpha)
  | limit limit hlimit ih =>
      intro hlimitDomain
      apply collapseStageCompatibleAt_limit
        (hlimitImage limit hlimit hlimitDomain)
        (hlimitWitness limit hlimit hlimitDomain)
      intro beta hbeta hbetaDomain
      exact ih beta hbeta hbetaDomain

end

end Constructible.MostowskiCollapse
