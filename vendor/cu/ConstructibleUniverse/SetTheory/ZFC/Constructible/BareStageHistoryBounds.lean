/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.VEqualsL

/-!
# Local bounds for bounded constructible-stage histories

This file records the elementary closure facts needed before constructing a
stage-only ("bare") history inside a prescribed limit level.  The hypotheses
and conclusions are deliberately local: membership in the proper class `L`
is not used as a substitute for membership in `LStageZF theta`.

The results below do not yet internalize the Replacement family occurring at
a limit step.  In particular, they do not claim that `stageHistoryData alpha`
belongs to every later limit level.
-/

@[expose] public section

universe u v

namespace Constructible

section ZFC

open Set

/-! ## Explicit finite successor bounds -/

/-- Pairing raises an explicit stage bound by one successor. -/
theorem pair_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ({x, y} : ZFSet.{u}) ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  exact pair_mem_DefZF hx hy

/-- Union raises an explicit stage bound by one successor. -/
theorem sUnion_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {x : ZFSet.{u}} (hx : x ∈ LStageZF alpha) :
    ZFSet.sUnion x ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  exact sUnion_mem_DefZF (LStageZF_isTransitive alpha) hx

/-- A Kuratowski ordered pair raises an explicit stage bound by two
successors. -/
theorem orderedPair_mem_LStageZF_succ_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ZFSet.pair x y ∈
      LStageZF (Order.succ (Order.succ alpha)) := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈
    LStageZF (Order.succ (Order.succ alpha))
  apply pair_mem_LStageZF_succ
  · simpa using pair_mem_LStageZF_succ hx hx
  · exact pair_mem_LStageZF_succ hx hy

/-- A right-associated Kuratowski triple raises an explicit stage bound by
four successors. -/
theorem triple_mem_LStageZF_four_succ {alpha : Ordinal.{u}}
    {x y z : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) (hz : z ∈ LStageZF alpha) :
    Godel.triple x y z ∈
      LStageZF
        (Order.succ (Order.succ (Order.succ (Order.succ alpha)))) := by
  change ZFSet.pair x (ZFSet.pair y z) ∈
    LStageZF
      (Order.succ (Order.succ (Order.succ (Order.succ alpha))))
  apply orderedPair_mem_LStageZF_succ_succ
  · exact LStageZF_mono
      ((Order.le_succ alpha).trans (Order.le_succ (Order.succ alpha))) hx
  · exact orderedPair_mem_LStageZF_succ_succ hy hz

/-- If a Kuratowski pair belongs to a transitive level, both coordinates
belong to that level. -/
theorem orderedPair_components_mem_LStageZF {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hpair : ZFSet.pair x y ∈ LStageZF alpha) :
    x ∈ LStageZF alpha ∧ y ∈ LStageZF alpha := by
  have htrans := LStageZF_isTransitive alpha
  have hxSingleton : ({x} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  exact
    ⟨htrans.mem_trans (by simp) hxSingleton,
      htrans.mem_trans (by simp) hxyPair⟩

/-- A fiber of a relation whose relation and selected coordinate lie in one
level belongs to the next level. -/
theorem Godel.fiber_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {relation index : ZFSet.{u}}
    (hrelation : relation ∈ LStageZF alpha)
    (hindex : index ∈ LStageZF alpha) :
    Godel.fiber relation index ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  apply (Godel.fiberDelta0Section hrelation hindex).mem_DefZF
    (LStageZF_isTransitive alpha)
  intro value hvalue
  exact (orderedPair_components_mem_LStageZF
    ((LStageZF_isTransitive alpha).mem_trans
      (Godel.mem_fiber_iff.mp hvalue) hrelation)).1

/-! ## Local closure under the rudimentary basis -/

/-- Every Jensen--Devlin primitive operation preserves an arbitrary nonzero
limit level.  The proof keeps an explicit common input stage and uses at most
five further successor stages; no appeal to closure of the proper class `L`
occurs. -/
theorem Godel.op_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (i : Fin 9) {x y : ZFSet.{u}}
    (hx : x ∈ LStageZF theta) (hy : y ∈ LStageZF theta) :
    Godel.op i x y ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  rcases (mem_LStageZF_limit_iff htheta).mp hy with
    ⟨beta, hbeta, hyBeta⟩
  let gamma0 := max alpha beta
  let gamma1 := Order.succ gamma0
  let gamma2 := Order.succ gamma1
  let gamma3 := Order.succ gamma2
  let gamma4 := Order.succ gamma3
  let gamma5 := Order.succ gamma4
  have hgamma0 : gamma0 < theta := max_lt halpha hbeta
  have hgamma1 : gamma1 < theta := htheta.succ_lt hgamma0
  have hgamma2 : gamma2 < theta := htheta.succ_lt hgamma1
  have hgamma3 : gamma3 < theta := htheta.succ_lt hgamma2
  have hgamma4 : gamma4 < theta := htheta.succ_lt hgamma3
  have hgamma5 : gamma5 < theta := htheta.succ_lt hgamma4
  have hx0 : x ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_left alpha beta) hxAlpha
  have hy0 : y ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_right alpha beta) hyBeta
  have lift0 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma0 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1
          (LStageZF_subset_succ gamma0 hz)))
  have lift1 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma1 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1 hz))
  have lift2 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma2 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2 hz)
  have htrans0 := LStageZF_isTransitive gamma0
  have hsub : Godel.op i x y ⊆ LStageZF gamma4 := by
    intro q hq
    fin_cases i
    · rcases Godel.mem_F0_iff.mp hq with rfl | rfl
      · exact lift0 hx0
      · exact lift0 hy0
    · exact lift0 (htrans0.mem_trans (Godel.mem_F1_iff.mp hq).1 hx0)
    · rcases Godel.mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hy0)
    · rcases Godel.mem_F3_iff.mp hq with
        ⟨a, z, b, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        (htrans0.mem_trans hz hx0) hcomponents.2
    · rcases Godel.mem_F4_iff.mp hq with
        ⟨a, b, z, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        hcomponents.2 (htrans0.mem_trans hz hx0)
    · rcases (Godel.mem_F5_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨member, hmember, hqMember⟩
      exact lift0
        (htrans0.mem_trans hqMember
          (htrans0.mem_trans hmember hx0))
    · rcases (Godel.mem_F6_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨left, hpair⟩
      exact lift0
        (orderedPair_components_mem_LStageZF
          (htrans0.mem_trans hpair hx0)).2
    · rcases (Godel.mem_F7_iff (x := x) (y := y) (q := q)).mp hq with
        ⟨a, ha, b, hb, rfl, _hab⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hx0)
    · rcases Godel.mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
      apply lift1
      exact Godel.fiber_mem_LStageZF_succ hx0
        (htrans0.mem_trans hz hy0)
  have hx4 : x ∈ LStageZF gamma4 := lift0 hx0
  have hy4 : y ∈ LStageZF gamma4 := lift0 hy0
  have hop5 : Godel.op i x y ∈ LStageZF gamma5 := by
    change Godel.op i x y ∈ LStageZF (Order.succ gamma4)
    rw [LStageZF_succ]
    exact Godel.op_mem_DefZF_of_subset
      (LStageZF_isTransitive gamma4) hx4 hy4 hsub
  exact LStageZF_mono hgamma5.le hop5

/-- Evaluation of every finite rudimentary term preserves a nonzero limit
level when all generator values lie in that level. -/
theorem Godel.RudimentaryTerm.eval_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {alpha : Type v} {rho : alpha → ZFSet.{u}}
    (hrho : ∀ a, rho a ∈ LStageZF theta)
    (term : Godel.RudimentaryTerm alpha) :
    Godel.RudimentaryTerm.eval rho term ∈ LStageZF theta := by
  induction term with
  | var a => exact hrho a
  | app i left right hleft hright =>
      exact Godel.op_mem_LStageZF_of_isSuccLimit
        htheta i hleft hright

/-- A nonzero limit level is closed under unordered pairing. -/
theorem pair_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    ({x, y} : ZFSet.{u}) ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  rcases (mem_LStageZF_limit_iff htheta).mp hy with
    ⟨beta, hbeta, hyBeta⟩
  let gamma := max alpha beta
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ gamma, htheta.succ_lt (max_lt halpha hbeta), ?_⟩
  rw [LStageZF_succ]
  exact pair_mem_DefZF
    (LStageZF_mono (le_max_left alpha beta) hxAlpha)
    (LStageZF_mono (le_max_right alpha beta) hyBeta)

/-- A nonzero limit level is closed under singleton formation. -/
theorem singleton_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    ({x} : ZFSet.{u}) ∈ LStageZF theta := by
  simpa using pair_mem_LStageZF_of_isSuccLimit htheta hx hx

/-- A nonzero limit level is closed under set union. -/
theorem sUnion_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x : ZFSet.{u}} (hx : x ∈ LStageZF theta) :
    ZFSet.sUnion x ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  apply (mem_LStageZF_limit_iff htheta).mpr
  refine ⟨Order.succ alpha, htheta.succ_lt halpha, ?_⟩
  rw [LStageZF_succ]
  exact sUnion_mem_DefZF (LStageZF_isTransitive alpha) hxAlpha

/-- A nonzero limit level is closed under binary union. -/
theorem union_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    x ∪ y ∈ LStageZF theta := by
  rw [← ZFSet.sUnion_pair]
  exact sUnion_mem_LStageZF_of_isSuccLimit htheta
    (pair_mem_LStageZF_of_isSuccLimit htheta hx hy)

/-- A nonzero limit level is closed under Kuratowski ordered pairing. -/
theorem orderedPair_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) :
    ZFSet.pair x y ∈ LStageZF theta := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈ LStageZF theta
  exact pair_mem_LStageZF_of_isSuccLimit htheta
    (singleton_mem_LStageZF_of_isSuccLimit htheta hx)
    (pair_mem_LStageZF_of_isSuccLimit htheta hx hy)

/-- A nonzero limit level is closed under the right-associated triple code. -/
theorem triple_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {x y z : ZFSet.{u}} (hx : x ∈ LStageZF theta)
    (hy : y ∈ LStageZF theta) (hz : z ∈ LStageZF theta) :
    Godel.triple x y z ∈ LStageZF theta := by
  change ZFSet.pair x (ZFSet.pair y z) ∈ LStageZF theta
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta hx
    (orderedPair_mem_LStageZF_of_isSuccLimit htheta hy hz)

/-- Every earlier ordinal code belongs to a strictly later constructible
level.  No limit hypothesis is needed. -/
theorem ordinal_toZFSet_mem_LStageZF_of_lt
    {alpha theta : Ordinal.{u}} (halpha : alpha < theta) :
    alpha.toZFSet ∈ LStageZF theta := by
  exact LStageZF_mono (Order.succ_le_of_lt halpha)
    (ordinal_toZFSet_mem_LStage_succ alpha)

/-- Limit-specialized spelling of `ordinal_toZFSet_mem_LStageZF_of_lt`. -/
theorem ordinal_toZFSet_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    alpha.toZFSet ∈ LStageZF theta :=
  ordinal_toZFSet_mem_LStageZF_of_lt halpha

/-- The code of `omega` is not an element of `L_omega`.  Thus a history
formula carrying `omega` as a free parameter cannot be interpreted in
`L_omega` with that intended assignment. -/
theorem omega_toZFSet_not_mem_LStageZF_omega :
    Ordinal.omega0.toZFSet ∉ LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  intro homega
  have hrankLt :=
    (ordinal_stage_invariants (Ordinal.omega0 : Ordinal.{u})).1
      (ZFSet.isOrdinal_toZFSet Ordinal.omega0) homega
  have hrank :
      (Ordinal.omega0.toZFSet : ZFSet.{u}).rank = Ordinal.omega0 := by
    apply Ordinal.toZFSet_injective
    exact (ZFSet.isOrdinal_toZFSet
      (Ordinal.omega0 : Ordinal.{u})).toZFSet_rank_eq
  rw [hrank] at hrankLt
  exact (lt_irrefl _ hrankLt).elim

/-- The earlier constructible level itself belongs to a later limit level. -/
theorem LStageZF_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    LStageZF alpha ∈ LStageZF theta :=
  LStageZF_mem_of_lt halpha

/-! ## Local bounds for finite sequence and program codes -/

/-- Every finite ordinal code belongs to every nonzero limit level. -/
theorem FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (n : Nat) :
    (FiniteSequenceZF.natCode n : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [FiniteSequenceZF.natCode] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta n)

/-- The empty set belongs to every nonzero limit level. -/
theorem empty_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (∅ : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [FiniteSequenceZF.natCode, Nat.cast_zero,
    Ordinal.toZFSet_zero] using
    FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit htheta 0

/-- A structural finite-list code stays in a nonzero limit level when all
of its entries lie there. -/
theorem FiniteSequenceZF.listCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) :
    FiniteSequenceZF.listCode xs ∈ LStageZF theta := by
  induction xs with
  | nil =>
      simpa only [FiniteSequenceZF.listCode_nil] using
        empty_mem_LStageZF_of_isSuccLimit htheta
  | cons x xs ih =>
      rw [FiniteSequenceZF.listCode_cons]
      apply orderedPair_mem_LStageZF_of_isSuccLimit htheta
      · exact hxs x (by simp)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- A length-tagged structural finite-sequence code stays in a nonzero
limit level when all of its entries lie there. -/
theorem FiniteSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) :
    FiniteSequenceZF.sequenceCode xs ∈ LStageZF theta := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
    (FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit htheta xs.length)
    (FiniteSequenceZF.listCode_mem_LStageZF_of_isSuccLimit htheta hxs)

/-- The finite indexed graph of a list stays in a nonzero limit level when
all list entries lie there. -/
theorem IndexedSequenceZF.graphFrom_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) (start : Nat) :
    IndexedSequenceZF.graphFrom start xs ∈ LStageZF theta := by
  induction xs generalizing start with
  | nil =>
      simpa only [IndexedSequenceZF.graphFrom_nil] using
        empty_mem_LStageZF_of_isSuccLimit htheta
  | cons x xs ih =>
      rw [IndexedSequenceZF.graphFrom_cons, ZFSet.insert_eq]
      apply union_mem_LStageZF_of_isSuccLimit htheta
      · apply singleton_mem_LStageZF_of_isSuccLimit htheta
        exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
          (hxs x (by simp))
          (FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit
            htheta start)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- A length-tagged indexed sequence code stays in a nonzero limit level
when all of its entries lie there. -/
theorem IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ LStageZF theta) :
    IndexedSequenceZF.sequenceCode xs ∈ LStageZF theta := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit htheta
    (FiniteSequenceZF.natCode_mem_LStageZF_of_isSuccLimit htheta xs.length)
    (IndexedSequenceZF.graphFrom_mem_LStageZF_of_isSuccLimit
      htheta hxs 0)

namespace Godel.RudimentaryTerm

/-- The variable-token tag is available in every nonzero limit level. -/
theorem varTag_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (varTag : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [varTag, Nat.cast_zero] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta 0)

/-- The application-token tag is available in every nonzero limit level. -/
theorem appTag_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta) :
    (appTag : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [appTag, Nat.cast_one] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta 1)

/-- Every one of the nine finite operation tags is available in every
nonzero limit level. -/
theorem operationCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (i : Fin 9) :
    (operationCode i : ZFSet.{u}) ∈ LStageZF theta := by
  simpa only [operationCode] using
    ordinal_toZFSet_mem_LStageZF_of_lt
      (Ordinal.natCast_lt_of_isSuccLimit htheta i.1)

/-- The natural interpretation of a rudimentary generator stays in a
transitive limit level containing its seed `U`. -/
theorem rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (generator : Option (Constructible.ZFCarrier U)) :
    rudimentaryGenerator U generator ∈ LStageZF theta := by
  cases generator with
  | none => exact hU
  | some x =>
      exact (LStageZF_isTransitive theta).mem_trans x.2 hU

/-- The genuine set code of one stack token stays in a nonzero limit level
containing its seed. -/
theorem stackTokenZFCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (token : StackToken (Option (Constructible.ZFCarrier U))) :
    stackTokenZFCode U token ∈ LStageZF theta := by
  cases token with
  | inl generator =>
      exact triple_mem_LStageZF_of_isSuccLimit htheta
        (varTag_mem_LStageZF_of_isSuccLimit htheta)
        (rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
          htheta hU generator)
        (empty_mem_LStageZF_of_isSuccLimit htheta)
  | inr operation =>
      exact triple_mem_LStageZF_of_isSuccLimit htheta
        (appTag_mem_LStageZF_of_isSuccLimit htheta)
        (operationCode_mem_LStageZF_of_isSuccLimit htheta operation)
        (empty_mem_LStageZF_of_isSuccLimit htheta)

/-- The indexed code of a finite postfix program stays in a nonzero limit
level containing its seed. -/
theorem stackProgramZFCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) :
    stackProgramZFCode U program ∈ LStageZF theta := by
  apply IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit htheta
  intro encodedToken hEncodedToken
  rcases List.mem_map.mp hEncodedToken with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit htheta hU token

/-! ## Local bounds for successful stack executions -/

/-- One successful local machine step preserves the property that every
stack entry belongs to the prescribed nonzero limit level. -/
theorem runStackToken_entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta)
    (hstep : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    ∀ x ∈ output, x ∈ LStageZF theta := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst output
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
          htheta hU generator
      · exact hinput x hx
  | inr operation =>
      cases input with
      | nil => simp [runStackToken] at hstep
      | cons right tail =>
          cases tail with
          | nil => simp [runStackToken] at hstep
          | cons left rest =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst output
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Godel.op_mem_LStageZF_of_isSuccLimit
                  htheta operation
                  (hinput left (by simp)) (hinput right (by simp))
              · exact hinput x (by simp [hx])

/-- Every state in a successful finite trace remains entrywise inside the
prescribed nonzero limit level. -/
theorem ExecutionTrace.entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta) :
    ∀ stack ∈ states, ∀ x ∈ stack, x ∈ LStageZF theta := by
  induction htrace generalizing input with
  | nil stack =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      simpa using hinput
  | @cons token program input next tailStates hstep htail ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      have hnext : ∀ x ∈ next, x ∈ LStageZF theta :=
        runStackToken_entries_mem_LStageZF_of_isSuccLimit
          htheta hU token _ _ hinput hstep
      intro stack hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | hstack
      · exact hinput
      · exact ih rfl hnext stack
          (by simpa only [List.mem_cons] using hstack)

/-- An indexed trace code stays in a nonzero limit level whenever all entries
of all of its finite stack states lie there. -/
theorem executionTraceZFCode_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {states : List (List ZFSet.{u})}
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF theta) :
    executionTraceZFCode states ∈ LStageZF theta := by
  apply IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit htheta
  intro stackCode hstackCode
  rcases List.mem_map.mp hstackCode with ⟨stack, hstack, rfl⟩
  apply FiniteSequenceZF.listCode_mem_LStageZF_of_isSuccLimit htheta
  exact hstates stack hstack

/-- The code of a successful trace from an entrywise bounded initial stack
belongs to the same prescribed nonzero limit level. -/
theorem executionTraceZFCode_mem_LStageZF_of_ExecutionTrace
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta) :
    executionTraceZFCode states ∈ LStageZF theta := by
  exact executionTraceZFCode_mem_LStageZF_of_isSuccLimit htheta
    (htrace.entries_mem_LStageZF_of_isSuccLimit
      htheta hU hhead hinput)

end Godel.RudimentaryTerm

namespace Model

/-- Above `omega`, every fixed evaluator parameter really is an element of
the prescribed limit stage. -/
theorem stageHistoryFixedParameters_mem_LStageZF_of_omega_lt
    {theta : Ordinal.{u}} (homega : Ordinal.omega0 < theta) :
    ∀ i : Fin 13,
      (stageHistoryFixedParameters.{u} i).1 ∈ LStageZF theta := by
  intro i
  rw [← canonicalStageParameters_eq_fixed]
  fin_cases i <;>
    simp only [canonicalStageParameters] <;>
    apply ordinal_toZFSet_mem_LStageZF_of_lt <;>
    first
    | exact homega
    | exact (Ordinal.natCast_lt_omega0 _).trans homega

/-- The final evaluator parameter witnesses the precise obstruction at
`L_omega`: it is the set `omega` itself, which is not in that level. -/
theorem stageHistoryFixedParameters_last_not_mem_LStageZF_omega :
    (stageHistoryFixedParameters.{u} (Fin.last 12)).1 ∉
      LStageZF Ordinal.omega0 := by
  simpa only [stageHistoryFixedParameters_last] using
    (omega_toZFSet_not_mem_LStageZF_omega :
      Ordinal.omega0.toZFSet ∉
        LStageZF (Ordinal.omega0 : Ordinal.{u}))

/-- Appending one canonical state entry preserves membership in a nonzero
limit level, provided all four inputs already belong to that level. -/
theorem addHistoryEntry_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (history index stage relation : LCarrier.{u})
    (hhistory : history.1 ∈ LStageZF theta)
    (hindex : index.1 ∈ LStageZF theta)
    (hstage : stage.1 ∈ LStageZF theta)
    (hrelation : relation.1 ∈ LStageZF theta) :
    (addHistoryEntry history index stage relation).1 ∈ LStageZF theta := by
  have htriple :
      (tripleLCarrier index stage relation).1 ∈ LStageZF theta := by
    simpa only [tripleLCarrier_val] using
      triple_mem_LStageZF_of_isSuccLimit htheta hindex hstage hrelation
  have hsingleton :
      (singletonLCarrier (tripleLCarrier index stage relation)).1 ∈
        LStageZF theta := by
    change
      ({(tripleLCarrier index stage relation).1,
        (tripleLCarrier index stage relation).1} : ZFSet.{u}) ∈
          LStageZF theta
    exact pair_mem_LStageZF_of_isSuccLimit htheta htriple htriple
  change
    ZFSet.sUnion
      ({history.1,
        (singletonLCarrier (tripleLCarrier index stage relation)).1} :
          ZFSet.{u}) ∈ LStageZF theta
  apply sUnion_mem_LStageZF_of_isSuccLimit htheta
  exact pair_mem_LStageZF_of_isSuccLimit htheta hhistory hsingleton

/-- The carrier wrapper for an earlier ordinal has the same local bound as
its underlying von Neumann code. -/
theorem ordinalLCarrier_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (_htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    (ordinalLCarrier alpha).1 ∈ LStageZF theta := by
  simpa only [ordinalLCarrier_val] using
    ordinal_toZFSet_mem_LStageZF_of_lt halpha

/-- The carrier wrapper for an earlier level belongs to the later limit
level; this is membership of the represented set, not merely inclusion. -/
theorem stageLCarrier_mem_LStageZF_of_lt_isSuccLimit
    {alpha theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (halpha : alpha < theta) :
    (stageLCarrier alpha).1 ∈ LStageZF theta := by
  simpa only [stageLCarrier_val] using
    LStageZF_mem_LStageZF_of_lt_isSuccLimit htheta halpha

end Model

end ZFC

end Constructible
