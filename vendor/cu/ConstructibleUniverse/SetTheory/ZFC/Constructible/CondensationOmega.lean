/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Condensation

/-!
# Condensation at the first limit level

This file proves the `theta = omega` case of the standard Condensation
Lemma.  The proof does not use the fixed evaluator parameters from the
reflection-level argument: the standard omega level does not contain its own
omega.  Instead it uses the ordinary fact that `L_omega` consists of
hereditarily finite sets and is therefore pointwise generated from the empty
set by finite insertion.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace OmegaCondensation

/-- A `ZFSet` is externally finite when its external set of members is
finite.  This is the direct Lean rendering of ordinary set-theoretic
finiteness used in the metatheoretic proof that `L_omega = HF`. -/
def ExternallyFinite (x : ZFSet.{u}) : Prop :=
  (x : Set ZFSet.{u}).Finite

/-- The internal powerset of an externally finite `ZFSet` has only finitely
many members externally. -/
theorem externallyFinite_powerset {a : ZFSet.{u}}
    (ha : ExternallyFinite a) : ExternallyFinite a.powerset := by
  classical
  let code : ZFSet.{u} -> Finset ZFSet.{u} :=
    fun z => ha.toFinset.filter fun x => x ∈ z
  have himage :
      code '' (a.powerset : Set ZFSet.{u}) ⊆
        (↑(ha.toFinset.powerset) : Set (Finset ZFSet.{u})) := by
    rintro t ⟨z, _hz, rfl⟩
    change code z ∈ ha.toFinset.powerset
    rw [Finset.mem_powerset]
    intro x hx
    exact (Finset.mem_filter.mp (by simpa only [code] using hx)).1
  apply Set.Finite.of_finite_image
    ((Finset.finite_toSet ha.toFinset.powerset).subset himage)
  intro x hx y hy hxy
  have hxsub : x ⊆ a := ZFSet.mem_powerset.mp hx
  have hysub : y ⊆ a := ZFSet.mem_powerset.mp hy
  apply ZFSet.ext
  intro z
  have hzx : z ∈ code x ↔ z ∈ x := by
    constructor
    · exact fun hz => (Finset.mem_filter.mp
        (by simpa only [code] using hz)).2
    · intro hz
      simpa only [code] using (Finset.mem_filter.mpr
        ⟨ha.mem_toFinset.mpr (hxsub hz), hz⟩)
  have hzy : z ∈ code y ↔ z ∈ y := by
    constructor
    · exact fun hz => (Finset.mem_filter.mp
        (by simpa only [code] using hz)).2
    · intro hz
      simpa only [code] using (Finset.mem_filter.mpr
        ⟨ha.mem_toFinset.mpr (hysub hz), hz⟩)
  rw [← hzx, hxy, hzy]

/-- `DefZF a` is externally finite whenever `a` is externally finite. -/
theorem externallyFinite_defZF {a : ZFSet.{u}}
    (ha : ExternallyFinite a) : ExternallyFinite (DefZF a) := by
  exact (externallyFinite_powerset ha).subset (DefZF_subset_powerset a)

/-- Every finite-indexed constructible level has finitely many members. -/
theorem externallyFinite_LStageZF_nat (n : Nat) :
    ExternallyFinite (LStageZF (n : Ordinal.{u})) := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, LStageZF_zero, ExternallyFinite]
      have hcoe : ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅ := by
        ext x
        simp
      rw [hcoe]
      exact Set.finite_empty
  | succ n ih =>
      rw [Nat.cast_succ, ← Order.succ_eq_add_one, LStageZF_succ]
      exact externallyFinite_defZF ih

/-- Every member of `L_omega` is externally finite.  Together with
transitivity of `L_omega`, this is precisely the hereditary-finiteness fact
needed below. -/
theorem externallyFinite_of_mem_LStageZF_omega
    {x : ZFSet.{u}} (hx : x ∈ LStageZF (Ordinal.omega0 : Ordinal.{u})) :
    ExternallyFinite x := by
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp hx with
    ⟨alpha, halpha, hxalpha⟩
  rcases Ordinal.lt_omega0.mp halpha with ⟨n, rfl⟩
  exact (externallyFinite_LStageZF_nat n).subset
    ((LStageZF_isTransitive (n : Ordinal.{u})).subset_of_mem hxalpha)

/-! ## Exact first-order definitions of the finite constructors -/

/-- The unary formula saying that its only coordinate has no members. -/
def emptyBody : FOFormula 1 :=
  FOFormula.all (.neg (.mem (Fin.last 1) (0 : Fin 1).castSucc))

/-- The three-coordinate formula with layout `[element, oldSet, output]`
saying `output = insert element oldSet`. -/
def insertBody : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (FOFormula.disj
        (.eq (Fin.last 3) (0 : Fin 3).castSucc)
        (.mem (Fin.last 3) (1 : Fin 3).castSucc)))

/-- Exact restricted semantics of `emptyBody`.  Quantification is over the
displayed carrier, as required by `SatisfactionAbsolute`. -/
@[simp]
theorem satisfiesIn_emptyBody_iff (M : Set ZFSet.{u}) (x : ZFSet.{u}) :
    Model.SatisfiesIn M emptyBody ![x] ↔
      ∀ z : ZFSet.{u}, z ∈ M → z ∉ x := by
  classical
  simp only [emptyBody, FOFormula.all, Model.SatisfiesIn,
    snoc_last, snoc_castSucc, Matrix.cons_val_zero]
  push Not
  rfl

/-- Exact restricted semantics of `insertBody`. -/
@[simp]
theorem satisfiesIn_insertBody_iff (M : Set ZFSet.{u})
    (a b out : ZFSet.{u}) :
    Model.SatisfiesIn M insertBody ![a, b, out] ↔
      ∀ z : ZFSet.{u}, z ∈ M →
        (z ∈ out ↔ z = a ∨ z ∈ b) := by
  classical
  simp only [insertBody, FOFormula.all, Model.SatisfiesIn,
    Model.satisfiesIn_biimp_iff, Model.satisfiesIn_disj_iff,
    snoc_last, snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push Not
  rfl

/-- Tarski--Vaught in the special form used below: an object uniquely
first-order definable in `big` from parameters in `small` belongs to `small`.
No definability or uniqueness is hidden in the name; both are explicit
hypotheses. -/
theorem uniqueDefinable_mem_of_satisfactionAbsolute
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    (helem : SatisfactionAbsolute small big)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple ZFSet.{u} n)
    (hparams : ∀ i, params i ∈ small)
    (out : ZFSet.{u}) (hout : out ∈ big)
    (hsat : Model.SatisfiesIn big phi (snoc params out))
    (hunique : ∀ y : ZFSet.{u}, y ∈ big →
      Model.SatisfiesIn big phi (snoc params y) → y = out) :
    out ∈ small := by
  have hexBig : Model.SatisfiesIn big (.ex phi) params :=
    ⟨out, hout, hsat⟩
  have hexSmall : Model.SatisfiesIn small (.ex phi) params :=
    (helem (.ex phi) params hparams).mpr hexBig
  rcases hexSmall with ⟨y, hySmall, hySmallSat⟩
  have hsnoc : ∀ i, snoc params y i ∈ small := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hySmall
    · simpa using hparams j
  have hyBigSat : Model.SatisfiesIn big phi (snoc params y) :=
    (helem phi (snoc params y) hsnoc).mp hySmallSat
  have hyo : y = out := hunique y (hsubset hySmall) hyBigSat
  simpa only [← hyo] using hySmall

/-! ## Closure of `L_omega` and of an elementary substructure -/

/-- Inserting one member into a set already in a transitive carrier produces
a definable subset of that carrier. -/
theorem insert_mem_DefZF_of_mem {A a b : ZFSet.{u}}
    (htrans : A.IsTransitive) (ha : a ∈ A) (hb : b ∈ A) :
    insert a b ∈ DefZF A := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sa : ZFCarrier A := ⟨a, ha⟩
  let sb : ZFCarrier A := ⟨b, hb⟩
  let params : Tuple (ZFCarrier A) 2 := ![sa, sb]
  let phi : FOFormula 3 :=
    FOFormula.disj
      (.eq (Fin.last 2) (Fin.castSucc (0 : Fin 2)))
      (.mem (Fin.last 2) (Fin.castSucc (1 : Fin 2)))
  refine ⟨?_, 2, params, phi, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
    · exact ha
    · exact htrans.mem_trans hz hb
  · intro z
    rw [ZFSet.mem_insert_iff, FOFormula.satisfies_disj]
    change
      (z.1 = a ∨ z.1 ∈ b) ↔
        (snoc params z (Fin.last 2) =
            snoc params z (Fin.castSucc (0 : Fin 2)) ∨
          (snoc params z (Fin.last 2)).1 ∈
            (snoc params z (Fin.castSucc (1 : Fin 2))).1)
    simp only [snoc_last, snoc_castSucc]
    simp only [params, sa, sb, Matrix.cons_val_zero,
      Matrix.cons_val_one, Subtype.ext_iff]

/-- The empty set is a member of `L_omega`. -/
theorem empty_mem_LStageZF_omega :
    (∅ : ZFSet.{u}) ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  apply (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mpr
  refine ⟨((1 : Nat) : Ordinal.{u}),
    Ordinal.natCast_lt_omega0 1, ?_⟩
  rw [show ((1 : Nat) : Ordinal.{u}) = Order.succ 0 by simp,
    LStageZF_succ, LStageZF_zero, DefZF_empty]
  simp

/-- `L_omega` is closed under adjoining one element to a set. -/
theorem insert_mem_LStageZF_omega {a b : ZFSet.{u}}
    (ha : a ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (hb : b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u})) :
    insert a b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp ha with
    ⟨alpha, halpha, haalpha⟩
  rcases (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mp hb with
    ⟨beta, hbeta, hbbeta⟩
  let delta : Ordinal.{u} := max alpha beta
  have hdelta : delta < Ordinal.omega0 :=
    max_lt halpha hbeta
  have haDelta : a ∈ LStageZF delta :=
    LStageZF_mono (le_max_left alpha beta) haalpha
  have hbDelta : b ∈ LStageZF delta :=
    LStageZF_mono (le_max_right alpha beta) hbbeta
  apply (mem_LStageZF_limit_iff Ordinal.isSuccLimit_omega0).mpr
  refine ⟨Order.succ delta,
    Ordinal.isSuccLimit_omega0.succ_lt hdelta, ?_⟩
  rw [LStageZF_succ]
  exact insert_mem_DefZF_of_mem
    (LStageZF_isTransitive delta) haDelta hbDelta

/-- Full elementarity in `L_omega` puts the actual empty set in the smaller
structure.  Uniqueness is checked in the transitive ambient level. -/
theorem empty_mem_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    (∅ : ZFSet.{u}) ∈ domain := by
  let noParams : Tuple ZFSet.{u} 0 := fun i => Fin.elim0 i
  apply uniqueDefinable_mem_of_satisfactionAbsolute
    hsubset helem emptyBody noParams
    (fun i => Fin.elim0 i) (∅ : ZFSet.{u})
    empty_mem_LStageZF_omega
  · have hraw :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          emptyBody ![(∅ : ZFSet.{u})] :=
      (satisfiesIn_emptyBody_iff _ _).mpr
        (fun z _hz => ZFSet.notMem_empty z)
    have hassign :
        snoc noParams (∅ : ZFSet.{u}) = ![(∅ : ZFSet.{u})] := by
      funext i
      fin_cases i
      rfl
    rw [hassign]
    exact hraw
  · intro y hy hySat
    have hySat' :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          emptyBody ![y] := by
      have hassign : snoc noParams y = ![y] := by
        funext i
        fin_cases i
        rfl
      rw [← hassign]
      exact hySat
    have hnone := (satisfiesIn_emptyBody_iff _ y).mp hySat'
    apply (ZFSet.eq_empty y).mpr
    intro z hz
    have hzOmega :
        z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
      (LStageZF_isTransitive
        (Ordinal.omega0 : Ordinal.{u})).mem_trans hz hy
    exact hnone z hzOmega hz

/-- Full elementarity in `L_omega` is closed under the actual finite
insertion operation. -/
theorem insert_mem_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u}))
    {a b : ZFSet.{u}} (ha : a ∈ domain) (hb : b ∈ domain) :
    insert a b ∈ domain := by
  let params : Tuple ZFSet.{u} 2 := ![a, b]
  have haOmega := hsubset ha
  have hbOmega := hsubset hb
  have houtOmega :
      insert a b ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    insert_mem_LStageZF_omega haOmega hbOmega
  refine uniqueDefinable_mem_of_satisfactionAbsolute
    hsubset helem insertBody params ?_ (insert a b) houtOmega ?_ ?_
  · intro i
    fin_cases i
    · change a ∈ domain
      exact ha
    · change b ∈ domain
      exact hb
  · have hraw :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          insertBody ![a, b, insert a b] :=
      (satisfiesIn_insertBody_iff _ _ _ _).mpr
        (fun z _hz => ZFSet.mem_insert_iff)
    have hassign :
        snoc params (insert a b) = ![a, b, insert a b] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact hraw
  · intro y hyOmega hySat
    have hySat' :
        Model.SatisfiesIn
          (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})
          insertBody ![a, b, y] := by
      have hassign : snoc params y = ![a, b, y] := by
        funext i
        fin_cases i <;> rfl
      rw [← hassign]
      exact hySat
    have hcharacterization :=
      (satisfiesIn_insertBody_iff _ a b y).mp hySat'
    apply ZFSet.ext
    intro z
    constructor
    · intro hzy
      have hzOmega :
          z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
        (LStageZF_isTransitive
          (Ordinal.omega0 : Ordinal.{u})).mem_trans hzy hyOmega
      exact ZFSet.mem_insert_iff.mpr
        ((hcharacterization z hzOmega).mp hzy)
    · intro hzInsert
      have hzOmega :
          z ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
        (LStageZF_isTransitive
          (Ordinal.omega0 : Ordinal.{u})).mem_trans hzInsert houtOmega
      exact (hcharacterization z hzOmega).mpr
        (ZFSet.mem_insert_iff.mp hzInsert)

/-- A set with finitely many members belongs to a carrier containing the
empty set and closed under insertion, provided each of its members belongs to
that carrier. -/
theorem mem_of_externallyFinite_of_insert_closed
    {domain x : ZFSet.{u}} (hempty : (∅ : ZFSet.{u}) ∈ domain)
    (hinsert : ∀ {a b : ZFSet.{u}}, a ∈ domain → b ∈ domain →
      insert a b ∈ domain)
    (hfinite : ExternallyFinite x) (hmembers : x ⊆ domain) :
    x ∈ domain := by
  classical
  have build : ∀ s : Finset ZFSet.{u},
      (∀ z : ZFSet.{u}, z ∈ s → z ∈ domain) →
        ∃ y : ZFSet.{u}, y ∈ domain ∧
          ∀ z : ZFSet.{u}, (z ∈ y ↔ z ∈ s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _hmembers
        refine ⟨∅, hempty, ?_⟩
        intro z
        simp
    | @insert a s ha ih =>
        intro hsMembers
        have haDomain : a ∈ domain :=
          hsMembers a (Finset.mem_insert_self a s)
        have hsDomain : ∀ z : ZFSet.{u}, z ∈ s → z ∈ domain := by
          intro z hz
          exact hsMembers z (Finset.mem_insert_of_mem hz)
        rcases ih hsDomain with ⟨old, holdDomain, hold⟩
        refine ⟨insert a old, hinsert haDomain holdDomain, ?_⟩
        intro z
        rw [ZFSet.mem_insert_iff, Finset.mem_insert, hold z]
  have hfinsetMembers :
      ∀ z : ZFSet.{u}, z ∈ hfinite.toFinset → z ∈ domain := by
    intro z hz
    exact hmembers (hfinite.mem_toFinset.mp hz)
  rcases build hfinite.toFinset hfinsetMembers with
    ⟨y, hyDomain, hyMembers⟩
  have hxy : x = y := by
    apply ZFSet.ext
    intro z
    rw [hyMembers z]
    exact hfinite.mem_toFinset.symm
  simpa only [hxy] using hyDomain

/-- Every fully elementary substructure of `L_omega` contains all of
`L_omega`.  The proof is well-founded membership induction, using hereditary
finiteness and the two exact finite constructors above. -/
theorem LStageZF_omega_subset_of_elementary {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    LStageZF (Ordinal.omega0 : Ordinal.{u}) ⊆ domain := by
  have hempty : (∅ : ZFSet.{u}) ∈ domain :=
    empty_mem_of_elementary_omega hsubset helem
  have hinsert : ∀ {a b : ZFSet.{u}}, a ∈ domain → b ∈ domain →
      insert a b ∈ domain :=
    fun ha hb => insert_mem_of_elementary_omega hsubset helem ha hb
  intro x hxOmega
  refine ZFSet.inductionOn
    (p := fun x : ZFSet.{u} =>
      x ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) → x ∈ domain)
    x ?_ hxOmega
  intro x ih hx
  apply mem_of_externallyFinite_of_insert_closed hempty hinsert
    (externallyFinite_of_mem_LStageZF_omega hx)
  intro y hy
  have hyOmega :
      y ∈ LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    (LStageZF_isTransitive
      (Ordinal.omega0 : Ordinal.{u})).mem_trans hy hx
  exact ih y hy hyOmega

/-- A fully elementary substructure of `L_omega` whose carrier is an actual
`ZFSet` is exactly `L_omega`. -/
theorem domain_eq_LStageZF_omega_of_elementary {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  apply ZFSet.ext
  intro x
  constructor
  · exact fun hx => hsubset hx
  · exact fun hx =>
      LStageZF_omega_subset_of_elementary hsubset helem hx

end OmegaCondensation

/-- The standard Condensation conclusion at `theta = omega`: the Mostowski
collapse of every set-sized fully elementary substructure of `L_omega` is
`L_omega` itself. -/
theorem condensation_of_elementary_omega {domain : ZFSet.{u}}
    (hsubset : domain ⊆ LStageZF (Ordinal.omega0 : Ordinal.{u}))
    (helem : SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF (Ordinal.omega0 : Ordinal.{u}) : Set ZFSet.{u})) :
    range domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) := by
  have hdomain :
      domain = LStageZF (Ordinal.omega0 : Ordinal.{u}) :=
    OmegaCondensation.domain_eq_LStageZF_omega_of_elementary
      hsubset helem
  have htrans : domain.IsTransitive := by
    rw [hdomain]
    exact LStageZF_isTransitive (Ordinal.omega0 : Ordinal.{u})
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases mem_range_iff.mp hz with ⟨x, hx, hcollapse⟩
    have hfixed := collapse_eq_self_of_mem htrans x hx
    have hxz : x = z := hfixed.symm.trans hcollapse
    rw [← hdomain, ← hxz]
    exact hx
  · intro hz
    have hzDomain : z ∈ domain := by
      rw [hdomain]
      exact hz
    exact mem_range_iff.mpr
      ⟨z, hzDomain, collapse_eq_self_of_mem htrans z hzDomain⟩

end

end MostowskiCollapse

end Constructible
