/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Model
public import Mathlib.Tactic.FinCases

/-!
# Elementarity for a finite formula fragment

This file isolates the Tarski--Vaught argument needed by the later Skolem-hull
and condensation construction.  For one fixed formula, `ClosesWithin` asks a
smaller carrier to contain witnesses for every existential subformula, with
parameters from the smaller carrier.  This finite closure condition is enough
to make satisfaction of the formula absolute between the two carriers.

Unlike a full elementary-substructure predicate, this construction does not
quantify over or encode all first-order formulas.  That distinction matters
for the cardinality-controlled hull used in the proof of GCH in `L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/--
`ClosesWithin phi small big` says that `small` contains a witness, whenever
`big` satisfies an existential subformula of `phi` with parameters in
`small`.  The recursive clauses impose the same condition on every subformula
of `phi`.
-/
def ClosesWithin (small big : Set ZFSet.{u}) :
    {n : Nat} -> FOFormula n -> Prop
  | _, .mem _ _ => True
  | _, .eq _ _ => True
  | _, .neg phi => ClosesWithin small big phi
  | _, .conj phi psi =>
      ClosesWithin small big phi /\ ClosesWithin small big psi
  | n, .ex phi =>
      ClosesWithin small big phi /\
        forall s : Tuple ZFSet.{u} n,
          (forall i, s i ∈ small) ->
          Model.SatisfiesIn big (.ex phi) s ->
          exists x : ZFSet.{u},
            x ∈ small /\ Model.SatisfiesIn big phi (snoc s x)

/--
Tarski--Vaught for one formula and its finite subformula tree.  The explicit
inclusion hypothesis is used when a witness already lies in the smaller
carrier and must be viewed in the larger one.
-/
theorem satisfiesIn_iff_of_closesWithin
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    {n : Nat} (phi : FOFormula n) (hclose : ClosesWithin small big phi)
    (s : Tuple ZFSet.{u} n) (hs : forall i, s i ∈ small) :
    Model.SatisfiesIn small phi s <-> Model.SatisfiesIn big phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      exact not_congr (ih hclose s hs)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi hclose.1 s hs) (ihPsi hclose.2 s hs)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hxSmall, hphi⟩
        refine ⟨x, hsubset hxSmall, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mp hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxSmall
        · simpa using hs j
      · intro hex
        rcases hclose.2 s hs hex with ⟨x, hxSmall, hphi⟩
        refine ⟨x, hxSmall, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mpr hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxSmall
        · simpa using hs j

/-- A closed fragment remains absolute for every tuple from `small`. -/
theorem closesWithin_iff_satisfiesIn
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    {n : Nat} {phi : FOFormula n} (hclose : ClosesWithin small big phi) :
    forall s : Tuple ZFSet.{u} n,
      (forall i, s i ∈ small) ->
      (Model.SatisfiesIn small phi s <-> Model.SatisfiesIn big phi s) :=
  fun s hs => satisfiesIn_iff_of_closesWithin hsubset phi hclose s hs

/-! ## The extensionality fragment -/

/-- A witness belongs to exactly one of the two free set variables. -/
def distinguishingMemberFormula : FOFormula 2 :=
  .ex (FOFormula.disj
    (.conj
      (.mem (Fin.last 2) (0 : Fin 2).castSucc)
      (.neg (.mem (Fin.last 2) (1 : Fin 2).castSucc)))
    (.conj
      (.mem (Fin.last 2) (1 : Fin 2).castSucc)
      (.neg (.mem (Fin.last 2) (0 : Fin 2).castSucc))))

@[simp]
theorem satisfiesIn_distinguishingMemberFormula
    (carrier : Set ZFSet.{u}) (x y : ZFSet.{u}) :
    Model.SatisfiesIn carrier distinguishingMemberFormula ![x, y] <->
      exists z : ZFSet.{u}, z ∈ carrier /\
        ((z ∈ x /\ z ∉ y) \/ (z ∈ y /\ z ∉ x)) := by
  classical
  simp only [distinguishingMemberFormula, Model.SatisfiesIn,
    FOFormula.disj, snoc_last, snoc_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply exists_congr
  intro z
  apply and_congr_right
  intro _hz
  tauto

/--
Closure under the single distinguishing-member formula makes membership on
`small` extensional, provided `big` is transitive.  This is the exact
extensionality input required for the Mostowski collapse of a finite-fragment
Skolem hull.
-/
theorem restricted_extensionality_of_closesWithin
    {small big : Set ZFSet.{u}}
    (hsubset : small ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithin small big distinguishingMemberFormula)
    {x y : ZFSet.{u}} (hx : x ∈ small) (hy : y ∈ small)
    (hsame : forall z : ZFSet.{u}, z ∈ small -> (z ∈ x <-> z ∈ y)) :
    x = y := by
  by_contra hxy
  have hdifference :
      exists z : ZFSet.{u}, (z ∈ x /\ z ∉ y) \/ (z ∈ y /\ z ∉ x) := by
    by_contra hnone
    apply hxy
    apply ZFSet.ext
    intro z
    by_contra hnotIff
    apply hnone
    by_cases hzx : z ∈ x
    · exact ⟨z, Or.inl ⟨hzx, fun hzy => hnotIff (iff_of_true hzx hzy)⟩⟩
    · have hzy : z ∈ y := by
        by_contra hzy
        exact hnotIff (iff_of_false hzx hzy)
      exact ⟨z, Or.inr ⟨hzy, hzx⟩⟩
  rcases hdifference with ⟨z, hdiff⟩
  have hzBig : z ∈ big := by
    rcases hdiff with hleft | hright
    · exact htrans x (hsubset hx) z hleft.1
    · exact htrans y (hsubset hy) z hright.1
  have hbigExists :
      Model.SatisfiesIn big distinguishingMemberFormula ![x, y] := by
    rw [satisfiesIn_distinguishingMemberFormula]
    exact ⟨z, hzBig, hdiff⟩
  have hparams : forall i, ![x, y] i ∈ small := by
    intro i
    fin_cases i <;> assumption
  rcases hclose.2 ![x, y] hparams hbigExists with
    ⟨w, hwSmall, hwFormula⟩
  have hwdiff : (w ∈ x /\ w ∉ y) \/ (w ∈ y /\ w ∉ x) := by
    classical
    simp only [Model.SatisfiesIn,
      FOFormula.disj, snoc_last, snoc_castSucc,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hwFormula
    tauto
  rcases hwdiff with hleft | hright
  · exact hleft.2 ((hsame w hwSmall).mp hleft.1)
  · exact hright.2 ((hsame w hwSmall).mpr hright.1)

end ZFC

end Constructible
