/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSkolemStep

/-!
# Arity-separated one-formula Skolem selection

`FormulaSkolemStep` uses a generic selector whose object-language predicate
contains both a nullary and a positive-arity disjunct.  That is sufficient for
its witness-existence theorem, but it is not an exact one-formula Skolem
operation: for a positive-arity compiled relation, the nullary disjunct can
also select a malformed, untagged member of the relation.

This file separates those two cases at the formula level.  A nullary formula
is handled by `nullaryCanonicalWitnessSelection`; a formula with at least one
parameter is handled by `positiveCanonicalWitnessSelection`.  Each selector
is obtained by Separation inside `L`, and minimality is expressed by the
actual internal graph `canonicalWitnessOrder`.  In particular, meta-level
choice is not used to choose any witness.

The exact membership theorems below expose the distinction: the positive
selector has only a prefix-fiber branch and therefore cannot admit an
unrelated bare tuple code through a nullary branch.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Branch-specific object-language predicates -/

/--
Layout `[U, relations, order, y]`.  Some member `relation` of `relations`
contains `y`, and `y` is the `order`-least such member lying in `U`.
-/
def nullaryWitnessSelectionFormula : FOFormula 4 :=
  .ex
    (.conj
      (.mem (4 : Fin 5) (1 : Fin 5))
      (.conj
        (.mem (3 : Fin 5) (4 : Fin 5))
        (.all
          (FOFormula.imp
            (.conj
              (.mem (5 : Fin 6) (0 : Fin 6))
              (.mem (5 : Fin 6) (4 : Fin 6)))
            (.neg (graphRelAt (2 : Fin 6) (5 : Fin 6) (3 : Fin 6)))))))

@[simp]
theorem satisfies_nullaryWitnessSelectionFormula
    (U relations order y : LCarrier.{u}) :
    FOFormula.Satisfies LMem nullaryWitnessSelectionFormula
        ![U, relations, order, y] ↔
      ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
        y.1 ∈ relation.1 ∧
          ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
            ¬ GraphRel order z y := by
  simp only [nullaryWitnessSelectionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt]
  apply exists_congr
  intro relation
  have hrelationAssignment :
      snoc ![U, relations, order, y] relation =
        ![U, relations, order, y, relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hrelationAssignment]
  apply and_congr_right
  intro _hrelation
  apply and_congr_right
  intro _hy
  constructor
  · intro hminimal z hzU hzRelation
    have hz := hminimal z
    rw [show
      snoc ![U, relations, order, y, relation] z =
        ![U, relations, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl] at hz
    exact hz ⟨hzU, hzRelation⟩
  · intro hminimal z
    rw [show
      snoc ![U, relations, order, y, relation] z =
        ![U, relations, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl]
    rintro ⟨hzU, hzRelation⟩
    exact hminimal z hzU hzRelation

/--
Layout `[U, relations, prefixes, order, y]`.  Some member `relation` of
`relations` has an `order`-least `U`-witness `y` in the fiber over some member
of `prefixes`.  There is deliberately no nullary disjunct.
-/
def positiveWitnessSelectionFormula : FOFormula 5 :=
  .ex
    (.conj
      (.mem (5 : Fin 6) (1 : Fin 6))
      (.ex positiveRudimentaryWitnessFormula))

@[simp]
theorem satisfies_positiveWitnessSelectionFormula
    (U relations prefixes order y : LCarrier.{u}) :
    FOFormula.Satisfies LMem positiveWitnessSelectionFormula
        ![U, relations, prefixes, order, y] ↔
      ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
        ∃ p : LCarrier.{u}, p.1 ∈ prefixes.1 ∧
          GraphRel relation y p ∧
            ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
              GraphRel relation z p → ¬ GraphRel order z y := by
  simp only [positiveWitnessSelectionFormula, FOFormula.Satisfies]
  apply exists_congr
  intro relation
  have hrelationAssignment :
      snoc ![U, relations, prefixes, order, y] relation =
        ![U, relations, prefixes, order, y, relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hrelationAssignment]
  apply and_congr_right
  intro _hrelation
  apply exists_congr
  intro p
  have hpAssignment :
      snoc ![U, relations, prefixes, order, y, relation] p =
        ![U, relations, prefixes, order, y, relation, p] := by
    funext i
    fin_cases i <;> rfl
  rw [hpAssignment, satisfies_positiveRudimentaryWitnessFormula]

/-! ## Internal branch-specific selections -/

/-- The nullary canonical witnesses, constructed by Separation in `L`. -/
def nullaryCanonicalWitnessSelection
    (U relations : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    nullaryWitnessSelectionFormula
    ![U, relations, canonicalWitnessOrder U]
    U)

@[simp]
theorem mem_nullaryCanonicalWitnessSelection_iff
    (U relations y : LCarrier.{u}) :
    y.1 ∈ (nullaryCanonicalWitnessSelection U relations).1 ↔
      y.1 ∈ U.1 ∧
        ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
          y.1 ∈ relation.1 ∧
            ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
              ¬ GraphRel (canonicalWitnessOrder U) z y := by
  rw [nullaryCanonicalWitnessSelection]
  rw [Classical.choose_spec (exists_separationLCarrier
    nullaryWitnessSelectionFormula
    ![U, relations, canonicalWitnessOrder U]
    U) y]
  rw [show
    snoc ![U, relations, canonicalWitnessOrder U] y =
      ![U, relations, canonicalWitnessOrder U, y] by
        funext i
        fin_cases i <;> rfl]
  rw [satisfies_nullaryWitnessSelectionFormula]

/-- The positive-arity canonical witnesses, constructed by Separation in `L`. -/
def positiveCanonicalWitnessSelection
    (U relations prefixes : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    positiveWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U)

@[simp]
theorem mem_positiveCanonicalWitnessSelection_iff
    (U relations prefixes y : LCarrier.{u}) :
    y.1 ∈ (positiveCanonicalWitnessSelection U relations prefixes).1 ↔
      y.1 ∈ U.1 ∧
        ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
          ∃ p : LCarrier.{u}, p.1 ∈ prefixes.1 ∧
            GraphRel relation y p ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                GraphRel relation z p →
                  ¬ GraphRel (canonicalWitnessOrder U) z y := by
  rw [positiveCanonicalWitnessSelection]
  rw [Classical.choose_spec (exists_separationLCarrier
    positiveWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U) y]
  rw [show
    snoc ![U, relations, prefixes, canonicalWitnessOrder U] y =
      ![U, relations, prefixes, canonicalWitnessOrder U, y] by
        funext i
        fin_cases i <;> rfl]
  rw [satisfies_positiveWitnessSelectionFormula]

/-! ## The exact one-formula selector and step -/

/-- Select the correct internal branch from the formula's parameter arity. -/
def aritySeparatedFormulaSkolemSelection
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : LCarrier.{u} :=
  match n with
  | 0 =>
      nullaryCanonicalWitnessSelection U
        (formulaSkolemRelationFamily U hU phi)
  | m + 1 =>
      positiveCanonicalWitnessSelection U
        (formulaSkolemRelationFamily U hU phi)
        (formulaSkolemPrefixFamily seed (m + 1))

/-- Retain the seed and adjoin exactly the branch-appropriate witnesses. -/
def aritySeparatedFormulaSkolemStep
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : LCarrier.{u} :=
  unionLCarrier seed (aritySeparatedFormulaSkolemSelection seed U hU phi)

/-- Exact membership semantics in the nullary formula selector. -/
theorem mem_aritySeparatedFormulaSkolemSelection_zero_iff
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (phi : FOFormula 1) (y : LCarrier.{u}) :
    y.1 ∈ (aritySeparatedFormulaSkolemSelection seed U hU phi).1 ↔
      y.1 ∈ U.1 ∧
        y.1 ∈ (formulaSkolemRelation U hU phi).1 ∧
          ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
            z.1 ∈ (formulaSkolemRelation U hU phi).1 →
              ¬ GraphRel (canonicalWitnessOrder U) z y := by
  change y.1 ∈ (nullaryCanonicalWitnessSelection U
    (formulaSkolemRelationFamily U hU phi)).1 ↔ _
  rw [mem_nullaryCanonicalWitnessSelection_iff]
  constructor
  · rintro ⟨hyU, relation, hrelation, hyRelation, hminimal⟩
    have hrelationEq :=
      (mem_formulaSkolemRelationFamily_iff U hU phi relation).mp hrelation
    subst relation
    exact ⟨hyU, hyRelation, hminimal⟩
  · rintro ⟨hyU, hyRelation, hminimal⟩
    refine ⟨hyU, formulaSkolemRelation U hU phi, ?_, hyRelation, hminimal⟩
    exact (mem_formulaSkolemRelationFamily_iff U hU phi
      (formulaSkolemRelation U hU phi)).mpr rfl

/--
Exact membership semantics in the positive-arity formula selector.  The
right-hand side has only a prefix-fiber case; no bare relation member can
enter through a nullary alternative.
-/
theorem mem_aritySeparatedFormulaSkolemSelection_succ_iff
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (m : Nat) (phi : FOFormula (m + 2)) (y : LCarrier.{u}) :
    y.1 ∈ (aritySeparatedFormulaSkolemSelection seed U hU phi).1 ↔
      y.1 ∈ U.1 ∧
        ∃ p : LCarrier.{u},
          p.1 ∈ Godel.positiveTupleSpace seed.1 m ∧
            GraphRel (formulaSkolemRelation U hU phi) y p ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                GraphRel (formulaSkolemRelation U hU phi) z p →
                  ¬ GraphRel (canonicalWitnessOrder U) z y := by
  change y.1 ∈ (positiveCanonicalWitnessSelection U
    (formulaSkolemRelationFamily U hU phi)
    (formulaSkolemPrefixFamily seed (m + 1))).1 ↔ _
  rw [mem_positiveCanonicalWitnessSelection_iff]
  constructor
  · rintro ⟨hyU, relation, hrelation, p, hp, hyGraph, hminimal⟩
    have hrelationEq :=
      (mem_formulaSkolemRelationFamily_iff U hU phi relation).mp hrelation
    subst relation
    refine ⟨hyU, p, ?_, hyGraph, hminimal⟩
    simpa only [formulaSkolemPrefixFamily_succ_val] using hp
  · rintro ⟨hyU, p, hp, hyGraph, hminimal⟩
    refine ⟨hyU, formulaSkolemRelation U hU phi, ?_, p, ?_,
      hyGraph, hminimal⟩
    · exact (mem_formulaSkolemRelationFamily_iff U hU phi
        (formulaSkolemRelation U hU phi)).mpr rfl
    · simpa only [formulaSkolemPrefixFamily_succ_val] using hp

/-- Exact membership semantics for the nullary one-formula step. -/
theorem mem_aritySeparatedFormulaSkolemStep_zero_iff
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (phi : FOFormula 1) (y : LCarrier.{u}) :
    y.1 ∈ (aritySeparatedFormulaSkolemStep seed U hU phi).1 ↔
      y.1 ∈ seed.1 ∨
        (y.1 ∈ U.1 ∧
          y.1 ∈ (formulaSkolemRelation U hU phi).1 ∧
            ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
              z.1 ∈ (formulaSkolemRelation U hU phi).1 →
                ¬ GraphRel (canonicalWitnessOrder U) z y) := by
  rw [aritySeparatedFormulaSkolemStep,
    mem_unionLCarrier_iff,
    mem_aritySeparatedFormulaSkolemSelection_zero_iff]

/-- Exact membership semantics for a positive-arity one-formula step. -/
theorem mem_aritySeparatedFormulaSkolemStep_succ_iff
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    (m : Nat) (phi : FOFormula (m + 2)) (y : LCarrier.{u}) :
    y.1 ∈ (aritySeparatedFormulaSkolemStep seed U hU phi).1 ↔
      y.1 ∈ seed.1 ∨
        (y.1 ∈ U.1 ∧
          ∃ p : LCarrier.{u},
            p.1 ∈ Godel.positiveTupleSpace seed.1 m ∧
              GraphRel (formulaSkolemRelation U hU phi) y p ∧
                ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                  GraphRel (formulaSkolemRelation U hU phi) z p →
                    ¬ GraphRel (canonicalWitnessOrder U) z y) := by
  rw [aritySeparatedFormulaSkolemStep,
    mem_unionLCarrier_iff,
    mem_aritySeparatedFormulaSkolemSelection_succ_iff]

/-- The exact step retains every member of the seed. -/
theorem seed_subset_aritySeparatedFormulaSkolemStep
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    seed.1 ⊆ (aritySeparatedFormulaSkolemStep seed U hU phi).1 := by
  intro x hx
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx seed.2⟩
  exact (mem_unionLCarrier_iff seed
    (aritySeparatedFormulaSkolemSelection seed U hU phi) xL).mpr
      (Or.inl hx)

/-- If the seed lies in `U`, every output of the exact step still lies in `U`. -/
theorem aritySeparatedFormulaSkolemStep_subset
    {seed U : LCarrier.{u}} (hU : U.1.IsTransitive)
    (hseed : seed.1 ⊆ U.1)
    {n : Nat} (phi : FOFormula (n + 1)) :
    (aritySeparatedFormulaSkolemStep seed U hU phi).1 ⊆ U.1 := by
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx (aritySeparatedFormulaSkolemStep seed U hU phi).2⟩
  rcases (mem_unionLCarrier_iff seed
      (aritySeparatedFormulaSkolemSelection seed U hU phi) xL).mp hx with
    hxSeed | hxSelected
  · exact hseed hxSeed
  · cases n with
    | zero =>
        exact (mem_aritySeparatedFormulaSkolemSelection_zero_iff
          seed U hU phi xL).mp hxSelected |>.1
    | succ m =>
        exact (mem_aritySeparatedFormulaSkolemSelection_succ_iff
          seed U hU m phi xL).mp hxSelected |>.1

/-! ## Tarski witness closure -/

private theorem positiveTupleCode_zero_snoc_eq
    {U : ZFSet.{u}} (params : Tuple (ZFCarrier U) 0)
    (x : ZFCarrier U) :
    Godel.positiveTupleCode 0
        (Delta0Formula.val (snoc params x)) = x.1 := by
  change (snoc params x 0).1 = x.1
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, snoc_last]

/--
Every seed-parameter instance of `phi` which has a witness in `U` has its
canonical witness in the arity-separated step.  In the successor case the
proof enters the selector exclusively through its prefix-fiber semantics.
-/
theorem exists_witness_mem_aritySeparatedFormulaSkolemStep
    {seed U : LCarrier.{u}} (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U.1) n)
    (hparams : ∀ i, (params i).1 ∈ seed.1)
    (hexists : ∃ x : ZFCarrier U.1,
      FOFormula.Satisfies (zfCarrierMem U.1) phi (snoc params x)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈ (aritySeparatedFormulaSkolemStep seed U hU phi).1 ∧
        FOFormula.Satisfies (zfCarrierMem U.1) phi (snoc params y) := by
  let relationIndex := Godel.boundedSatisfactionIndex U.1 hU phi
  let relation := formulaSkolemRelation U hU phi
  rcases hexists with ⟨x, hxSat⟩
  have hxCode :
      Godel.positiveTupleCode n
          (Delta0Formula.val (snoc params x)) ∈ relationIndex.1 := by
    exact (Godel.mem_boundedSatisfactionRelation_iff
      U.1 hU phi (snoc params x)).mpr hxSat
  rcases existsUnique_canonicalRudimentaryWitnessGraph
      U relationIndex params ⟨x, hxCode⟩ with
    ⟨y, hyGraph, _hyUnique⟩
  rcases (graphRel_canonicalRudimentaryWitnessGraph_relation_iff
      U relationIndex params y).mp hyGraph with
    ⟨yU, hyEq, hyCode, hminimal⟩
  have hyU : y.1 ∈ U.1 := by
    rw [hyEq]
    exact yU.2
  have hySelection :
      y.1 ∈
        (aritySeparatedFormulaSkolemSelection seed U hU phi).1 := by
    cases n with
    | zero =>
        apply (mem_aritySeparatedFormulaSkolemSelection_zero_iff
          seed U hU phi y).mpr
        refine ⟨hyU, ?_, ?_⟩
        · have hyCode' : yU.1 ∈ relationIndex.1 := by
            simpa only [positiveTupleCode_zero_snoc_eq] using hyCode
          change y.1 ∈ relation.1
          rw [hyEq]
          change yU.1 ∈ relationIndex.1
          exact hyCode'
        · intro z hzU hzRelation
          let zU : ZFCarrier U.1 := ⟨z.1, hzU⟩
          have hzCode :
              Godel.positiveTupleCode 0
                  (Delta0Formula.val (snoc params zU)) ∈
                    relationIndex.1 := by
            change z.1 ∈ relationIndex.1
            change z.1 ∈ relationIndex.1 at hzRelation
            exact hzRelation
          have hzMinimal := hminimal zU hzCode
          have hzEq :
              (⟨zU.1, mem_L_of_mem zU.2 U.2⟩ : LCarrier.{u}) = z :=
            Subtype.ext rfl
          simpa only [hzEq] using hzMinimal
    | succ m =>
        apply (mem_aritySeparatedFormulaSkolemSelection_succ_iff
          seed U hU m phi y).mpr
        let p : LCarrier.{u} := positiveTupleCodeLCarrier U params
        refine ⟨hyU, p, ?_, ?_, ?_⟩
        · change Godel.positiveTupleCode m (Delta0Formula.val params) ∈
            Godel.positiveTupleSpace seed.1 m
          exact (Godel.mem_positiveTupleSpace_iff
            (U := seed.1) (s := Delta0Formula.val params)).mpr hparams
        · change ZFSet.pair y.1 p.1 ∈ relationIndex.1
          simpa only [Delta0Formula.val_snoc,
            Godel.positiveTupleCode_snoc, p,
            positiveTupleCodeLCarrier, hyEq] using hyCode
        · intro z hzU hzGraph
          let zU : ZFCarrier U.1 := ⟨z.1, hzU⟩
          have hzPair : ZFSet.pair z.1 p.1 ∈ relationIndex.1 := by
            change ZFSet.pair z.1 p.1 ∈ relationIndex.1 at hzGraph
            exact hzGraph
          have hzCode :
              Godel.positiveTupleCode (m + 1)
                  (Delta0Formula.val (snoc params zU)) ∈
                    relationIndex.1 := by
            simpa only [Delta0Formula.val_snoc,
              Godel.positiveTupleCode_snoc, p,
              positiveTupleCodeLCarrier, zU] using hzPair
          have hzMinimal := hminimal zU hzCode
          have hzEq :
              (⟨zU.1, mem_L_of_mem zU.2 U.2⟩ : LCarrier.{u}) = z :=
            Subtype.ext rfl
          simpa only [hzEq] using hzMinimal
  have hyStep :
      y.1 ∈ (aritySeparatedFormulaSkolemStep seed U hU phi).1 := by
    exact (mem_unionLCarrier_iff seed
      (aritySeparatedFormulaSkolemSelection seed U hU phi) y).mpr
        (Or.inr hySelection)
  have hySat :
      FOFormula.Satisfies (zfCarrierMem U.1) phi (snoc params yU) := by
    apply (Godel.mem_boundedSatisfactionRelation_iff
      U.1 hU phi (snoc params yU)).mp
    exact hyCode
  refine ⟨yU, ?_, hySat⟩
  rw [← hyEq]
  exact hyStep

end

end Constructible.Model
