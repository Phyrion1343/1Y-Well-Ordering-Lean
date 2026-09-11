/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FullSkolemHull

/-!
# A one-formula witness-adjoining approximation

For one externally fixed formula `phi`, an ambient transitive constructible
set `U`, and a constructible seed contained in `U`, this file constructs a
set which contains a canonical witness for every parameter tuple from the
seed for which `phi` has a witness in `U`.

The compiled relation family is a singleton.  When the parameter arity is
positive, its prefix family is exactly the set of tuple codes over the seed;
the nullary case uses the existing nullary branch of
`canonicalWitnessSelection`.  The generic selector used here has no arity
tag, however, so for positive arity its nullary disjunct can add at most one
extra tuple-code element from the compiled relation.  The witness theorem
below remains correct, but this operation is therefore not the exact total
Skolem function of the textbook construction and must not be used for its
cardinality calculation until the two selector branches are separated.

This construction does not close under all rudimentary relations.  It is one
formula witness-adjoining approximation only: no omega iteration,
elementarity conclusion, exact Skolem-function characterization, or cardinal
bound is asserted here.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The relation and prefix families -/

/-- The compiled satisfaction relation, viewed as an element of `L`. -/
def formulaSkolemRelation
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : LCarrier.{u} :=
  rudimentaryRelationLCarrier U
    (Godel.boundedSatisfactionIndex U.1 hU phi)

@[simp]
theorem formulaSkolemRelation_val
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    (formulaSkolemRelation U hU phi).1 =
      Godel.boundedSatisfactionRelation U.1 hU phi :=
  rfl

/-- The singleton containing the relation compiled from `phi`. -/
def formulaSkolemRelationFamily
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : LCarrier.{u} :=
  singletonLCarrier (formulaSkolemRelation U hU phi)

@[simp]
theorem mem_formulaSkolemRelationFamily_iff
    (U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) (relation : LCarrier.{u}) :
    relation.1 ∈ (formulaSkolemRelationFamily U hU phi).1 ↔
      relation = formulaSkolemRelation U hU phi := by
  exact mem_singletonLCarrier_iff (formulaSkolemRelation U hU phi) relation

/--
Codes of seed parameter tuples of arity `n`.  There is no nonempty tuple code
for arity zero, so that case supplies the empty prefix family and is handled
by the nullary relation branch.
-/
def formulaSkolemPrefixFamily (seed : LCarrier.{u}) : Nat → LCarrier.{u}
  | 0 => emptyLCarrier
  | n + 1 =>
      rudimentaryRelationLCarrier seed
        ⟨Godel.positiveTupleSpace seed.1 n,
          Godel.positiveTupleSpace_mem_rudimentaryClosure seed.1 n⟩

@[simp]
theorem formulaSkolemPrefixFamily_zero (seed : LCarrier.{u}) :
    formulaSkolemPrefixFamily seed 0 = emptyLCarrier :=
  rfl

@[simp]
theorem formulaSkolemPrefixFamily_succ_val
    (seed : LCarrier.{u}) (n : Nat) :
    (formulaSkolemPrefixFamily seed (n + 1)).1 =
      Godel.positiveTupleSpace seed.1 n :=
  rfl

/-! ## The actual one-formula step -/

/-- Retain `seed` and adjoin a set containing canonical `phi`-witnesses. -/
def formulaSkolemStep
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : LCarrier.{u} :=
  witnessSelectionStep seed U
    (formulaSkolemRelationFamily U hU phi)
    (formulaSkolemPrefixFamily seed n)

/-- The one-formula step retains every member of the seed. -/
theorem seed_subset_formulaSkolemStep
    (seed U : LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    seed.1 ⊆ (formulaSkolemStep seed U hU phi).1 := by
  exact seed_subset_witnessSelectionStep seed U
    (formulaSkolemRelationFamily U hU phi)
    (formulaSkolemPrefixFamily seed n)

/-- If the seed lies in `U`, the one-formula step still lies in `U`. -/
theorem formulaSkolemStep_subset
    {seed U : LCarrier.{u}} (hU : U.1.IsTransitive)
    (hseed : seed.1 ⊆ U.1)
    {n : Nat} (phi : FOFormula (n + 1)) :
    (formulaSkolemStep seed U hU phi).1 ⊆ U.1 := by
  exact witnessSelectionStep_subset hseed
    (formulaSkolemRelationFamily U hU phi)
    (formulaSkolemPrefixFamily seed n)

/-! ## Tarski witness closure for the fixed formula -/

private theorem positiveTupleCode_zero_snoc
    {U : ZFSet.{u}} (params : Tuple (ZFCarrier U) 0)
    (x : ZFCarrier U) :
    Godel.positiveTupleCode 0
        (Delta0Formula.val (snoc params x)) = x.1 := by
  change (snoc params x 0).1 = x.1
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, snoc_last]

/--
Every seed-parameter instance of `phi` which has a witness in `U` has a
witness in the one-formula step.  Satisfaction on both sides is the ordinary
Tarskian semantics of the set-sized membership structure on `U`.
-/
theorem exists_witness_mem_formulaSkolemStep
    {seed U : LCarrier.{u}} (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier U.1) n)
    (hparams : ∀ i, (params i).1 ∈ seed.1)
    (hexists : ∃ x : ZFCarrier U.1,
      FOFormula.Satisfies (zfCarrierMem U.1) phi (snoc params x)) :
    ∃ y : ZFCarrier U.1,
      y.1 ∈ (formulaSkolemStep seed U hU phi).1 ∧
        FOFormula.Satisfies (zfCarrierMem U.1) phi (snoc params y) := by
  let relationIndex := Godel.boundedSatisfactionIndex U.1 hU phi
  let relation := formulaSkolemRelation U hU phi
  let relations := formulaSkolemRelationFamily U hU phi
  let prefixes := formulaSkolemPrefixFamily seed n
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
  have hrelationMem : relation.1 ∈ relations.1 := by
    exact (mem_formulaSkolemRelationFamily_iff U hU phi relation).mpr rfl
  have hySelection :
      y.1 ∈ (canonicalWitnessSelection U relations prefixes).1 := by
    apply (mem_canonicalWitnessSelection_iff U relations prefixes y).mpr
    refine ⟨hyU, ?_⟩
    apply (satisfies_rudimentaryWitnessSelectionFormula
      U relations prefixes (canonicalWitnessOrder U) y).mpr
    refine ⟨relation, hrelationMem, ?_⟩
    cases n with
    | zero =>
        left
        refine ⟨?_, ?_⟩
        · have hyCode' : yU.1 ∈ relationIndex.1 := by
            simpa only [positiveTupleCode_zero_snoc] using hyCode
          change y.1 ∈ relation.1
          rw [hyEq]
          change yU.1 ∈ relationIndex.1
          exact hyCode'
        · intro z hzU hzRelation
          let zU : ZFCarrier U.1 := ⟨z.1, hzU⟩
          have hzCode :
              Godel.positiveTupleCode 0
                  (Delta0Formula.val (snoc params zU)) ∈ relationIndex.1 := by
            change z.1 ∈ relationIndex.1
            change z.1 ∈ relationIndex.1 at hzRelation
            exact hzRelation
          have hzMinimal := hminimal zU hzCode
          have hzEq :
              (⟨zU.1, mem_L_of_mem zU.2 U.2⟩ : LCarrier.{u}) = z :=
            Subtype.ext rfl
          simpa only [hzEq] using hzMinimal
    | succ m =>
        right
        let p : LCarrier.{u} := positiveTupleCodeLCarrier U params
        refine ⟨p, ?_, ?_, ?_⟩
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
                  (Delta0Formula.val (snoc params zU)) ∈ relationIndex.1 := by
            simpa only [Delta0Formula.val_snoc,
              Godel.positiveTupleCode_snoc, p,
              positiveTupleCodeLCarrier, zU] using hzPair
          have hzMinimal := hminimal zU hzCode
          have hzEq :
              (⟨zU.1, mem_L_of_mem zU.2 U.2⟩ : LCarrier.{u}) = z :=
            Subtype.ext rfl
          simpa only [hzEq] using hzMinimal
  have hyStep : y.1 ∈ (formulaSkolemStep seed U hU phi).1 := by
    exact (mem_unionLCarrier_iff seed
      (canonicalWitnessSelection U relations prefixes) y).mpr
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
