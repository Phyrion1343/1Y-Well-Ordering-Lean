/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalSkolemSelection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CodedSatisfaction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentSkolemHull
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaSyntaxCode

/-!
# Skolem witness-selection primitives

This file constructs one set-valued step used in the standard Skolem-hull
argument. Given a seed, an ambient constructible set `U`, and set-sized
families of internally represented relations and parameter-prefix codes, the
step adjoins their canonical least witnesses. The selected witnesses are an
actual member of `L`, obtained by Separation with one fixed first-order
formula.

This file does not yet enumerate every first-order formula, iterate the
selection step through omega, internalize that sequence by Replacement, or
prove that its union is fully elementary. Those are separate obligations for
a full cardinal-controlled Skolem hull. In particular, closure under every
relation in the unrestricted rudimentary closure of `U` is not a substitute:
nullary singleton relations would force the alleged hull to contain all of
`U`. The standard continuation must use the countable formula syntax,
formula-by-formula canonical witnesses, omega iteration, and the
Tarski--Vaught criterion.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## A fixed formula selecting a set-sized family of witnesses -/

/-- The graph predicate with arbitrary coordinates in a larger context. -/
def graphRelAt {n : Nat} (relation x y : Fin n) : FOFormula n :=
  FOFormula.rename ![relation, x, y] graphRelFormula

@[simp]
theorem satisfies_graphRelAt {n : Nat} (relation x y : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (graphRelAt relation x y) s ↔
      GraphRel (s relation) (s x) (s y) := by
  rw [graphRelAt, FOFormula.satisfies_rename,
    satisfies_graphRelFormula]
  have hassign :
      (fun i => s (![relation, x, y] i)) =
        ![s relation, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  have h0 := congrFun hassign (0 : Fin 3)
  have h1 := congrFun hassign (1 : Fin 3)
  have h2 := congrFun hassign (2 : Fin 3)
  change s (![relation, x, y] 0) = s relation at h0
  change s (![relation, x, y] 1) = s x at h1
  change s (![relation, x, y] 2) = s y at h2
  simp only [h0, h1, h2]

/-- In the context `[U, relations, prefixes, order, y, relation]`, assert
that `y` is the canonical least nullary witness belonging to `relation`.
-/
def nullaryRudimentaryWitnessFormula : FOFormula 6 :=
  .conj
    (.mem (4 : Fin 6) (5 : Fin 6))
    (.all
      (FOFormula.imp
        (.conj
          (.mem (6 : Fin 7) (0 : Fin 7))
          (.mem (6 : Fin 7) (5 : Fin 7)))
        (.neg (graphRelAt (3 : Fin 7) (6 : Fin 7) (4 : Fin 7)))))

/-- In the context
`[U, relations, prefixes, order, y, relation, prefix]`, assert that `y` is
the canonical least member of the `prefix`-fiber of `relation`.
-/
def positiveRudimentaryWitnessFormula : FOFormula 7 :=
  .conj
    (.mem (6 : Fin 7) (2 : Fin 7))
    (.conj
      (graphRelAt (5 : Fin 7) (4 : Fin 7) (6 : Fin 7))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (7 : Fin 8) (0 : Fin 8))
            (graphRelAt (5 : Fin 8) (7 : Fin 8) (6 : Fin 8)))
          (.neg (graphRelAt (3 : Fin 8) (7 : Fin 8) (4 : Fin 8))))))

/-- Layout `[U, relations, prefixes, order, y]`.  The formula says that some
`relation ∈ relations` canonically selects `y`, either as a nullary witness or
from a fiber indexed by a member of `prefixes`.
-/
def rudimentaryWitnessSelectionFormula : FOFormula 5 :=
  .ex
    (.conj
      (.mem (5 : Fin 6) (1 : Fin 6))
      (.disj nullaryRudimentaryWitnessFormula
        (.ex positiveRudimentaryWitnessFormula)))

@[simp]
theorem satisfies_nullaryRudimentaryWitnessFormula
    (U relations prefixes order y relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem nullaryRudimentaryWitnessFormula
        ![U, relations, prefixes, order, y, relation] ↔
      y.1 ∈ relation.1 ∧
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
          ¬ GraphRel order z y := by
  simp only [nullaryRudimentaryWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt]
  constructor
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hzU hzRelation
    have hz := hminimal z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation] z =
        ![U, relations, prefixes, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl] at hz
    exact hz ⟨hzU, hzRelation⟩
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation] z =
        ![U, relations, prefixes, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl]
    intro hz
    exact hminimal z hz.1 hz.2

@[simp]
theorem satisfies_positiveRudimentaryWitnessFormula
    (U relations prefixes order y relation p : LCarrier.{u}) :
    FOFormula.Satisfies LMem positiveRudimentaryWitnessFormula
        ![U, relations, prefixes, order, y, relation, p] ↔
      p.1 ∈ prefixes.1 ∧ GraphRel relation y p ∧
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
          GraphRel relation z p → ¬ GraphRel order z y := by
  simp only [positiveRudimentaryWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt]
  constructor
  · rintro ⟨hp, hgraph, hminimal⟩
    refine ⟨hp, hgraph, ?_⟩
    intro z hzU hzGraph
    have hz := hminimal z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation, p] z =
        ![U, relations, prefixes, order, y, relation, p, z] by
          funext i
          fin_cases i <;> rfl] at hz
    exact hz ⟨hzU, hzGraph⟩
  · rintro ⟨hp, hgraph, hminimal⟩
    refine ⟨hp, hgraph, ?_⟩
    intro z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation, p] z =
        ![U, relations, prefixes, order, y, relation, p, z] by
          funext i
          fin_cases i <;> rfl]
    intro hz
    exact hminimal z hz.1 hz.2

@[simp]
theorem satisfies_rudimentaryWitnessSelectionFormula
    (U relations prefixes order y : LCarrier.{u}) :
    FOFormula.Satisfies LMem rudimentaryWitnessSelectionFormula
        ![U, relations, prefixes, order, y] ↔
      ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
        ((y.1 ∈ relation.1 ∧
            ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
              ¬ GraphRel order z y) ∨
          ∃ p : LCarrier.{u}, p.1 ∈ prefixes.1 ∧
            GraphRel relation y p ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                GraphRel relation z p → ¬ GraphRel order z y) := by
  simp only [rudimentaryWitnessSelectionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj]
  apply exists_congr
  intro relation
  have hrelationAssignment :
      snoc ![U, relations, prefixes, order, y] relation =
        ![U, relations, prefixes, order, y, relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hrelationAssignment,
    satisfies_nullaryRudimentaryWitnessFormula]
  apply and_congr_right
  intro _hrelation
  apply or_congr Iff.rfl
  apply exists_congr
  intro p
  have hpAssignment :
      snoc ![U, relations, prefixes, order, y, relation] p =
        ![U, relations, prefixes, order, y, relation, p] := by
    funext i
    fin_cases i <;> rfl
  rw [hpAssignment, satisfies_positiveRudimentaryWitnessFormula]

/-- The actual constructible set selected from one relation family and one
prefix-code family.  This operation is generic; controlled hulls instantiate
`relations` by the singleton containing one compiled formula relation, never
by all of `rudimentaryClosure U`.
-/
noncomputable def canonicalWitnessSelection
    (U relations prefixes : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    rudimentaryWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U)

@[simp]
theorem mem_canonicalWitnessSelection_iff
    (U relations prefixes y : LCarrier.{u}) :
    y.1 ∈ (canonicalWitnessSelection U relations prefixes).1 ↔
      y.1 ∈ U.1 ∧
        FOFormula.Satisfies LMem rudimentaryWitnessSelectionFormula
          ![U, relations, prefixes, canonicalWitnessOrder U, y] := by
  exact Classical.choose_spec (exists_separationLCarrier
    rudimentaryWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U) y

/-- Retain the seed and adjoin the witnesses selected from the supplied
set-sized relation and prefix families.
-/
noncomputable def witnessSelectionStep
    (seed U relations prefixes : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier seed (canonicalWitnessSelection U relations prefixes)

theorem seed_subset_witnessSelectionStep
    (seed U relations prefixes : LCarrier.{u}) :
    seed.1 ⊆ (witnessSelectionStep seed U relations prefixes).1 := by
  intro x hx
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx seed.2⟩
  exact (mem_unionLCarrier_iff seed
    (canonicalWitnessSelection U relations prefixes) xL).mpr (Or.inl hx)

theorem witnessSelectionStep_subset
    {seed U : LCarrier.{u}} (hseed : seed.1 ⊆ U.1) :
    ∀ relations prefixes : LCarrier.{u},
      (witnessSelectionStep seed U relations prefixes).1 ⊆ U.1 := by
  intro relations prefixes x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx
      (witnessSelectionStep seed U relations prefixes).2⟩
  rcases (mem_unionLCarrier_iff seed
      (canonicalWitnessSelection U relations prefixes) xL).mp hx with
    hxSeed | hxSelected
  · exact hseed hxSeed
  · exact (mem_canonicalWitnessSelection_iff
      U relations prefixes xL).mp hxSelected |>.1

end

end Constructible.Model
