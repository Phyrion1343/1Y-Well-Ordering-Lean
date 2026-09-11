/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessIteration
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GeneralCollapseInternalization

/-!
# The full textbook E elementary hull

For constructible parameters `kappa` and `x`, choose a condensation reflection
level containing both.  Start with the textbook seed

`kappa union {x}`,

represented exactly by `adjoinLCarrier kappa x`, and iterate the simultaneous
textbook `E` witness operation through the internal natural numbers.
Replacement collects the finite stages, and their internal union is fully
elementary in the chosen constructible level.

The construction of the elementary hull is independent of its cardinal
bound.  The final assembly into `CardinalControlledHull` therefore keeps the
remaining smallness premise visible as an actual internal injection from this
specific hull into `kappa`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The chosen ambient level and the textbook seed -/

/-- A condensation reflection level containing both displayed parameters. -/
noncomputable def textbookEElementaryHullTheta
    (kappa x : LCarrier.{u}) : Ordinal.{u} :=
  Classical.choose
    (exists_condensationReflectionLevel_containing_pair kappa x)

theorem textbookEElementaryHullTheta_spec
    (kappa x : LCarrier.{u}) :
    IsCondensationReflectionLevel
        (textbookEElementaryHullTheta kappa x) ∧
      kappa.1 ∈ LStageZF (textbookEElementaryHullTheta kappa x) ∧
      x.1 ∈ LStageZF (textbookEElementaryHullTheta kappa x) :=
  Classical.choose_spec
    (exists_condensationReflectionLevel_containing_pair kappa x)

/-- The selected constructible level, packaged as an actual member of `L`. -/
noncomputable def textbookEElementaryHullAmbient
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  stageLCarrier (textbookEElementaryHullTheta kappa x)

/--
The initial textbook hull seed is exactly `kappa union {x}`.  The existing
`adjoinLCarrier` definition writes the binary union in the opposite order,
which is extensionally the same set.
-/
def textbookEElementaryHullSeed
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  adjoinLCarrier kappa x

/-- Every member of the seed lies in the selected ambient level. -/
theorem textbookEElementaryHullSeed_subset_ambient
    (kappa x : LCarrier.{u}) :
    (textbookEElementaryHullSeed kappa x).1 ⊆
      (textbookEElementaryHullAmbient kappa x).1 := by
  intro z hz
  let zL : LCarrier.{u} :=
    ⟨z, mem_L_of_mem hz (textbookEElementaryHullSeed kappa x).2⟩
  rcases (mem_adjoinLCarrier_iff kappa x zL).mp hz with
    hzx | hzkappa
  · have hzEq : z = x.1 := congrArg Subtype.val hzx
    simpa only [textbookEElementaryHullAmbient, stageLCarrier_val,
      hzEq] using (textbookEElementaryHullTheta_spec kappa x).2.2
  · change z ∈ LStageZF (textbookEElementaryHullTheta kappa x)
    exact
      (LStageZF_isTransitive
        (textbookEElementaryHullTheta kappa x)).mem_trans
          hzkappa
          (textbookEElementaryHullTheta_spec kappa x).2.1

/-- The empty set belongs to the selected nonzero limit level. -/
theorem empty_mem_textbookEElementaryHullAmbient
    (kappa x : LCarrier.{u}) :
    emptyLCarrier.1 ∈ (textbookEElementaryHullAmbient kappa x).1 := by
  change (∅ : ZFSet.{u}) ∈
    LStageZF (textbookEElementaryHullTheta kappa x)
  exact empty_mem_LStageZF_of_isSuccLimit
    (textbookEElementaryHullTheta_spec kappa x).1.1

/-! ## The full elementary hull -/

/-- The internal omega union of all simultaneous textbook E witness stages. -/
noncomputable def textbookEElementaryHull
    (kappa x : LCarrier.{u}) : LCarrier.{u} :=
  textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)

/-- The full hull stays inside its selected constructible level. -/
theorem textbookEElementaryHull_subset_ambient
    (kappa x : LCarrier.{u}) :
    (textbookEElementaryHull kappa x).1 ⊆
      LStageZF (textbookEElementaryHullTheta kappa x) := by
  simpa only [textbookEElementaryHull,
    textbookEElementaryHullAmbient, stageLCarrier_val] using
      textbookEUniformWitnessOmegaUnion_subset
        (textbookEElementaryHullSeed kappa x)
        (textbookEElementaryHullAmbient kappa x)
        (textbookEElementaryHullSeed_subset_ambient kappa x)
        (empty_mem_textbookEElementaryHullAmbient kappa x)

/-- Every member of `kappa` belongs to the full hull. -/
theorem kappa_subset_textbookEElementaryHull
    (kappa x : LCarrier.{u}) :
    kappa.1 ⊆ (textbookEElementaryHull kappa x).1 := by
  intro z hz
  let zL : LCarrier.{u} := ⟨z, mem_L_of_mem hz kappa.2⟩
  apply seed_subset_textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)
  exact (mem_adjoinLCarrier_iff kappa x zL).mpr (Or.inr hz)

/-- The distinguished subset parameter itself belongs to the full hull. -/
theorem x_mem_textbookEElementaryHull
    (kappa x : LCarrier.{u}) :
    x.1 ∈ (textbookEElementaryHull kappa x).1 := by
  apply seed_subset_textbookEUniformWitnessOmegaUnion
    (textbookEElementaryHullSeed kappa x)
    (textbookEElementaryHullAmbient kappa x)
  exact (mem_adjoinLCarrier_iff kappa x x).mpr (Or.inl rfl)

/-- The concrete omega union is closed under every textbook E witness task. -/
theorem textbookEElementaryHull_closesUnderTextbookEWitnesses
    (kappa x : LCarrier.{u}) :
    ClosesUnderTextbookEWitnesses
      (textbookEElementaryHull kappa x).1
      (LStageZF (textbookEElementaryHullTheta kappa x)) := by
  intro arity code params hparams hexists
  exact
    textbookEUniformWitnessOmegaUnion_closes
      (textbookEElementaryHullSeed kappa x)
      (textbookEElementaryHullAmbient kappa x)
      (n := arity) code params hparams hexists

/--
The internally constructed omega union is a fully elementary substructure of
the selected constructible level.
-/
theorem textbookEElementaryHull_satisfactionAbsolute
    (kappa x : LCarrier.{u}) :
    SatisfactionAbsolute
      ((textbookEElementaryHull kappa x).1 : Set ZFSet.{u})
      (LStageZF (textbookEElementaryHullTheta kappa x) :
        Set ZFSet.{u}) := by
  exact satisfactionAbsolute_of_closesUnderTextbookEWitnesses
    (textbookEElementaryHull_subset_ambient kappa x)
    (textbookEElementaryHull_closesUnderTextbookEWitnesses kappa x)

/-! ## Condensation and the explicit cardinal-smallness interface -/

/-- Package the concrete elementary omega union as a condensation hull. -/
theorem textbookEElementaryCondensationHull
    (kappa x : LCarrier.{u}) :
    CondensationHull
      (textbookEElementaryHullTheta kappa x)
      (textbookEElementaryHull kappa x).1 :=
  CondensationHull.of_elementary
    (textbookEElementaryHullTheta_spec kappa x).1
    (textbookEElementaryHull_subset_ambient kappa x)
    (textbookEElementaryHull_satisfactionAbsolute kappa x)

/--
If the concrete elementary hull has a genuine internal injection into
`kappa`, it supplies a `CardinalControlledHull`.  No cardinal smallness is
inferred from an external set cardinality.
-/
theorem nonempty_cardinalControlledHull_of_textbookEElementaryHull_injects
    (kappa x : LCarrier.{u})
    (hsmall :
      Injects LMem (textbookEElementaryHull kappa x) kappa) :
    Nonempty (CardinalControlledHull kappa x) := by
  rcases
      (textbookEElementaryCondensationHull kappa x)
        |>.exists_internalizedCollapse with
    ⟨collapseData, _⟩
  exact ⟨{
    theta := textbookEElementaryHullTheta kappa x
    domain := textbookEElementaryHull kappa x
    hull := textbookEElementaryCondensationHull kappa x
    collapseData := collapseData
    bound_subset := kappa_subset_textbookEElementaryHull kappa x
    element_mem := x_mem_textbookEElementaryHull kappa x
    small := hsmall
  }⟩

/--
Exact all-subsets interface for the remaining cardinal estimate.  For an
infinite internal cardinal, the intended caller supplies `hkappa` and
`omega ⊆ kappa` separately when applying the later GCH bridge; this theorem
uses precisely the still-missing injection for each `x ⊆ kappa`.
-/
theorem hasCardinalControlledHulls_of_textbookEElementaryHull_injects
    (kappa : LCarrier.{u})
    (hsmall : ∀ x : LCarrier.{u},
      IsSubsetOf LMem x kappa →
        Injects LMem (textbookEElementaryHull kappa x) kappa) :
    HasCardinalControlledHulls kappa := by
  intro x hx
  exact
    nonempty_cardinalControlledHull_of_textbookEElementaryHull_injects
      kappa x (hsmall x hx)

end

end Constructible.ContinuumFormula
