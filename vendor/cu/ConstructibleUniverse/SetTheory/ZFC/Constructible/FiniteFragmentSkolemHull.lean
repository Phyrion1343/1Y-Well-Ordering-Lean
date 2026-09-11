/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteFragmentElementarity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaGodel
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Infinity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement

/-!
# Full elementarity and internally represented omega unions

The first part of this file upgrades the one-formula Tarski--Vaught interface
from `FiniteFragmentElementarity` to an external quantification over every
first-order formula.  This is the elementarity notion required by a genuine
Mostowski condensation theorem; closure under one fixed finite fragment is
not substituted for full elementarity.

The second part isolates the internal set construction used by a Skolem-hull
argument.  If one fixed first-order formula uniformly defines an omega-indexed
family of constructible sets, Replacement produces an actual member of `L`
whose members are precisely that family.  Its union is therefore an actual
`ZFSet` in `L`, rather than an external `Set ZFSet`.

This file deliberately does not assert that the full Skolem iteration has
already been constructed.  The implication from closure under all
rudimentary relation sets to elementarity is useful as a semantic comparison,
but that closure predicate is too strong for a cardinal-controlled hull:
nullary singleton relations force the smaller carrier to contain all of `U`.
Consequently a genuine Skolem construction must enumerate only the compiled
relations of first-order formulas; it must not iterate the unrestricted
predicate below.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/-! ## Full Tarski--Vaught closure -/

/-- Closure under witnesses for every first-order formula and all of its
subformulas.  Formula syntax is quantified over externally here. -/
def ClosesWithinAll (small big : Set ZFSet.{u}) : Prop :=
  forall {n : Nat} (phi : FOFormula n), ClosesWithin small big phi

/-- Satisfaction is absolute between `small` and `big` for every formula
whose free parameters lie in `small`. -/
def SatisfactionAbsolute (small big : Set ZFSet.{u}) : Prop :=
  forall {n : Nat} (phi : FOFormula n) (s : Tuple ZFSet.{u} n),
    (forall i, s i ∈ small) ->
      (Model.SatisfiesIn small phi s <-> Model.SatisfiesIn big phi s)

/-- Full witness closure implies absoluteness for every first-order formula. -/
theorem satisfactionAbsolute_of_closesWithinAll
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big)
    (hclose : ClosesWithinAll small big) :
    SatisfactionAbsolute small big := by
  intro n phi s hs
  exact satisfiesIn_iff_of_closesWithin hsubset phi (hclose phi) s hs

/-- If satisfaction of every formula is absolute, then `small` contains the
required Tarski--Vaught witnesses for every existential subformula. -/
theorem closesWithinAll_of_satisfactionAbsolute
    {small big : Set ZFSet.{u}}
    (habsolute : SatisfactionAbsolute small big) :
    ClosesWithinAll small big := by
  intro n phi
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ⟨ihPhi, ihPsi⟩
  | ex phi ih =>
      refine ⟨ih, ?_⟩
      intro s hs hbig
      have hsmall : Model.SatisfiesIn small (.ex phi) s :=
        (habsolute (.ex phi) s hs).mpr hbig
      rcases hsmall with ⟨x, hxSmall, hxFormula⟩
      refine ⟨x, hxSmall, ?_⟩
      apply (habsolute phi (snoc s x) ?_).mp hxFormula
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxSmall
      · simpa using hs j

/-- Full Tarski--Vaught closure is equivalent to full satisfaction
absoluteness once the smaller carrier is included in the larger one. -/
theorem closesWithinAll_iff_satisfactionAbsolute
    {small big : Set ZFSet.{u}} (hsubset : small ⊆ big) :
    ClosesWithinAll small big <-> SatisfactionAbsolute small big := by
  constructor
  · exact satisfactionAbsolute_of_closesWithinAll hsubset
  · exact closesWithinAll_of_satisfactionAbsolute

/-- Full witness closure supplies the extensionality needed for a Mostowski
collapse whenever the ambient carrier is transitive. -/
theorem restricted_extensionality_of_closesWithinAll
    {small big : Set ZFSet.{u}}
    (hsubset : small ⊆ big)
    (htrans : forall x : ZFSet.{u}, x ∈ big ->
      forall z : ZFSet.{u}, z ∈ x -> z ∈ big)
    (hclose : ClosesWithinAll small big)
    {x y : ZFSet.{u}} (hx : x ∈ small) (hy : y ∈ small)
    (hsame : forall z : ZFSet.{u}, z ∈ small -> (z ∈ x <-> z ∈ y)) :
    x = y :=
  restricted_extensionality_of_closesWithin hsubset htrans
    (hclose distinguishingMemberFormula) hx hy hsame

/-! ## Full formula closure through rudimentary relation sets -/

/--
Witness closure stated uniformly for every relation set in
`rudimentaryClosure U`.  A relation consumes the code of a nonempty tuple;
the final coordinate is the candidate witness and the preceding coordinates
are parameters from `small`.

This condition is intentionally stronger than closure under a syntactically
enumerated list of formulas.  `Godel.formulaRep` shows that it covers every
first-order formula over a transitive `U`, so the elementarity implication
below is correct.  It is not a viable small-hull invariant: because singleton
relations occur in `rudimentaryClosure U`, its nullary case implies
`U ⊆ small`; see `RudimentaryWitnessClosureDegenerate`.
-/
def ClosesUnderRudimentaryWitnesses
    (small : Set ZFSet.{u}) (U : ZFSet.{u}) : Prop :=
  forall {n : Nat} (relation : ZFSet.{u}),
    relation ∈ Godel.rudimentaryClosure U ->
      forall params : Tuple (ZFCarrier U) n,
        (forall i, (params i).1 ∈ small) ->
          (∃ x : ZFCarrier U,
            Godel.positiveTupleCode n
              (Delta0Formula.val (snoc params x)) ∈ relation) ->
          ∃ x : ZFCarrier U, x.1 ∈ small ∧
            Godel.positiveTupleCode n
              (Delta0Formula.val (snoc params x)) ∈ relation

/-- Closure under all rudimentary relation sets supplies full Tarski--Vaught
closure for every first-order formula.  This is the bridge which avoids an
object-language enumeration of formula syntax. -/
theorem closesWithinAll_of_closesUnderRudimentaryWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hU : U.IsTransitive) (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderRudimentaryWitnesses small U) :
    ClosesWithinAll small (U : Set ZFSet.{u}) := by
  intro n phi
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ⟨ihPhi, ihPsi⟩
  | @ex m phi ih =>
      refine ⟨ih, ?_⟩
      intro s hs hbig
      rcases hbig with ⟨x, hxU, hxFormula⟩
      let params : Tuple (ZFCarrier U) m :=
        fun i => ⟨s i, hsubset (hs i)⟩
      let xU : ZFCarrier U := ⟨x, hxU⟩
      let rep := Godel.RelationRep.formulaRep U hU phi
      have hxCarrier :
          FOFormula.Satisfies (zfCarrierMem U) phi (snoc params xU) := by
        apply (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) phi (snoc params xU)).mpr
        simpa only [Model.subtypeVal_snoc, params, xU] using hxFormula
      have hxCode :
          Godel.positiveTupleCode m
              (Delta0Formula.val (snoc params xU)) ∈ rep.set :=
        (rep.correct (snoc params xU)).mpr hxCarrier
      rcases hclose rep.set rep.set_mem params
          (fun i => by simpa only [params] using hs i) ⟨xU, hxCode⟩ with
        ⟨w, hwSmall, hwCode⟩
      refine ⟨w.1, hwSmall, ?_⟩
      have hwCarrier :
          FOFormula.Satisfies (zfCarrierMem U) phi (snoc params w) :=
        (rep.correct (snoc params w)).mp hwCode
      have hwRaw :=
        (Model.satisfies_subtype_iff_satisfiesIn
          (U : Set ZFSet.{u}) phi (snoc params w)).mp hwCarrier
      simpa only [Model.subtypeVal_snoc, params] using hwRaw

/-- The same rudimentary closure hypothesis, stated directly as full
satisfaction absoluteness. -/
theorem satisfactionAbsolute_of_closesUnderRudimentaryWitnesses
    {small : Set ZFSet.{u}} {U : ZFSet.{u}}
    (hU : U.IsTransitive) (hsubset : small ⊆ (U : Set ZFSet.{u}))
    (hclose : ClosesUnderRudimentaryWitnesses small U) :
    SatisfactionAbsolute small (U : Set ZFSet.{u}) :=
  satisfactionAbsolute_of_closesWithinAll hsubset
    (closesWithinAll_of_closesUnderRudimentaryWitnesses hU hsubset hclose)

/-! ## A uniform omega-indexed Replacement interface -/

namespace Model

open FiniteSequenceZF

local notation "LMem" => lCarrierMem

/-- The constructible carrier corresponding to the von Neumann code of `n`. -/
noncomputable def natLCarrier (n : Nat) : LCarrier.{u} :=
  ⟨natCode n, natCode_mem_L n⟩

@[simp]
theorem natLCarrier_val (n : Nat) : (natLCarrier n).1 = natCode n :=
  rfl

/--
Data showing that one fixed object-language formula uniformly defines an
omega-indexed family.  The formula layout is `[index, value]`.

This is intentionally stronger than merely giving an external function
`Nat -> LCarrier`: the uniform formula is exactly what permits internal
Replacement over `omega`.
-/
structure UniformOmegaFamilySpec where
  formula : FOFormula 2
  value : Nat -> LCarrier.{u}
  realizes : forall (n : Nat) (y : LCarrier.{u}),
    FOFormula.Satisfies LMem formula ![natLCarrier n, y] <-> y = value n

private theorem snoc_snoc_empty_eq_pair
    (x y : LCarrier.{u}) :
    snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y = ![x, y] := by
  funext i
  fin_cases i <;> rfl

/-- Replacement can be applied to every uniform omega-family specification. -/
theorem exists_uniformOmegaFamily (spec : UniformOmegaFamilySpec.{u}) :
    exists family : LCarrier.{u}, forall y : LCarrier.{u},
      y.1 ∈ family.1 <-> exists n : Nat, y = spec.value n := by
  let noParams : Tuple LCarrier.{u} 0 := fun i => Fin.elim0 i
  have hfun : forall x : LCarrier.{u}, x.1 ∈ omegaLCarrier.1 ->
      ∃! y : LCarrier.{u},
        FOFormula.Satisfies LMem spec.formula
          (snoc (snoc noParams x) y) := by
    intro x hx
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x.1).mp hx with
      ⟨n, hxCode⟩
    have hxNat : x = natLCarrier n := Subtype.ext hxCode
    refine ⟨spec.value n, ?_, ?_⟩
    · change FOFormula.Satisfies LMem spec.formula
        (snoc (snoc noParams x) (spec.value n))
      rw [show snoc (snoc noParams x) (spec.value n) =
          ![natLCarrier n, spec.value n] by
        simpa only [noParams, hxNat] using
          snoc_snoc_empty_eq_pair (natLCarrier n) (spec.value n)]
      exact (spec.realizes n (spec.value n)).mpr rfl
    · intro y hy
      apply (spec.realizes n y).mp
      rw [← show snoc (snoc noParams x) y = ![natLCarrier n, y] by
        simpa only [noParams, hxNat] using
          snoc_snoc_empty_eq_pair (natLCarrier n) y]
      exact hy
  rcases exists_replacementLCarrier spec.formula noParams omegaLCarrier hfun with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro y
  rw [hfamily]
  constructor
  · rintro ⟨x, hxOmega, hxy⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x.1).mp hxOmega with
      ⟨n, hxCode⟩
    have hxNat : x = natLCarrier n := Subtype.ext hxCode
    refine ⟨n, (spec.realizes n y).mp ?_⟩
    rw [← show snoc (snoc noParams x) y = ![natLCarrier n, y] by
      simpa only [noParams, hxNat] using
        snoc_snoc_empty_eq_pair (natLCarrier n) y]
    exact hxy
  · rintro ⟨n, rfl⟩
    refine ⟨natLCarrier n, ?_, ?_⟩
    · change natCode n ∈ Ordinal.omega0.toZFSet
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
        (Ordinal.natCast_lt_omega0 n)
    · change FOFormula.Satisfies LMem spec.formula
        (snoc (snoc noParams (natLCarrier n)) (spec.value n))
      rw [show snoc (snoc noParams (natLCarrier n)) (spec.value n) =
          ![natLCarrier n, spec.value n] by
        simpa only [noParams] using
          snoc_snoc_empty_eq_pair (natLCarrier n) (spec.value n)]
      exact (spec.realizes n (spec.value n)).mpr rfl

/-- The internally represented range selected from Replacement. -/
noncomputable def uniformOmegaFamily
    (spec : UniformOmegaFamilySpec.{u}) : LCarrier.{u} :=
  Classical.choose (exists_uniformOmegaFamily spec)

@[simp]
theorem mem_uniformOmegaFamily_iff
    (spec : UniformOmegaFamilySpec.{u}) (y : LCarrier.{u}) :
    y.1 ∈ (uniformOmegaFamily spec).1 <->
      exists n : Nat, y = spec.value n :=
  Classical.choose_spec (exists_uniformOmegaFamily spec) y

/-- The actual internal union of all values in a uniform omega-family. -/
noncomputable def uniformOmegaUnion
    (spec : UniformOmegaFamilySpec.{u}) : LCarrier.{u} :=
  sUnionLCarrier (uniformOmegaFamily spec)

@[simp]
theorem mem_uniformOmegaUnion_iff
    (spec : UniformOmegaFamilySpec.{u}) (z : LCarrier.{u}) :
    z.1 ∈ (uniformOmegaUnion spec).1 <->
      exists n : Nat, z.1 ∈ (spec.value n).1 := by
  rw [uniformOmegaUnion, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstage, hz⟩
    rcases (mem_uniformOmegaFamily_iff spec stage).mp hstage with
      ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨spec.value n,
      (mem_uniformOmegaFamily_iff spec (spec.value n)).mpr ⟨n, rfl⟩,
      hz⟩

/-- Every stage of a uniform omega-family is contained in its internal union. -/
theorem value_subset_uniformOmegaUnion
    (spec : UniformOmegaFamilySpec.{u}) (n : Nat) :
    (spec.value n).1 ⊆ (uniformOmegaUnion spec).1 := by
  intro z hz
  exact (mem_uniformOmegaUnion_iff spec
    ⟨z, mem_L_of_mem hz (spec.value n).2⟩).mpr ⟨n, hz⟩

/-- A designated seed is contained in the internal omega-union whenever it
is the zeroth value of the uniform family. -/
theorem seed_subset_uniformOmegaUnion
    (spec : UniformOmegaFamilySpec.{u}) (seed : LCarrier.{u})
    (hzero : spec.value 0 = seed) :
    seed.1 ⊆ (uniformOmegaUnion spec).1 := by
  simpa only [hzero] using value_subset_uniformOmegaUnion spec 0

end Model

end ZFC

end Constructible
