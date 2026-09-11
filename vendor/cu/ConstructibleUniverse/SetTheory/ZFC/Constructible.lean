/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module

public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteStageInternalOrder
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaDefinedSet
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Absoluteness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFModel
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFSeparation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFReplacement
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFFunctionGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFOmega
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDefinabilityCode
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteTupleAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookTupleSpaceAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookAtomicAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookProjectionAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookBooleanAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookGraphLookupAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalLiterals
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalAddition
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalMultiplication
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalPower
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeArithmetic
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeDecode
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookSetWellFounded
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPredecessorClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassWellFounded
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassRecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalRecursionBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalPredecessorClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionAbsoluteness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalTextbookRecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDomain
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEKeyDecode
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEParameterizedDomain
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookERecursion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEDefinability
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDfFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefinableRelationEnumeration
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.LStageZFCardinality
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteReflection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteFormulaReflection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookFiniteReflectionL
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.AritySeparatedFormulaSkolemStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteSkolemIteration
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteSkolemOmega
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalSkolemMatrixCode
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPositiveFormulaEnumeration
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookESkolemClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEInternalTasks
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEConstructible
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookESingleWitnessStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryGraphSystem
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ContinuumHypothesis
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Hartogs
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalStageCardinalUnion
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalLimitStageSelector
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalSchroederBernstein
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCantor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.HartogsSuccessor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInfiniteCardinalAbsorption
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalDefZFInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalLStageInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.HartogsLimit
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Condensation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.StandardCondensation
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypePredecessor
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeCanonical
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeUniqueness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeReplacement
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeInduction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalCardinalRepresentativeInterface
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalOrderTypeWitnessConstruction
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CondensationGCHApplication
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.GCHImpliesCH
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFCVEqualsL
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFCVEqualsLGCH
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.CHRelativeConsistency

/-!
# The constructible universe

This directory defines the constructible hierarchy as internally represented `ZFSet`s, proves
that its stages agree with first-order definability, and constructs coherent internal well-orders
of all stages. The membership structure on the constructible universe is consequently a model of
the canonical first-order theory ZFC.

Each stage `LStageZF α` is an actual `ZFSet`; only the union `L` of all ordinal-indexed stages is
represented externally as a `Set ZFSet`. Successor stages use the internally constructed operation
`DefZF`, while limit stages use Replacement followed by internal union.

The proof proceeds through the following interfaces:

* an intrinsically scoped formula syntax and its equivalence with Mathlib's first-order formulas;
* Gödel operations and rudimentary relation graphs realizing `DefZF` internally;
* reflection and bounding arguments giving the Separation and Replacement schemes in `L`;
* internally represented, coherent well-orders of all stages, yielding Choice in `L`.

## Main declarations

- `Constructible.LStageZF`: the internally represented constructible hierarchy.
- `Constructible.L`: the class of constructible sets.
- `Constructible.textbookEZF`: the exact five-clause enumeration
  `E(a,n,m)` obtained by well-founded recursion on the internally represented
  domain `omega x omega`.
- `Constructible.textbookDfZF_eq_range_textbookEZF`: the textbook identity
  `Df(a,n) = {E(a,n,m) | m in omega}`.
- `Constructible.card_textbookDfZF_le_aleph0`: the textbook least-code proof
  that each fixed-arity `Df(a,n)` has cardinality at most `aleph0`.
- `Constructible.Model.textbookEZF_functionAbsoluteTo` and
  `Constructible.Model.textbookDfCodeZF_functionAbsoluteTo`: the complete
  object-language function-absoluteness theorems for `E` and `Df` over every
  transitive ZF set model.
- `Constructible.Model.finiteFunctionSpace_functionAbsoluteTo`: finite
  function-space formation is absolute on standard finite ordinal domains.
- `Constructible.Model.textbookDInCodeZF_functionAbsoluteTo` and
  `Constructible.Model.textbookDEqCodeZF_functionAbsoluteTo`: the two
  totalized atomic generators are absolute to every transitive ZF set model.
- `Constructible.Model.textbookExistsProjCodeZF_functionAbsoluteTo`: the
  textbook existential projection, including its zero-arity empty branch, is
  absolute to every transitive ZF set model.
- `Constructible.range_definableRelationEnumerate_val`: the external
  natural-number enumeration has underlying range exactly `Df E n`.
- `Constructible.cardinal_mk_definableRelation_le_aleph0`: fixed-arity
  definable relations form a countable type.
- `Constructible.card_DefZF_eq_of_aleph0_le`: an infinite set and its
  definable powerset have the same external cardinality.
- `Constructible.card_LStageZF_eq_of_aleph0_le`: every infinite
  constructible level has the cardinality of its ordinal index.
- `Constructible.exists_transitive_textbookFiniteFragmentReflection`: the
  set-sized form of the textbook finite reflection theorem, including the
  Mostowski collapse and `max aleph0 (card seed)` bound.
- `Constructible.exists_transitive_textbookFiniteFragmentReflection_L`: the
  Section 6.3 theorem specialized to the transitive class `L`, after choosing
  one common reflecting constructible level for the finite sentence list.
- `Constructible.Model.LCarrier`: the membership structure carried by `L`.
- `Constructible.Model.lCarrier_models_ZF`: `L` is a model of ZF.
- `Constructible.Model.lCarrier_models_ZFC`: `L` is a model of ZFC.
- `Constructible.Model.relativeL_eq_L`: the hierarchy computed inside `L` is externally `L`
  (the standard stagewise theorem `L^L = L`).
- `Constructible.Model.lCarrier_models_vEqualsL`: `L` satisfies the parameter-free,
  evaluator-coded `V = L` sentence proved correct for `LCarrier`.
- `FirstOrder.Language.Theory.ZFCVEqualsL`: ZFC packaged with that selected sentence.
- `Constructible.Model.lCarrier_models_ZFCVEqualsL`: `L` models the packaged theory. A generic
  adequacy theorem for the sentence over arbitrary ZFC models is not asserted here.
- `Constructible.ContinuumFormula.chSentence`: the first-order sentence CH.
- `Constructible.ContinuumFormula.gchSentence`: the first-order sentence GCH.
- `Constructible.ContinuumFormula.realizes_chSentence_iff`: the satisfaction semantics of CH.
- `Constructible.ContinuumFormula.realizes_gchSentence_iff`: the satisfaction semantics of GCH.
- `Constructible.ContinuumFormula.internalHartogsLCarrier`: the internal Hartogs number of a
  constructible set.
- `Constructible.ContinuumFormula.internalHartogsLCarrier_isHartogsNumber`: correctness of the
  internal Hartogs construction.
- `Constructible.ContinuumFormula.internalHartogsLCarrier_isCardinal`: the internal Hartogs
  number is an internal cardinal.
- `Constructible.ContinuumFormula.injects_antisymm_lCarrier`: internally represented
  injections in both directions yield an internally represented bijection.
- `Constructible.ContinuumFormula.internalHartogsLCarrier_isSuccessorCardinal`: the Hartogs
  number of an internal cardinal is its internal successor cardinal.
- `Constructible.ContinuumFormula.injects_adjoin_fresh_of_omega_subset_lCarrier`: an internal
  injection into a constructible set containing `omega` extends over one fresh point, using an
  actual constructible omega-shift graph whose range omits the empty set.
- `Constructible.ContinuumFormula.internalHartogsOrdinal_isSuccLimit`: the internal Hartogs
  ordinal of an internal cardinal containing `omega` is a nonzero limit ordinal.
- `Constructible.ContinuumFormula.not_injects_powerSet_lCarrier`: Cantor's theorem for the
  internal powerset of a constructible set.
- `Constructible.MostowskiCollapse.CondensationHull.condensation_of_elementary_at_reflectionLevel`:
  the Mostowski collapse of a set-sized fully elementary substructure of a condensation
  reflection level is exactly a constructible level.
- `Constructible.MostowskiCollapse.condensation_of_elementary_isSuccLimit`:
  the Mostowski collapse of a set-sized fully elementary substructure of any nonzero limit
  level `L_theta` is exactly the constructible level indexed by its ordinal height.
- `Constructible.ContinuumFormula.modelsGCH_lCarrier_of_condensation_interfaces`:
  the generic conditional reduction of GCH to cardinal-controlled hulls, the Hartogs-stage
  cardinal bound, and internal cardinal representatives.
- `Constructible.Model.aritySeparatedFormulaSkolemStep`: the internally represented
  one-formula witness step whose nullary and positive-arity selectors have separate exact
  membership semantics. Positive arity uses only parameter-prefix fibers.
- `Constructible.Model.internalFormulaSkolemOmegaUnion`: the internally collected omega union
  of a finite Skolem-family iteration, conditional on one uniform object-language formula for
  its stage graph. It gives finite-family witness closure only, not full elementarity.
- `Constructible.Model.internalSkolemMatrixNatEnumerate_surjective`: every existential
  Skolem matrix occurs in one explicit external natural-number enumeration. This does not
  assert that decoding or compilation has an internally represented graph.
- `Constructible.exists_textbookECode_for_positiveFormula`: every positive-arity formula
  relation is represented by a value of the textbook enumeration `E(a,n,m)`.
- `Constructible.closesWithinAll_of_closesUnderTextbookEWitnesses`: closure under witnesses
  for all textbook `E` relations implies full Tarski--Vaught closure for every formula.
  The corresponding internal omega hull is constructed by
  `TextbookEUniformWitnessIteration`.
- `Constructible.Model.textbookEWitnessTaskDomain`: the actual constructible task set
  `omega x (omega \ {0})`; its members uniquely decode as an `E` code and positive arity.
- `Constructible.Model.closesUnderTextbookEWitnesses_iff_internalTasks`: exact reduction of
  the full external witness-closure predicate to one requirement for each member of that
  internal task set.
- `Constructible.textbookEZF_natCode_mem_L`: every standard-code value of the textbook
  recursion `E(a,n,m)` is constructible when `a` is, proved directly by strong induction
  through the five clauses rather than by placing `L` in a transitive ZF set model.
- `Constructible.Model.textbookEZFLCarrier`: the corresponding `LCarrier` representation of
  one standard-code `E` relation.
- `Constructible.Model.textbookESingleWitnessStep`: the actual internal one-task step for a
  decoded `E` code and arity. Its prefixes are textbook function graphs from `seed^n`, and
  its selected witnesses are obtained by a fixed Separation formula and the canonical
  internal stage order.
- `Constructible.Model.exists_witness_mem_textbookESingleWitnessStep`: exact witness closure
  for that one decoded task.
- `Constructible.Model.textbookEUniformWitnessStepFormula`: one fixed first-order formula for
  the uniform witness step over the internal task domain.
- `Constructible.Model.textbookEUniformWitnessOmegaUnion`: the actual internal omega union of
  the uniform witness iteration.
- `Constructible.ContinuumFormula.hasCardinalControlledHulls_lCarrier`: the resulting full
  elementary hull has the textbook cardinal bound.
- `Constructible.ContinuumFormula.InternalOrderTypeWitness`: the explicit internal
  order-type-graph interface, now constructed by internal Separation, Replacement, and
  well-founded induction along each represented well-order.
- `Constructible.ContinuumFormula.hasInternalCardinalRepresentatives_lCarrier`: every
  constructible set is internally equinumerous with an internal cardinal. The bijection is an
  actual Kuratowski graph belonging to `L`; an external order type or equivalence is not used as
  its witness.
- `Constructible.ContinuumFormula.modelsGCH_lCarrier_of_hulls_and_hartogsStageBound`:
  the specialized GCH reduction after internal cardinal representatives have been constructed.
- `Constructible.ContinuumFormula.modelsGCH_lCarrier`: the constructible membership structure
  satisfies GCH, using the textbook `E` Skolem hull and the internal Hartogs-stage induction.
- `Constructible.ContinuumFormula.modelsCH_lCarrier`: the constructible membership structure
  satisfies CH as the `kappa = omega` instance of GCH.
- `Constructible.Model.lCarrier_models_ZFCVEqualsLGCH`: `LCarrier` is a model of the packaged
  first-order theory `ZFC + V = L + GCH`.
- `FirstOrder.Language.Theory.ZFCVEqualsLGCH`: the packaged theory `ZFC + V = L + GCH`.
- `FirstOrder.Language.Theory.ZFCCH_isSatisfiable`,
  `FirstOrder.Language.Theory.ZFCGCH_isSatisfiable`, and
  `FirstOrder.Language.Theory.ZFCVEqualsLGCH_isSatisfiable`: concrete semantic model existence,
  witnessed by `LCarrier`; these are not arbitrary-model transformations or syntactic
  proof-calculus theorems.
-/
