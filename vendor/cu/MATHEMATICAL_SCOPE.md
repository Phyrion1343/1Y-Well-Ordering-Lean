# Mathematical Scope and Proof Fidelity

This file records the mathematical meaning of the main Lean constructions and
the review rules for extending them. A technical Lean lemma need not have a
name found in a textbook, but it must implement a substep of a standard proof
without changing the definition, hypotheses, or conclusion.

## Standard Proof Map

| Mathematical step | Lean realization | Status and exact scope |
| --- | --- | --- |
| `Def(A)` is the family of subsets of `A` first-order definable over `(A, in)` with finitely many parameters from `A` | `FOFormula`, `Df`, `definablePowerset`, `DefZF` | Proved extensionally, including both directions of the satisfaction characterization |
| For transitive `A`, formula definability agrees with the finite rudimentary closure of `A union {A}` intersected with `P(A)` | `Godel.godelDef`, `FormulaGodel`, `Equivalence` | Proved as `DefZF_eq_godelDef`; transitivity is an explicit hypothesis |
| `L_0 = empty`, `L_(alpha+1) = Def(L_alpha)`, and `L_lambda = union_(beta<lambda) L_beta` | `LStageZF_zero`, `LStageZF_succ`, `LStageZF_limit` | Every level is an actual `ZFSet`; only the full class `L` is an external `Set ZFSet` |
| Every level is transitive and the hierarchy is increasing | `LStageZF_isTransitive`, `LStageZF_mono` | Unconditional for the hierarchy above |
| Formula reflection is obtained by an omega-chain closed under witnesses | `Reflection` | Standard Tarski--Vaught/reflection proof in the ambient Lean metatheory |
| Separation in `L` follows by reflecting one formula to a level and applying `Def` | `Separation` | Full first-order scheme, not a finite fragment |
| Collection bounds a set-indexed family of witnesses; Replacement is Collection followed by Separation | `Collection`, `Replacement` | Full internal model schemes for `LCarrier` |
| The internal powerset of `a` is `P(a) intersect L`, bounded into one level | `PowerSet` | Standard inner-model powerset theorem |
| Choice follows from the canonical well-order of `L`: order new definitions by their least code/parameters and take coherent unions at limits | successor program orders, stage histories, `StageHistoryGraphSystem` | The relation graph is proved to be a member of `L`; an external Lean relation is never substituted for it |
| Every constructible set has an internal cardinal representative | `InternalOrderTypePredecessor`, `InternalOrderTypeReplacement`, `InternalOrderTypeStep`, `InternalOrderTypeInduction`, `InternalOrderTypeWitnessConstruction` | Proved unconditionally from the represented stage well-orders. Predecessor sets, order-isomorphism graphs, and the final bijection are actual members of `L`; `Ordinal.typein` is used only to identify the canonical ordinal |
| The hierarchy recomputed internally by `L` has the same stages, hence `L^L = L` | `VEqualsL`, `relativeL_eq_L` | Proved stage by stage for the concrete structure `LCarrier` |
| Condensation is proved by the Mostowski collapse of a fully elementary set-sized substructure | `StandardCondensation` | Full elementarity remains visible in the theorem; no finite-fragment substitute is used |
| The textbook GCH argument uses the internal `E/Df` enumeration to form a cardinal-controlled omega Skolem hull, applies Condensation, and bounds the hierarchy through the Hartogs successor | `TextbookEUniformWitnessIteration`, `TextbookEElementaryHull`, `TextbookEUniformWitnessCardinality`, `StandardCondensation`, `InternalDefZFInjection`, `CanonicalStageInjectionFamily`, `InternalLStageInjection`, `CondensationGCHApplication` | Completed unconditionally for `LCarrier`. Successor and limit maps are actual internal Kuratowski graphs; the limit family is collected by Replacement. This yields `modelsGCH_lCarrier` and then `modelsCH_lCarrier` |

## Metatheoretic Boundary

The model theorems concern Mathlib's concrete type `ZFSet` and the subtype
`LCarrier`. They are checked by Lean's kernel and have no `sorry` or custom
axiom. The theorems `ZFCCH_isSatisfiable`, `ZFCGCH_isSatisfiable`, and
`ZFCVEqualsLGCH_isSatisfiable` assert semantic model existence in Lean's
metatheory, with this concrete `LCarrier` as witness. They are not a syntactic
proof-calculus theorem over ZFC and do not give an inner-model construction
parameterized over every arbitrary, possibly externally ill-founded, model
of ZFC.

In particular:

- `Classical.choice` is available in the ambient Lean metatheory. Its use does
  not automatically produce a function graph belonging to `L`.
- Mathlib's `ZFSet.Definable` means liftability to `PSet`, not first-order
  definability in the language of set theory.
- `ZFSet.sep` accepts an ambient Lean predicate. When a later argument needs
  an operation inside `L`, an object-language formula or an internal graph
  must be constructed separately.
- An external cardinal inequality, Lean function, or `Set ZFSet` is not a
  replacement for an internally represented set or function graph.

## Textbook Route Lock

The route from definability to GCH follows Wang Fangting, *Axiomatic Set
Theory*, Sections 6.3--6.8. Its completed checkpoints are:

1. Formalize absoluteness of the set-theoretic operations and well-founded
   recursions used in the construction.
2. Construct `D(k,a,n)`, `Df(a,n)`, and the internally represented textbook
   enumeration `E(a,n,m)`, with exact semantics, range, countability, and
   transitive-model absoluteness.
3. Use one fixed formula for the uniform `E`-witness step, collect its finite
   iterates by Replacement over internal omega, and take the internal union.
   This gives the full Tarski--Vaught elementary hull with the textbook
   cardinal bound.
4. Apply the genuine Mostowski collapse and Condensation theorem to that hull.
5. Prove the hierarchy bound by an internal transfinite construction:
   `DefZF` supplies the successor injection; at a limit, Replacement collects
   the canonical earlier-stage injection family and the least-containing-stage
   map combines it with internal product absorption; the construction is then
   assembled below the internal Hartogs successor.
6. Apply the Condensation bridge to obtain `modelsGCH_lCarrier`, derive
   `modelsCH_lCarrier` by specializing GCH at omega, and package the concrete
   semantic satisfiability theorems.

The neutral restriction semantics in checkpoint 1 is implemented in
`Absoluteness`: `relationAbsoluteTo_iff_interpreted_eq_restricted`,
`classAbsoluteTo_iff_interpreted_eq_inter`, and
`functionAbsoluteTo_iff_interpretedGraph_eq_restriction` prove exactly that
interpretation in a carrier is restriction of the ambient relation, class,
or function graph. `TransitiveZFModel` separately defines a transitive ZF set
model as exactly transitivity plus satisfaction of `Theory.ZF`, and proves the
two-way semantic bridges between the independent formula syntaxes.
`TransitiveZFClosure` derives ambient empty-set, pairing, singleton, union, and
Kuratowski-pair closure from the corresponding internal ZF axioms and
transitivity. It deliberately does not assert ambient power-set closure.
`FormulaSchemeBridge`, `TransitiveZFSeparation`, and
`TransitiveZFReplacement` now derive formula-indexed Separation and functional
Replacement directly from the model's own ZF schemes. Their internal witnesses
are identified with ambient extensional descriptions only after the existence
proof. `TransitiveZFFunctionGraph` then applies Replacement to the explicit
object-language formula `exists y, phi(params,x,y) and q = <x,y>` and obtains
an internally represented Kuratowski graph on any internal set-sized domain.
The theorem does not turn a class-sized model-relative function into one global
set graph. `TransitiveZFOmega` derives `omega.toZFSet in M` for every transitive
ZF set model `M`: Infinity first gives an internal inductive set, two uses of
the model's Separation scheme isolate its least inductive subset and prove the
zero-or-successor decomposition, and ambient membership induction identifies
that subset with the standard omega. This result is restricted to transitive
well-founded `ZFSet` models; it does not assert the same conclusion for an
arbitrary abstract or nontransitive model. `TextbookSetWellFounded` separately
implements the Section 6.1
definitions: well-foundedness quantifies over nonempty actual set subsets,
set-likeness asserts that predecessor classes are actual sets, and neither is
replaced by Lean's stronger whole-type `WellFounded`.
`TextbookPredecessorClosure` constructs the actual sets `p_n(x)` and
`cl(A,x,R)` and proves the two textbook closure propositions.
`TextbookClassWellFounded` then applies set-minimality only to the actual set
`X intersect cl(A,x,R)`, obtains minima for arbitrary external subclasses,
and only afterwards derives Lean well-foundedness of the subtype relation.
It also constructs the actual local domain `{x} union cl(A,x,R)`.
`TextbookClassRecursion` uses that derived induction principle to construct
the ambient recursive class function, passes an actual Kuratowski restriction
graph to every recursive step, and proves existence and uniqueness with the
textbook minimal-bad-class argument. Its existence implementation uses Lean's
well-founded fixpoint after the textbook class-induction theorem has been
proved. Independently, `TextbookLocalRecursion` now reproduces the page-108
proof: it constructs the actual local domains and Kuratowski graphs `f_x`,
proves overlap agreement, forms `q = union_{y R x} f_y`, adjoins the top pair,
and assembles the global function by `F(x) = f_x(x)`. Its existence proof does
not call the fixpoint implementation. `TextbookLocalRecursionBridge` proves
definitionally that this construction satisfies the established
`SatisfiesTextbookClassRecursion` predicate and re-exports existence and
uniqueness through that interface. These ambient constructions do not assert
that their Nat-indexed ranges, closures, or function graphs belong to an
arbitrary model. `TextbookRecursionFormula` supplies uniformly parameterized
first-order formulas for predecessor sets, local domains, local solution
graphs, and recursive values. Its `SatisfiesIn` theorems prove the exact
restricted semantics in both directions, including all internal witnesses;
the formulas themselves do not assert that a local solution graph exists.
`InternalPredecessorClosure` then proves those ambient predecessor closures
and local domains belong to a transitive ZF set model under the textbook
conditions (I)--(III). It first uses the model-internal set-like assertion to
obtain an internal predecessor-set witness and only then identifies it with
the ambient predecessor set using class/relation absoluteness and condition
(III). Successor layers use internal Replacement and Union. A uniform finite
history formula, Replacement over the already internal standard omega, and a
final Union construct the full closure. External `Nat` indexing is never used
directly as evidence that the closure belongs to the model.
`TextbookRecursionAbsoluteness` packages the final Section 6.2
argument and proves the resulting `FunctionAbsoluteTo` theorem once a
formula-represented model-relative recursive solution `H` and its transported
recursion equation are supplied. `InternalTextbookRecursion` discharges that
obligation. It uses internal Separation on each internal local domain to form
the set of points with no formula-represented local solution, derives an
internal minimal bad point from the textbook set-minimum hypothesis, and
contradicts minimality by the literal page-108 parent step. That step uses
internal Replacement to collect the unique child graphs, Union to form their
glued graph, internal graph restriction for the step input, and Pairing plus
Union to adjoin the top value. The resulting global model solution is closed
in the model and represented by `recursionValueFormula`; the terminal
minimal-counterexample argument yields the standard `FunctionAbsoluteTo`
theorem in the parameter-free interface. The implementation does not invoke
an ambient well-founded recursion as a substitute for this internal bad-set
argument.

The textbook `E/Df` layers follow the definitions on textbook
pages 127--130. `TextbookDefinability` constructs the standard-`Nat` core
`a^n`, `D_in`, `D_eq`, `P_exists`, `D(k,a,n)`, and `Df(a,n)` as genuine
`ZFSet`s; complements are relative to the genuine finite function space and
the projection branch at stage `k+1` uses arity `n+1` at the same stage `k`.
`TextbookDefinabilityCode` only totalizes the natural-number arguments as
ambient set-coded inputs, returning the empty set on invalid codes. It is not
itself an internal decoder or an absoluteness theorem.
`TextbookFiniteTupleAbsolute` proves that every ambient graph on a standard
finite domain belongs to a transitive ZF model and then constructs the full
ambient finite function space by internal Power Set and Separation. It never
identifies an internal Power Set with the ambient Power Set on an infinite
domain. `TextbookTupleSpaceAbsolute` adds the standard finite-domain guard and
packages exactly this restricted result as `FunctionAbsoluteTo`; the bare
general function-space formula is not claimed absolute.
`TextbookAtomicAbsolute` and `TextbookProjectionAbsolute` give object-language
graphs, model-internal Separation constructions, and `FunctionAbsoluteTo`
theorems for the totalized `D_in`, `D_eq`, and `P_exists` operations. The
projection formula retains the textbook convention `P_exists(a,0,r)=empty`.
`TextbookNaturalLiterals` supplies Delta-zero formulas for each fixed standard
natural-number literal. `TextbookNaturalAddition` gives a pure
membership-language finite-recursion graph for addition on the standard
omega, proves its exact ambient and restricted semantics, and proves the
canonical finite witness graph belongs to every transitive ZF model.
`TextbookNaturalMultiplication` and `TextbookNaturalPower` repeat this
construction with finite recursion graphs for multiplication and
exponentiation; their reusable renamed formulas have exact ambient and
restricted semantics. `TextbookBooleanAbsolute` gives the actual `ZFSet`
relative difference and intersection operations, obtains their model closure
from internal Separation, and proves their pure membership-language graph
formulas absolute. `TextbookGraphLookupAbsolute` totalizes unique-value
lookup on arbitrary set-coded graphs and proves its formula absolute; on a
genuine function graph it returns exactly the displayed value, so recursive
history values are read from an internal graph rather than an external Lean
function.
`TextbookECodeArithmetic` proves in the metatheory that the exact textbook
codes `2^i * 3^j * 5^t` have unique exponent fields and that their recursive
index `i` is smaller than the code; it does not present this arithmetic as an
internal formula. `TextbookECodeDecode` adds a checked metatheoretic decoder
which accepts exactly tags below five and rejects codes with additional prime
factors; it likewise is not used as an internal graph.
`TextbookECodeFormula` separately supplies the genuine object-language graph:
it constructs the literals `2`, `3`, and `5`, invokes the already absolute
power graph three times and multiplication graph twice, and proves exact
ambient and restricted semantics for `2^i * 3^j * 5^t` without restricting
the general tag. `TextbookEDomain` constructs the genuine internal set
`omega x omega`, the relation `<i,k> R <m,n>` iff `i in m`, its exact
parameter-free formulas and restricted semantics, its well-founded set-like
proof, and its model-internal predecessor closure. `TextbookEKeyDecode` is the
corresponding metatheoretic reader for keys and is proved to accept exactly
the Kuratowski pairs in that domain; the internal key formula remains the one
from `TextbookEDomain`. `TextbookEParameterizedDomain` adds the fixed set
parameter without changing the domain or relation. `TextbookEStep` gives the
exact five branches and fallback using only internally represented operations
and total graph lookup. `TextbookERecursion` applies the internal textbook
recursion theorem and proves the object-language graph of `E` absolute.
`TextbookEDefinability` proves `Df(a,n)` is exactly the natural-number range of
`E(a,n,.)`, follows the textbook least-code argument to obtain
`|Df(a,n)| <= aleph0`, uses the model's Replacement axiom over its internal
omega to construct that range, and proves the resulting set-coded `Df`
function absolute.

The external cardinal estimates used alongside checkpoint 5 are implemented by
`DefZFCardinality` and `LStageZFCardinality`. The latter follows the actual
zero/successor/limit recursion, identifies the replacement-based limit with
the union of earlier levels, and proves `card (LStageZF alpha) = alpha.card`
under the standard infinitude hypothesis. These are ambient cardinal
statements and are logically separate from the now completed internal `E/Df`
absoluteness. The bound `|Df(a,n)| <= aleph0` in `TextbookEDefinability` is an
external cardinal statement about the concrete `ZFSet`; the associated
model-internal result is the Replacement-based closure and function
absoluteness theorem, not an unproved internal-cardinal assertion.

An independent finite-fragment reflection development is implemented by
`TextbookSkolemFunction`, `TextbookFiniteSkolemIteration`,
`TextbookFiniteSkolemCardinal`, and `TextbookFiniteReflection`.  In particular,
`exists_transitive_textbookFiniteFragmentReflection` uses the least default
in the selected well-order and proves seed containment, transitivity,
absoluteness of every listed sentence, and the exact
`max(aleph0, card seed)` upper bound.  Its ambient structure is a transitive
`ZFSet`.  `TextbookFiniteReflectionL` separately performs the simultaneous
reflection step selecting a common level `L_beta` and then composes the two
equivalences.  Thus
`exists_transitive_textbookFiniteFragmentReflection_L` specializes this
finite-fragment result to `T = L`; it still asserts only the displayed finite
fragment and is not substituted for the full elementary hull used by GCH.

Lean-specific syntax codes, tuple encodings, and graph representations are
implementation devices. They may enter this route only through a theorem
proving that they realize the corresponding textbook formula, relation,
function, or cardinal statement. A conditional interface is not evidence
that the textbook checkpoint has been proved.

## Formula Coding Boundary

`FormulaSyntaxCode` currently gives an injective natural-number code and a
partial decoder for external `FOFormula` values. Every valid formula receives
an internal von Neumann natural-number representative, but there is not yet a
single internally represented decoder, compiler, or satisfaction predicate
which operates on arbitrary codes. Per-formula compilation in
`FormulaGodel` is correct but strictly weaker than that uniform result.

The textbook construction of `E(a,n,m)` is a different obligation from a
uniform formula decoder. `TextbookERecursion` now recursively enumerates the
finite relation algebra `D(k,a,n)` through an internally represented graph,
and `TextbookEDefinability` proves its transitive-model absoluteness and exact
range. These results do not turn the external Lean function
`definableRelationEnumerate` into an internal decoder or satisfaction
predicate.

The sentence `vEqualsLSentence` is proved correct for `LCarrier` using the
stage-history evaluator and the theorem `relativeL_eq_L`. What is not yet
proved is a generic adequacy theorem over an arbitrary ZFC model, comparing
this evaluator-coded sentence with an independent semantic specification of
that model's internal constructible universe. Accordingly,
`lCarrier_models_vEqualsL` is a genuine theorem about the constructed model,
while the theory name `ZFCVEqualsL` must not be advertised as already carrying
that unproved arbitrary-model comparison.

The completed full hull does not require a uniform internal decoder for the
external formula syntax. Instead, `TextbookPositiveFormulaEnumeration` maps
formula semantics into the internally represented `E/Df` relation algebra,
and one fixed witness-step formula handles the internal code/arity task set.
`TextbookEUniformWitnessIteration` applies Replacement through omega and
forms the internal union; `TextbookEElementaryHull` then obtains full
elementarity from the exact Tarski--Vaught bridge.

Despite its historical filename, `FullSkolemHull.lean` contains only legacy
single-step primitives. The completed GCH proof uses the `TextbookE...`
modules above and does not infer an omega hull from that legacy API.

`AritySeparatedFormulaSkolemStep` repairs the branch ambiguity of the older
generic selector. Its nullary and positive-arity selections are defined by
different object-language Separation predicates. The exact successor-arity
membership theorem contains only a parameter-prefix fiber and therefore
cannot add a bare relation member through a nullary alternative. Both
selections and their seed unions are actual `LCarrier`s, and their canonical
least witnesses are selected by the internally represented stage order.

`InternalFiniteSkolemIteration` now iterates this arity-separated operation
over a displayed finite list of matrices, retaining an actual `LCarrier` at
every finite stage and proving the corresponding witness-closure theorem. Its
natural-number stage map remains external. `InternalFiniteSkolemOmega`
constructs an internal omega union only under
`InternalFormulaSkolemStageSpec`, whose uniform object-language stage formula
is an explicit hypothesis for Replacement. It proves closure for that finite
list, not an internally enumerated all-formula hull or full elementarity, and
no sharp cardinal bound is inferred merely from branch separation.

`InternalSkolemMatrixCode` packages every existential matrix
`phi(params,y)` into one injective natural-number code and proves that its
total external enumeration is surjective. Each individual von Neumann code
belongs to internal omega and to `L`. This does not make the decoder, formula
compiler, or satisfaction map an internally represented function graph.

`TextbookPositiveFormulaEnumeration` follows the relation-algebra definition
of `Df(a,n)`: atomic formulas are interpreted by `D_in` and `D_eq`, negation
by relative complement, conjunction by intersection, and existential
quantification by projection. It proves ordinary Tarski semantics for every
positive arity and then uses completeness of `E(a,n,m)` to enumerate the
resulting relation. The positive-arity restriction is explicit because the
textbook's zero-arity projection convention is empty and must not be confused
with the truth value of a closed existential sentence.

`TextbookESkolemClosure` proves the full semantic bridge needed for a genuine
Skolem hull: closure under witnesses for every textbook relation
`E(U,n+1,m)` implies `ClosesWithinAll`, and hence `SatisfactionAbsolute`, for
all first-order formulas. `ClosesUnderTextbookEWitnesses` is an external
semantic predicate, but `TextbookEUniformWitnessStepFormula` gives the fixed
internal step formula and `TextbookEUniformWitnessIteration` constructs an
actual `LCarrier` omega union satisfying it. `TextbookEElementaryHull` and
`TextbookEUniformWitnessCardinality` turn this into the required elementary,
cardinal-controlled hull.

`FormulaSkolemStep.lean` currently proves only that its output retains the
seed, stays inside the ambient set, and contains a required witness. The
generic selector has an untagged nullary disjunct, so at positive arity it may
also add one unrelated tuple-code element. Its theorem statements remain
valid, but this legacy API is not the textbook's exact total Skolem function
and is not used by `InternalFiniteSkolemIteration`. Branch-exact finite
iteration instead uses `aritySeparatedFormulaSkolemStep`; this does not
retroactively strengthen any theorem about the legacy operation.

`InternalOrderTypePredecessor` uses internal Separation to form the actual
predecessor set of a point in a represented relation. `InternalOrderTypeCanonical`
identifies the canonical external ordinal references, and
`InternalOrderTypeUniqueness` proves uniqueness from represented
order-isomorphism graphs. `InternalOrderTypeReplacement` applies internal
Replacement to `beforeOrderTypeRelation`; `InternalOrderTypeStep` then uses
Separation in a bounded internal container to construct the actual local
Kuratowski graph and proves it is an order isomorphism. The small-carrier
well-founded induction in `InternalOrderTypeInduction` supplies this graph at
every point. Finally, `InternalOrderTypeWitnessConstruction` proves totality,
boundedness, single-valuedness, injectivity, and surjectivity of
`memberOrderTypeRelation`, constructs the final graph in `L`, and proves
`hasInternalCardinalRepresentatives_lCarrier` without extra hypotheses.
External `Ordinal.typein` and semantic equivalences are used only to identify
and verify the represented graph; neither is substituted for an internal
set-valued witness.

The reusable Condensation-to-GCH bridge keeps
`HasCardinalControlledHulls` and `HartogsStageBound` explicit. Both are now
discharged for `LCarrier`: `hasCardinalControlledHulls_lCarrier` uses the
uniform textbook `E` hull, and `hartogsStageBound_lCarrier` uses the internal
stage induction.

For the limit part of `HartogsStageBound`, `InternalStageCardinalUnion` uses
Replacement to form the actual internal set of earlier levels and Separation to form the actual
index-to-stage graph. `CanonicalLimitStageSelector` uses a fixed formula to
select the least earlier level containing each element of a nonzero limit
stage; its selector is an actual `LCarrier` graph. The external `firstStage`
operation is used only to prove totality and uniqueness of that graph. Thus
neither an external ordinal-indexed family nor an external choice function is
being treated as an internal witness. `InternalInfiniteCardinalAbsorption`
constructs, by a fixed formula and Separation, the internal map which shifts
the natural numbers and fixes the complement of `omega`; its range omits the
empty set. Extending a graph by that omitted value proves one-point
absorption internally. `HartogsLimit` applies this standard argument to prove
that the internal Hartogs ordinal of an internal cardinal containing `omega`
is a nonzero limit ordinal. `InternalDefZFInjection` constructs the successor
map. `CanonicalStageInjectionFamily` and `InternalStageInjectionFamily`
collect the earlier-stage injection graphs by internal Replacement, and
`InternalLStageInjection` combines the successor and limit cases to prove
`hartogsStageBound_lCarrier`. Ambient `ZFSet.card` estimates are used only
where transported to these genuine internal graphs.

Finally, `modelsGCH_lCarrier` applies the conditional bridge to
`hasInternalCardinalRepresentatives_lCarrier`,
`hasCardinalControlledHulls_lCarrier`, and `hartogsStageBound_lCarrier`.
`modelsCH_lCarrier` is the standard implication `GCH -> CH`, and
`lCarrier_models_ZFCVEqualsLGCH` packages ZFC, the selected `V = L` sentence,
and GCH in the concrete constructible model.

## Required Review for Future Steps

Before accepting a new major theorem:

1. State the standard mathematical definition and theorem, including every
   side condition.
2. Prove that the Lean predicate has exactly that semantics; a convenient
   sufficient condition may not be renamed as the standard concept.
3. Mark every object as external or internally represented. Internal
   functions and relations require set-valued graphs.
4. Keep conditional interfaces in the final theorem type until they are
   constructed from earlier results.
5. Do not replace full elementarity by an arbitrary finite fragment in a
   theorem whose standard statement requires full elementarity. Conversely,
   do not strengthen the textbook GCH proof to full elementarity and then
   hide the extra unproved machinery. A specialized finite fragment is usable
   only after proving that it contains every subformula and every finite ZF
   fact used by the target argument.
6. Check theorem strength in both directions and inspect all typeclass and
   implicit assumptions.
7. Rebuild with warnings as errors, search for `sorry`, `admit`, and custom
   axioms, and inspect the kernel axiom dependencies of the exported theorem.
8. Follow a standard published proof route. If an implementation uses a
   different coding or auxiliary relation, first prove that it realizes the
   standard definition; convenience alone is not evidence of equivalence.
9. Do not give an unfinished approximation the name of the final mathematical
   object. Conditional hypotheses must remain visible in every exported
   theorem until constructions discharging them have been checked.
