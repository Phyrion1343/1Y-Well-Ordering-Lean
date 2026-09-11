# The Constructible Universe in Lean 4

This repository formalizes Goedel's constructible universe `L` in Lean 4. Each hierarchy stage
`LStageZF alpha` is represented by an internal `ZFSet`, while the full universe `L` is represented
as a class of `ZFSet`s. The inherited membership structure on `L` is proved to model the canonical
first-order theory ZFC, the selected `V = L` sentence, and GCH.

The formalization includes:

- an intrinsically scoped formula syntax and satisfaction semantics;
- a proved per-formula compilation into internally represented rudimentary
  relations, the nine Goedel operations, and `DefZF`;
- successor and limit stages of the constructible hierarchy;
- Separation, Replacement, Power Set, Infinity, and the remaining ZF axioms in `L`;
- coherent internal well-orders of the stages and the Axiom of Choice;
- internally represented order-type maps and an internal cardinal representative for every
  constructible set;
- a stage-by-stage proof that the hierarchy computed inside `L` is externally `L`;
- the set-sized finite-fragment Skolem/Mostowski reflection theorem with its
  exact `max(aleph0, card seed)` bound;
- the standard external cardinal equalities for `Def(A)` and `L_alpha` at
  infinite inputs;
- the standard Condensation Lemma for fully elementary set-sized substructures of every nonzero
  limit level `L_theta`;
- the internally represented textbook `E/Df` enumeration, uniform omega-stage Skolem hull,
  and its exact cardinal bound;
- internal successor and limit bounds for constructible levels up to the Hartogs successor;
- GCH and CH in `L`, and concrete semantic models of `ZFC + CH`, `ZFC + GCH`, and
  `ZFC + V = L + GCH`.

The main exported results are:

- `Constructible.LStageZF`
- `Constructible.DefZF`
- `Constructible.L`
- `Constructible.Model.lCarrier_models_ZF`
- `Constructible.Model.lCarrier_models_ZFC`
- `Constructible.Model.relativeL_eq_L`
- `Constructible.Model.lCarrier_models_vEqualsL`
- `Constructible.ContinuumFormula.hasInternalCardinalRepresentatives_lCarrier`
- `Constructible.ContinuumFormula.modelsGCH_lCarrier_of_hulls_and_hartogsStageBound`
- `Constructible.ContinuumFormula.modelsGCH_lCarrier`
- `Constructible.ContinuumFormula.modelsCH_lCarrier`
- `Constructible.MostowskiCollapse.condensation_of_elementary_isSuccLimit`
- `Constructible.MostowskiCollapse.exists_collapse_eq_LStageZF_of_elementary_isSuccLimit`
- `Constructible.Model.lCarrier_models_ZFCVEqualsLGCH`
- `FirstOrder.Language.Theory.ZFCCH_isSatisfiable`
- `FirstOrder.Language.Theory.ZFCGCH_isSatisfiable`
- `FirstOrder.Language.Theory.ZFCVEqualsLGCH_isSatisfiable`

## Build

The project pins Lean `v4.33.0-rc1` and mathlib commit
`eba3d887fc52c98627f4b81507c0efc3096e91b9`.

```text
lake update
lake --wfail build
```

## Scope

The final model has carrier `Constructible.Model.LCarrier`, the subtype of `ZFSet` consisting of
constructible sets, with the inherited membership relation. The base theorem proves that this
structure satisfies `FirstOrder.Language.Theory.ZFC`; the combined theorem
`lCarrier_models_ZFCVEqualsLGCH` proves that it also models the packaged
`ZFC + V = L + GCH` theory. This is not a proof of `Con(ZFC)` inside ZFC.

The Condensation theorem assumes a nonzero limit ordinal `theta`, an internally represented set
`domain` contained in `LStageZF theta`, and full first-order satisfaction absoluteness between the
two membership structures. It proves that the Mostowski-collapse range is exactly
`LStageZF (ordinalHeight range)`; the usual existential statement follows as a corollary.

The CH and GCH development follows Wang Fangting, *Axiomatic Set Theory*, Sections 6.3--6.8.
The internally represented enumeration `E(a,n,m)` has range `Df(a,n)`. A fixed first-order
witness-step formula, internal Replacement through omega, and a final internal union construct
cardinal-controlled elementary hulls; the Tarski--Vaught bridge and Mostowski collapse give
Condensation. For the hierarchy bound, the successor step constructs an internal injection for
`DefZF`, while the limit step collects earlier-stage injections by Replacement and combines them
with a least-containing-stage selector and internal product absorption. The Hartogs-stage
argument then yields `modelsGCH_lCarrier`, and its `kappa = omega` instance yields
`modelsCH_lCarrier`. The earlier conditional reduction is retained as a reusable interface, but
all of its hypotheses are discharged for `LCarrier`.

The model theorems use Lean's `propext`, `Classical.choice`, and `Quot.sound` in the
ambient metatheory. Lean kernel checking verifies the formal derivations, but this repository has
not undergone external peer review.

These are semantic model theorems about Mathlib's concrete `ZFSet` universe. In particular,
`ZFCCH_isSatisfiable`, `ZFCGCH_isSatisfiable`, and `ZFCVEqualsLGCH_isSatisfiable` state model
existence in Lean's metatheory, witnessed by this concrete `LCarrier`. They are not a syntactic
proof-calculus derivation from `Theory.ZFC`, nor a construction parameterized over an arbitrary,
possibly externally ill-founded, model of ZFC. In particular, external uses of `ZFSet.sep`,
set-indexed suprema, and `Classical.choice` must not be read as internally represented operations
of `L` unless an internal graph or object-language specification is proved separately.

`FormulaSyntaxCode` assigns natural-number codes to external formulas, proves decoding on the
image of the encoder, and gives total external enumerations. It does not provide one internal
decoder and satisfaction predicate for arbitrary formula codes. The completed hull construction
does not assume such an evaluator: it uses the internally represented textbook `E/Df`
relation enumeration, an exact fixed object-language witness-step formula, and Replacement
through omega. The standard-`Nat` relation algebra, its total set-coded input interface,
finite function-space
closure, and the absolute graph formulas for `D_in`, `D_eq`, and `P_exists` are now formalized.
The standard-omega addition graph is absolute, the metatheoretic uniqueness and decrease facts
for the textbook code `2^i * 3^j * 5^t` are proved, and the recursion domain `omega x omega` with
relation `<i,k> R <m,n>` iff `i in m` is represented internally and proved well-founded,
set-like, and absolute. The corresponding multiplication and exponentiation graphs, together
with the relative-difference and intersection operations used by the recursion, are also proved
absolute. The prime-power code itself has a separate pure membership-language graph with exact
ambient and restricted semantics; its metatheoretic decoder is used only to implement and verify
branch selection. The five-branch function `E(a,n,m)` is now constructed by the textbook
well-founded recursion on the internally represented domain `omega x omega`. Its object-language
graph is absolute to every transitive ZF set model. Its range is proved to be exactly `Df(a,n)`,
the least-code injection proves `|Df(a,n)| <= aleph0`, and internal Replacement over the model's
omega gives both model closure and a complete object-language absoluteness theorem for `Df`. The
older external formula enumeration remains only an independent semantic check.

`relativeL_eq_L` is the standard stagewise theorem `L^L = L`, and
`lCarrier_models_vEqualsL` proves that `LCarrier` satisfies the particular parameter-free
evaluator-coded sentence constructed in `VEqualsL`. The repository has not yet proved a generic
adequacy theorem saying that this same sentence is equivalent to an independently specified
notion of `V = L` in every arbitrary ZFC model. Names such as `ZFCVEqualsL` package that selected
sentence; they should be read with this scope restriction.

See [MATHEMATICAL_SCOPE.md](MATHEMATICAL_SCOPE.md) for the standard proof map, the exact scope of
the current theorems, and the proof-fidelity checks required for future work.

## Project Structure

- `ConstructibleUniverse/ModelTheory/SetTheory`: the first-order language and theories ZF and ZFC.
- `ConstructibleUniverse/SetTheory/ZFC/Constructible`: the hierarchy, internal definability
  machinery, model construction, and Choice proof.
- `ConstructibleUniverse.lean`: the standalone root module.

## AI Assistance

OpenAI Codex was used substantially during code generation, refactoring, debugging, verification,
documentation, and repository preparation. Zike Liu is the author responsible for the published
content. Kernel type checking does not replace independent review of the definitions or their
intended mathematical interpretation.

## License

Copyright (c) 2026 Zike Liu. Released under the Apache License 2.0. See `LICENSE`.
