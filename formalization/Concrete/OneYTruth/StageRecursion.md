# Actual bounded-stage recursion over L and adequate levels

This development does not assume the existence of a set model of ZF. It
uses the already proved schemas of the proper class `LCarrier`.

`StageCoding.lean` constructs the actual index set

    Stage κ = Nat × {η : Ordinal // η ≤ κ}

with literal code `pair (natCode k) η.toZFSet`. Its range is exactly
`ω.toZFSet × (succ κ).toZFSet` and belongs to L. A fixed Δ₀ formula
recognizes the actual lexicographic predecessor relation. The coded relation
is well-founded, and each complete predecessor set belongs to L.

`StageRecursionDomain.lean` proves that the textbook local recursion domain
of a stage is exactly that stage together with all its predecessors. This
set belongs to L. Relation-on-domain, set-minimum, set-predecessor,
predecessor-closure, and fixed-formula semantics are supplied for these
actual sets and relations.

`StageRecursionL.lean` proves an actual collection theorem. Given a uniform
first-order presentation of a one-step operator `op`, and external values F
satisfying its predecessor-graph recursion equation:

1. Every L-internal graph satisfying the local-solution formula equals the
   literal restriction graph of F. This is proved by well-founded induction
   on the actual coded stage order.
2. Every constructible literal local graph satisfies that formula. Its
   predecessor restrictions are constructed by L Separation.
3. By well-founded induction on stages, L Replacement collects the earlier
   local graphs using that one fixed formula and its proved uniqueness.
   Their union is exactly the new predecessor graph. One-step closure
   supplies the next value, and adjoining its pair gives the next local
   graph in L.
4. One final Replacement and union gives the entire restriction graph of F
   on the bounded stage set as a member of L.

The central theorems are `StageStepPresentation.stageLocalGraph_mem_L` and
`StageStepPresentation.stageGraph_mem_L`. Their inputs do **not** include
constructibility of any recursive graph.

`GraphInputTower.lean` defines a total literal graph-input satisfaction
operator. Even a malformed input graph has a specified meaning: a named or
diagonal relation holds when the graph displays some truth set containing
the queried formula/assignment pair. On the actual predecessor graph this
interpretation equals `ExternalTower.stageInterpretation`. Consequently,
the already constructed `ExternalTower.truth` satisfies the exact
graph-input recursion equation. The theorem
`graph_mem_L_of_stepPresentation` applies the preceding construction to
the **actual** external truth tower.

`StageStepFormula.lean` supplies all stage-domain/relation syntax from an
ordinary whole-step formula. `GraphInputConstructible.lean` connects the
actual bounded graph-query construction and proves one-step closure for
arbitrary constructible input graphs.

`ActualTowerConstructible.lean` now instantiates that interface with the
actual formula in `GraphStepCorrect.lean`. Its canonical sources, diagrams,
and witnesses have been constructed and verified. Thus
`ExternalTower.graph_mem_L κ hU` is an unconditional theorem for every
constructible U. `UniformFromGraph.lean` performs a fixed Δ₀ flattening of
the graph, giving `uniformSet_mem_L` and the actual
`RootSemantics.ambientTruth_mem_L` used by initial representations.

## Exact remaining boundary

`PureFOSchemas.lean` derives ordinary first-order Separation and Replacement
from actual adequacy. `InternalStageDomain.lean` proves source, predecessor,
and local-domain membership in Lβ for κ<β. `InternalRecursionEnvironment.lean`
supplies the basic set operations and schemas actually needed by the local
graph construction, without asserting that Lβ is a model of all ZF.

`InternalFormulaRestriction.lean`, `InternalStagePresentation.lean`, and
`InternalStageRecursion.lean` now prove the entire local-graph construction
inside this weak environment. Separation constructs literal restrictions;
well-founded uniqueness makes the displayed local-solution formula functional;
Replacement collects its values and unions form the actual whole graph.
`InternalStageStepFormula.lean` supplies the actual bounded stage syntax.

`ActualInternalTower.lean` instantiates this construction with the genuinely
Σ₁ one-step certificate in `GraphStepSigmaFO.lean`. Soundness, completeness,
all thirteen fixed source sets, and step closure are proved in the actual
smaller carrier by `InternalActualStep.lean`. The final theorem is

    graph_mem_of_adequate (hβ : Adequate β) (hκβ : κ < β)
      (hU : U ∈ LStageZF β) : graph κ U ∈ LStageZF β

`InternalUniformTower.lean` flattens that actual graph by bounded Separation,
proving `uniformSet_mem_of_adequate` under exactly the same three hypotheses.

There is no remaining one-step, source-set, lookup, atomic-table,
satisfaction-set, or recursive-graph hypothesis. This does not use arbitrary
FO absoluteness from L to Lβ; the smaller-domain witnesses are constructed.

The remaining finite-reflection work includes combining these local
certificates into one canonical Σ₁ certificate for the whole tower and
using the completed canonical stage query in the finite pattern matrix.
Membership of the actual tower has been proved; its one-piece Σ₁ graph
definition is a separate task, and the overall 1-Y proof is not yet complete.

At the completed recursion/graph-input boundary, Lean reports only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry` or custom axiom
is used.


`ActualStageQuery.lean` has now completed the independent domain obligation:
its actual four-parameter Sigma-one query is equivalent to `U = LStageZF a`
inside every adequate larger level. It uses a real bounded Def certificate,
the proved local bound for the actual canonical history, and Collection for
one common certificate witness bound. No local semantic fields remain.

