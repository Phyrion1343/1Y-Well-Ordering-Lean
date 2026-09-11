/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookLocalRecursionBridge
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalPredecessorClosure
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TransitiveZFFunctionGraph
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookRecursionAbsoluteness

/-!
# Internal textbook recursion in a transitive ZF model

This file supplies the model-internal builder required in Section 6.2,
Theorem 2 of Wang Fangting, *Axiomatic Set Theory*.

The first part is the semantic bridge needed before Replacement may be used:
a model-internal graph satisfying `localSolutionFormula` is decoded into an
actual `TextbookLocalSolution`, and two such graphs are proved equal.  Thus
the functionality premise for Replacement is a theorem about the formula's
exact semantics, rather than an assumption hidden behind notation.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-! ## Absoluteness of the recursion functional at fixed parameters -/

/-- The textbook recursion functional is absolute at the displayed parameter
tuple.  This fixed-parameter form is essential: a parameterized formula may
define corresponding functions at many different parameter tuples, so asking
it to be false away from one fixed prefix would be an unjustified stronger
hypothesis.

The first conjunct is the closure part of function absoluteness.  The second
conjunct gives the exact restricted semantics of
`stepFormula(params,x,q,z)`. -/
def TextbookStepAbsoluteAt (M : Set ZFSet.{u}) {n : Nat}
    (params : Tuple ZFSet.{u} n) (A : Set ZFSet.{u})
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (stepFormula : FOFormula (n + 3)) : Prop :=
  (forall x, x ∈ M -> x ∈ A -> forall q, q ∈ M -> step x q ∈ M) ∧
    forall x q z, x ∈ M -> q ∈ M -> z ∈ M ->
      (SatisfiesIn M stepFormula
          (snoc (snoc (snoc params x) q) z) <->
        x ∈ A ∧ z = step x q)

/-- Standard binary tuple domain for the parameter-free recursion functional:
the first coordinate lies in `A`, while the graph coordinate is arbitrary. -/
def TextbookStepTupleDomain (A : Set ZFSet.{u}) :
    Set (Tuple ZFSet.{u} 2) :=
  {s | s 0 ∈ A}

/-- Tuple presentation of the parameter-free binary recursion functional. -/
def textbookStepTupleFunction
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (s : Tuple ZFSet.{u} 2) : ZFSet.{u} :=
  step (s 0) (s 1)

/-- With no parameters, fixed-parameter step absoluteness is exactly the
standard `FunctionAbsoluteTo` statement on binary tuples. -/
theorem textbookStepAbsoluteAt_zero_iff_functionAbsoluteTo
    (M : Set ZFSet.{u}) (params : Tuple ZFSet.{u} 0)
    (A : Set ZFSet.{u})
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (stepFormula : FOFormula 3) :
    TextbookStepAbsoluteAt M params A step stepFormula <->
      FunctionAbsoluteTo M (TextbookStepTupleDomain A)
        (textbookStepTupleFunction step) stepFormula := by
  constructor
  · rintro ⟨hclosed, hgraph⟩
    constructor
    · intro s hsM hsDomain
      exact hclosed (s 0) (hsM 0) hsDomain (s 1) (hsM 1)
    · intro s value hsM hvalueM
      have hdecompose : snoc (snoc params (s 0)) (s 1) = s := by
        funext i
        fin_cases i <;> rfl
      have hsemantic := hgraph (s 0) (s 1) value
        (hsM 0) (hsM 1) hvalueM
      have hassignment :
          snoc (snoc (snoc params (s 0)) (s 1)) value =
            snoc s value := congrArg (fun t => snoc t value) hdecompose
      rw [hassignment] at hsemantic
      change
        (SatisfiesIn M stepFormula (snoc s value) <->
          s 0 ∈ A ∧ value = step (s 0) (s 1))
      exact hsemantic
  · rintro ⟨hclosed, hgraph⟩
    constructor
    · intro x hxM hxA q hqM
      let s : Tuple ZFSet.{u} 2 := snoc (snoc params x) q
      have hsM : TupleIn M s := by
        intro i
        fin_cases i
        · exact hxM
        · exact hqM
      have hsDomain : s ∈ TextbookStepTupleDomain A := by
        change x ∈ A
        exact hxA
      have hvalue := hclosed s hsM hsDomain
      change step x q ∈ M at hvalue
      exact hvalue
    · intro x q value hxM hqM hvalueM
      let s : Tuple ZFSet.{u} 2 := snoc (snoc params x) q
      have hsM : TupleIn M s := by
        intro i
        fin_cases i
        · exact hxM
        · exact hqM
      have hsemantic := hgraph s value hsM hvalueM
      change
        (SatisfiesIn M stepFormula
            (snoc (snoc (snoc params x) q) value) <->
          x ∈ A ∧ value = step x q)
      change
        (SatisfiesIn M stepFormula
            (snoc (snoc (snoc params x) q) value) <->
          x ∈ A ∧ value = step x q) at hsemantic
      exact hsemantic

/-! ## The model-relative well-foundedness consequence -/

/-- The textbook set-minimum hypothesis implies the raw restricted semantic
well-foundedness assertion used inside the transitive model.

For an internal nonempty set whose internally visible members satisfy the
class formula, this produces an internally visible member with no internally
visible predecessor satisfying the relation formula.  In particular,
model-relative well-foundedness is derived here; it is not an extra hypothesis
of the internal recursion builder.  The explicit `hparams` hypothesis records
that the fixed parameters form a legitimate model assignment. -/
theorem exists_internal_relation_minimum
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hmin : HasSetMinimaOn A R)
    (_hparams : forall i, params i ∈ M)
    (hclass : forall x, x ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params x) <->
        x ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall x, x ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) x) <-> ClassRel R y x))
    {z : ZFSet.{u}} (hzM : z ∈ M)
    (hnonempty : exists x : ZFSet.{u}, x ∈ M ∧ x ∈ z)
    (hsubset : forall x : ZFSet.{u}, x ∈ M -> x ∈ z ->
      SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params x)) :
    exists u : ZFSet.{u}, u ∈ M ∧ u ∈ z ∧
      forall v : ZFSet.{u}, v ∈ M -> v ∈ z ->
        Not (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params v) u)) := by
  have hzSubset : (z : Set ZFSet.{u}) ⊆ A := by
    intro x hxz
    have hxM : x ∈ M := htrans.mem_trans hxz hzM
    exact (hclass x hxM).mp (hsubset x hxM hxz)
  have hzNonempty : exists x : ZFSet.{u}, x ∈ z := by
    rcases hnonempty with ⟨x, _hxM, hxz⟩
    exact ⟨x, hxz⟩
  rcases hmin z hzSubset hzNonempty with ⟨u, huz, huMinimal⟩
  have huM : u ∈ M := htrans.mem_trans huz hzM
  refine ⟨u, huM, huz, ?_⟩
  intro v hvM hvz hvFormula
  exact huMinimal v hvz
    ((hrelationFormula v hvM u huM).mp hvFormula)

/-! ## Internal graph lemmas -/

private theorem internalTR_orderedPair_components_mem
    {M x y : ZFSet.{u}} (htrans : M.IsTransitive)
    (hpair : ZFSet.pair x y ∈ M) : x ∈ M ∧ y ∈ M := by
  have hxSingleton : ({x} : ZFSet.{u}) ∈ M :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ M :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  exact ⟨htrans.mem_trans (by simp) hxSingleton,
    htrans.mem_trans (by simp) hxyPair⟩

/-- A model-internal graph whose values agree with an ambient function on an
internal domain yields the actual restriction graph as an element of the
model.  The Replacement formula is the already verified graph-value formula;
no absoluteness statement about the target recursive function is used. -/
theorem predecessorRestrictionGraph_mem_of_internal_graph
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {domain graph : ZFSet.{u}} (hdomainM : domain ∈ M)
    (hgraphM : graph ∈ M) (F : ZFSet.{u} -> ZFSet.{u})
    (hclosed : forall x, x ∈ domain -> F x ∈ M)
    (hgraph : forall x, x ∈ domain -> forall y, y ∈ M ->
      (ZFSet.pair x y ∈ graph <-> y = F x)) :
    predecessorRestrictionGraph domain F ∈ M := by
  let graphParams : Tuple (ZFCarrier M) 1 := ![⟨graph, hgraphM⟩]
  let domainM : ZFCarrier M := ⟨domain, hdomainM⟩
  apply predecessorRestrictionGraph_mem_of_formula hM
    (graphValueFormulaAt (0 : Fin 3) (1 : Fin 3) (2 : Fin 3))
    graphParams domainM F hclosed
  intro x hx y hyM
  let s : Tuple ZFSet.{u} 3 :=
    snoc (snoc (zfCarrierTupleVal graphParams) x) y
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change y ∈ M
      exact hyM
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · change x ∈ M
        exact hM.1.mem_trans hx hdomainM
      · have hk : k = 0 := Subsingleton.elim _ _
        subst k
        change graph ∈ M
        exact hgraphM
  have hsemantic := satisfiesIn_graphValueFormulaAt_iff hM.1
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) s hs
  rw [hsemantic]
  change ZFSet.pair x y ∈ graph <-> y = F x
  exact hgraph x hx y hyM

/-- Values represented by an internal actual local graph belong to the
transitive model throughout the local domain. -/
theorem textbookLocalSolution_value_mem
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {hsetLike : HasSetPredecessorsOn A R}
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {x : ZFSet.{u}}
    (solution : TextbookLocalSolution A R hsetLike step x)
    (hgraphM : solution.graph ∈ M) {t : ZFSet.{u}}
    (ht : t ∈ localRecursionDomain A R hsetLike x) :
    solution.value t ∈ M := by
  have hpairGraph : ZFSet.pair t (solution.value t) ∈ solution.graph := by
    rw [solution.graph_eq]
    exact pair_mem_predecessorRestrictionGraph solution.value ht
  have hpairM : ZFSet.pair t (solution.value t) ∈ M :=
    hM.1.mem_trans hpairGraph hgraphM
  exact (internalTR_orderedPair_components_mem hM.1 hpairM).2

/-- Every predecessor restriction used by an internal local solution belongs
to the model.  It is obtained by Replacement from graph-value satisfaction
inside the already internal local graph. -/
theorem textbookLocalSolution_predecessorGraph_mem
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (solution : TextbookLocalSolution A R hR.2.2 step x)
    (hgraphM : solution.graph ∈ M)
    {top : ZFSet.{u}}
    (htop : top ∈ localRecursionDomain A R hR.2.2 x) :
    predecessorRestrictionGraph
      (displayedPredecessors A R hR.2.2 top) solution.value ∈ M := by
  have htopA : top ∈ A :=
    localRecursionDomain_subset hR.2.2 hxA htop
  have hlocalDomainM : localRecursionDomain A R hR.2.2 x ∈ M :=
    localRecursionDomain_mem_of_isTransitiveZFModel
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR hclosedIn hsetLikeIn hxM hxA
  have htopM : top ∈ M := hM.1.mem_trans htop hlocalDomainM
  have hpredecessorsM : displayedPredecessors A R hR.2.2 top ∈ M :=
    displayedPredecessors_mem_of_satisfiesIn_setLike
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR.2.2 hclosedIn hsetLikeIn htopM htopA
  apply predecessorRestrictionGraph_mem_of_internal_graph hM
    hpredecessorsM hgraphM solution.value
  · intro input hinputPred
    have hinputRel :=
      (displayedPredecessors_spec hR.2.2 htopA input).mp hinputPred |>.2
    have hinputDomain := localRecursionDomain_predecessorClosed
      hR.1 hR.2.2 hxA htop hinputRel
    exact textbookLocalSolution_value_mem hM solution hgraphM hinputDomain
  · intro input hinputPred output _houtputM
    have hinputRel :=
      (displayedPredecessors_spec hR.2.2 htopA input).mp hinputPred |>.2
    have hinputDomain := localRecursionDomain_predecessorClosed
      hR.1 hR.2.2 hxA htop hinputRel
    rw [solution.graph_eq]
    constructor
    · intro hpair
      rcases mem_predecessorRestrictionGraph_iff.mp hpair with
        ⟨other, _hotherDomain, hotherPair⟩
      rcases ZFSet.pair_inj.mp hotherPair with ⟨hinput, houtput⟩
      subst other
      exact houtput.symm
    · intro houtput
      subst output
      exact pair_mem_predecessorRestrictionGraph solution.value hinputDomain

/-- An actual textbook local solution whose graph belongs to the model
satisfies the internal first-order local-solution formula.

All witnesses required by the formula are constructed inside `M`: the local
domain comes from the internal finite-predecessor closure, and every
predecessor restriction graph comes from model Replacement applied to graph
lookup in the already internal local graph. -/
theorem satisfiesIn_localSolutionFormula_of_textbookLocalSolution
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (solution : TextbookLocalSolution A R hR.2.2 step x)
    (hgraphM : solution.graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula)
      (snoc (snoc params x) solution.graph) := by
  have hlocalDomainM : localRecursionDomain A R hR.2.2 x ∈ M :=
    localRecursionDomain_mem_of_isTransitiveZFModel
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR hclosedIn hsetLikeIn hxM hxA
  apply (satisfiesIn_localSolutionFormula_iff hM.1
    classFormula relationFormula stepFormula params x solution.graph
    hparams hxM hgraphM).mpr
  refine ⟨localRecursionDomain A R hR.2.2 x, hlocalDomainM, ?_, ?_, ?_⟩
  · apply (satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
      hM.1 classFormula relationFormula params hclass hrelationFormula
      hR.1 hR.2.2 hclosedIn hxM hxA hlocalDomainM hlocalDomainM).mpr
    rfl
  · constructor
    · intro input hinputM hinputDomain
      have hvalueM : solution.value input ∈ M :=
        textbookLocalSolution_value_mem hM solution hgraphM hinputDomain
      refine ⟨solution.value input, hvalueM, ?_, ?_⟩
      · rw [solution.graph_eq]
        exact pair_mem_predecessorRestrictionGraph solution.value hinputDomain
      · intro other _hotherM hotherGraph
        rw [solution.graph_eq] at hotherGraph
        rcases mem_predecessorRestrictionGraph_iff.mp hotherGraph with
          ⟨source, _hsourceDomain, hpair⟩
        rcases ZFSet.pair_inj.mp hpair with ⟨hsource, hvalue⟩
        subst source
        exact hvalue.symm
    · intro pair _hpairM hpairGraph
      rw [solution.graph_eq] at hpairGraph
      rcases mem_predecessorRestrictionGraph_iff.mp hpairGraph with
        ⟨input, hinputDomain, hpair⟩
      have hinputM : input ∈ M :=
        hM.1.mem_trans hinputDomain hlocalDomainM
      have hvalueM : solution.value input ∈ M :=
        textbookLocalSolution_value_mem hM solution hgraphM hinputDomain
      exact ⟨input, hinputM, hinputDomain, solution.value input,
        hvalueM, hpair.symm⟩
  · intro top htopM htopDomain
    let restriction := predecessorRestrictionGraph
      (displayedPredecessors A R hR.2.2 top) solution.value
    have hrestrictionM : restriction ∈ M :=
      textbookLocalSolution_predecessorGraph_mem
        hM classFormula relationFormula params hR hparams hclass
        hrelationFormula hclosedIn hsetLikeIn hxM hxA solution hgraphM
        htopDomain
    have hvalueM : solution.value top ∈ M :=
      textbookLocalSolution_value_mem hM solution hgraphM htopDomain
    refine ⟨restriction, hrestrictionM, solution.value top, hvalueM,
      ?_, ?_, ?_⟩
    · intro pair hpairM
      constructor
      · intro hpairRestriction
        rcases mem_predecessorRestrictionGraph_iff.mp hpairRestriction with
          ⟨input, hinputPred, hpair⟩
        have htopA : top ∈ A :=
          localRecursionDomain_subset hR.2.2 hxA htopDomain
        have hinputSpec :=
          (displayedPredecessors_spec hR.2.2 htopA input).mp hinputPred
        have hinputDomain := localRecursionDomain_predecessorClosed
          hR.1 hR.2.2 hxA htopDomain hinputSpec.2
        have hinputM : input ∈ M :=
          hM.1.mem_trans hinputDomain hlocalDomainM
        have hinputValueM : solution.value input ∈ M :=
          textbookLocalSolution_value_mem hM solution hgraphM hinputDomain
        refine ⟨?_, input, hinputM, solution.value input,
          hinputValueM, hpair.symm, ?_, ?_⟩
        · rw [solution.graph_eq]
          have hmember := pair_mem_predecessorRestrictionGraph
            solution.value hinputDomain
          rw [hpair] at hmember
          exact hmember
        · exact (hclass input hinputM).mpr hinputSpec.1
        · exact (hrelationFormula input hinputM top htopM).mpr
            hinputSpec.2
      · rintro ⟨hpairGraph, input, hinputM, output, houtputM,
          hpairEq, hinputFormula, hrelationRaw⟩
        have htopA : top ∈ A :=
          localRecursionDomain_subset hR.2.2 hxA htopDomain
        have hinputA : input ∈ A :=
          (hclass input hinputM).mp hinputFormula
        have hinputRel : ClassRel R input top :=
          (hrelationFormula input hinputM top htopM).mp hrelationRaw
        have hinputPred :
            input ∈ displayedPredecessors A R hR.2.2 top :=
          (displayedPredecessors_spec hR.2.2 htopA input).mpr
            ⟨hinputA, hinputRel⟩
        rw [solution.graph_eq] at hpairGraph
        rcases mem_predecessorRestrictionGraph_iff.mp hpairGraph with
          ⟨source, _hsourceDomain, hsourcePair⟩
        have hpairs : ZFSet.pair source (solution.value source) =
            ZFSet.pair input output := hsourcePair.trans hpairEq
        rcases ZFSet.pair_inj.mp hpairs with ⟨hsource, houtput⟩
        subst source
        subst output
        apply mem_predecessorRestrictionGraph_iff.mpr
        exact ⟨input, hinputPred, hpairEq.symm⟩
    · rw [solution.graph_eq]
      exact pair_mem_predecessorRestrictionGraph solution.value htopDomain
    · apply (hstep.2 top restriction (solution.value top)
        htopM hrestrictionM hvalueM).mpr
      refine ⟨localRecursionDomain_subset hR.2.2 hxA htopDomain, ?_⟩
      simpa only [restriction] using solution.satisfies top htopDomain

/-! ## Decoding the formula into an actual local solution -/

/-- A graph satisfying the internal local-solution formula is an actual
textbook local graph.

The actual local domain is required here only as an intermediate membership
fact.  The public internal-recursion builder below derives that fact from the
model axioms and does not expose it as an extra hypothesis. -/
theorem exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x graph : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hgraphM : graph ∈ M)
    (hlocalDomainM : localRecursionDomain A R hR.2.2 x ∈ M)
    (hformula : SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula)
      (snoc (snoc params x) graph)) :
    exists solution : TextbookLocalSolution A R hR.2.2 step x,
      solution.graph = graph := by
  classical
  rcases (satisfiesIn_localSolutionFormula_iff hM.1
      classFormula relationFormula stepFormula params x graph
      hparams hxM hgraphM).mp hformula with
    ⟨domain, hdomainM, hdomainFormula, hfunction, hsteps⟩
  have hdomainEq : domain = localRecursionDomain A R hR.2.2 x :=
    (satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
      hM.1 classFormula relationFormula params hclass hrelationFormula
      hR.1 hR.2.2 hclosedIn hxM hxA hdomainM hlocalDomainM).mp
        hdomainFormula
  subst domain
  let d := localRecursionDomain A R hR.2.2 x
  have hdM : d ∈ M := hlocalDomainM
  have hinputM : forall t : ZFSet.{u}, t ∈ d -> t ∈ M := by
    intro t ht
    exact hM.1.mem_trans ht hdM
  let value : ZFSet.{u} -> ZFSet.{u} := fun t =>
    if ht : t ∈ d then
      Classical.choose (hfunction.1 t (hinputM t ht) ht)
    else ∅
  have hvalueSpec : forall t : ZFSet.{u}, forall ht : t ∈ d,
      value t ∈ M ∧ ZFSet.pair t (value t) ∈ graph ∧
        forall other : ZFSet.{u}, other ∈ M ->
          ZFSet.pair t other ∈ graph -> other = value t := by
    intro t ht
    have hchosen := Classical.choose_spec
      (hfunction.1 t (hinputM t ht) ht)
    simpa only [value, dif_pos ht] using hchosen
  have hgraphEq : graph = predecessorRestrictionGraph d value := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hpairGraph
      have hpairM : pair ∈ M := hM.1.mem_trans hpairGraph hgraphM
      rcases hfunction.2 pair hpairM hpairGraph with
        ⟨input, _hinputM, hinputD, output, houtputM, rfl⟩
      have houtputEq :=
        (hvalueSpec input hinputD).2.2 output houtputM
          (by simpa only using hpairGraph)
      apply mem_predecessorRestrictionGraph_iff.mpr
      exact ⟨input, hinputD, by rw [← houtputEq]⟩
    · intro hpairRestriction
      rcases mem_predecessorRestrictionGraph_iff.mp hpairRestriction with
        ⟨input, hinputD, hpairEq⟩
      rw [← hpairEq]
      exact (hvalueSpec input hinputD).2.1
  have hsatisfies :
      SatisfiesTextbookLocalRecursion A R hR.2.2 step x value := by
    intro top htopD
    have htopM : top ∈ M := hinputM top htopD
    rcases hsteps top htopM htopD with
      ⟨restriction, hrestrictionM, output, houtputM,
        hrestriction, houtputGraph, hstepFormula⟩
    have htopA : top ∈ A :=
      localRecursionDomain_subset hR.2.2 hxA htopD
    have hrestrictionEq : restriction =
        predecessorRestrictionGraph
          (displayedPredecessors A R hR.2.2 top) value := by
      apply ZFSet.ext
      intro pair
      constructor
      · intro hpairRestriction
        have hpairM : pair ∈ M :=
          hM.1.mem_trans hpairRestriction hrestrictionM
        rcases (hrestriction pair hpairM).mp hpairRestriction with
          ⟨hpairGraph, input, hinputM', output', houtputM',
            hpairEq, hinputFormula, hrelationRaw⟩
        have hinputA : input ∈ A :=
          (hclass input hinputM').mp hinputFormula
        have hinputTop : ClassRel R input top :=
          (hrelationFormula input hinputM' top htopM).mp hrelationRaw
        have hinputPred :
            input ∈ displayedPredecessors A R hR.2.2 top :=
          (displayedPredecessors_spec hR.2.2 htopA input).mpr
            ⟨hinputA, hinputTop⟩
        have hinputD : input ∈ d :=
          localRecursionDomain_predecessorClosed hR.1 hR.2.2 hxA
            htopD hinputTop
        have houtputEq : output' = value input :=
          (hvalueSpec input hinputD).2.2 output' houtputM' (by
            rw [hpairEq] at hpairGraph
            exact hpairGraph)
        apply mem_predecessorRestrictionGraph_iff.mpr
        exact ⟨input, hinputPred, by rw [← houtputEq, hpairEq]⟩
      · intro hpairExpected
        rcases mem_predecessorRestrictionGraph_iff.mp hpairExpected with
          ⟨input, hinputPred, hpairEq⟩
        have hinputSpec :=
          (displayedPredecessors_spec hR.2.2 htopA input).mp hinputPred
        have hinputD : input ∈ d :=
          localRecursionDomain_predecessorClosed hR.1 hR.2.2 hxA
            htopD hinputSpec.2
        have hinputM' : input ∈ M := hinputM input hinputD
        have hvalueM : value input ∈ M := (hvalueSpec input hinputD).1
        have hpairM : ZFSet.pair input (value input) ∈ M :=
          kuratowskiPair_mem_of_isTransitiveZFModel hM hinputM' hvalueM
        rw [← hpairEq]
        apply (hrestriction (ZFSet.pair input (value input)) hpairM).mpr
        refine ⟨(hvalueSpec input hinputD).2.1,
          input, hinputM', value input, hvalueM, rfl, ?_, ?_⟩
        · exact (hclass input hinputM').mpr hinputSpec.1
        · exact (hrelationFormula input hinputM' top htopM).mpr
            hinputSpec.2
    have houtputEq : output = value top :=
      (hvalueSpec top htopD).2.2 output houtputM houtputGraph
    have hstepSemantic :=
      (hstep.2 top restriction output htopM hrestrictionM houtputM).mp
        hstepFormula
    have hstepEq : output = step top restriction := by
      exact hstepSemantic.2
    rw [← houtputEq, hstepEq, hrestrictionEq]
  let solution : TextbookLocalSolution A R hR.2.2 step x :=
    { value := value
      graph := graph
      graph_eq := hgraphEq
      satisfies := hsatisfies }
  exact ⟨solution, rfl⟩

/-- The local-solution formula is functional in its graph coordinate.

This is the exact functionality theorem used by the model's Replacement
scheme when collecting predecessor-local graphs. -/
theorem localSolutionFormula_graph_unique
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x graph₁ graph₂ : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hgraph₁M : graph₁ ∈ M) (hgraph₂M : graph₂ ∈ M)
    (hlocalDomainM : localRecursionDomain A R hR.2.2 x ∈ M)
    (hformula₁ : SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula)
      (snoc (snoc params x) graph₁))
    (hformula₂ : SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula)
      (snoc (snoc params x) graph₂)) :
    graph₁ = graph₂ := by
  rcases exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hstep hxM hxA hgraph₁M hlocalDomainM
      hformula₁ with
    ⟨solution₁, hsolution₁⟩
  rcases exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hstep hxM hxA hgraph₂M hlocalDomainM
      hformula₂ with
    ⟨solution₂, hsolution₂⟩
  rw [← hsolution₁, ← hsolution₂, solution₁.graph_eq, solution₂.graph_eq]
  apply predecessorRestrictionGraph_congr
  intro t ht
  exact textbookLocalSolutions_agreeOn_intersection hR hxA hxA
    solution₁ solution₂ t (ZFSet.mem_inter.mpr ⟨ht, ht⟩)

/-! ## The model-internal page-108 local construction -/

/-- At `(params,x)`, assert that there is no model-internal graph satisfying
the local-solution formula.  This is the formula used by Separation to form
the internal bad set in the recursion-existence proof. -/
def noLocalSolutionFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 1) :=
  .neg (.ex (localSolutionFormula
    classFormula relationFormula stepFormula))

@[simp]
theorem satisfiesIn_noLocalSolutionFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x : ZFSet.{u}) :
    SatisfiesIn M
        (noLocalSolutionFormula classFormula relationFormula stepFormula)
        (snoc params x) <->
      Not (exists graph : ZFSet.{u}, graph ∈ M ∧
        SatisfiesIn M
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params x) graph)) := by
  rfl

/-- The literal page-108 parent step.  If every immediate predecessor already
has an internal local solution, Replacement collects the unique child graphs,
Union forms `q`, and Pairing plus Union adjoins the top value. -/
theorem exists_internal_textbookLocalSolution_of_predecessors
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hpredecessorSolutions : forall y : ZFSet.{u}, y ∈ A ->
      ClassRel R y x -> y ∈ M ->
      exists solution : TextbookLocalSolution A R hR.2.2 step y,
        solution.graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params y) solution.graph)) :
    exists solution : TextbookLocalSolution A R hR.2.2 step x,
      solution.graph ∈ M ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) solution.graph) := by
  classical
  let top : {z : ZFSet.{u} // z ∈ A} := ⟨x, hxA⟩
  have htopM : top.1 ∈ M := hxM
  let predecessors := displayedPredecessors A R hR.2.2 top.1
  have hpredecessorsM : predecessors ∈ M :=
    displayedPredecessors_mem_of_satisfiesIn_setLike
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR.2.2 hclosedIn hsetLikeIn htopM top.2
  let childExistence : forall y : ZFCarrier predecessors,
      exists solution : TextbookLocalSolution A R hR.2.2 step y.1,
        solution.graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params y.1) solution.graph) := fun y => by
    have hySpec :=
      (displayedPredecessors_spec hR.2.2 top.2 y.1).mp y.2
    have hyM : y.1 ∈ M :=
      hclosedIn top.1 htopM y.1 hySpec.1 hySpec.2
    exact hpredecessorSolutions y.1 hySpec.1 hySpec.2 hyM
  let children : forall y : ZFCarrier predecessors,
      TextbookLocalSolution A R hR.2.2 step y.1 := fun y =>
    Classical.choose (childExistence y)
  have hchildren : forall y : ZFCarrier predecessors,
      (children y).graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params y.1) (children y).graph) := by
    intro y
    exact Classical.choose_spec (childExistence y)
  let paramsM : Tuple (ZFCarrier M) n := fun i => ⟨params i, hparams i⟩
  have hparamsVal : zfCarrierTupleVal paramsM = params := by
    funext i
    rfl
  let predecessorsM : ZFCarrier M := ⟨predecessors, hpredecessorsM⟩
  have hreplacementFun : forall y : ZFCarrier M, y.1 ∈ predecessorsM.1 ->
      ExistsUnique fun graph : ZFCarrier M =>
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc (zfCarrierTupleVal paramsM) y.1) graph.1) := by
    intro y hyPredecessor
    let yPred : ZFCarrier predecessors := ⟨y.1, hyPredecessor⟩
    have hySpec :=
      (displayedPredecessors_spec hR.2.2 top.2 y.1).mp hyPredecessor
    have hchild := hchildren yPred
    let childGraph : ZFCarrier M := ⟨(children yPred).graph, hchild.1⟩
    refine ⟨childGraph, ?_, ?_⟩
    · rw [hparamsVal]
      exact hchild.2
    · intro other hother
      apply Subtype.ext
      rw [hparamsVal] at hother
      have hlocalDomainM : localRecursionDomain A R hR.2.2 y.1 ∈ M :=
        localRecursionDomain_mem_of_isTransitiveZFModel
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hR hclosedIn hsetLikeIn y.2 hySpec.1
      exact (localSolutionFormula_graph_unique
        (x := y.1) (graph₁ := (children yPred).graph)
        (graph₂ := other.1)
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hstep y.2 hySpec.1 hchild.1 other.2
        hlocalDomainM hchild.2 hother).symm
  let range : ZFSet.{u} := M.sep fun graph =>
    exists y : ZFSet.{u}, y ∈ predecessors ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc (zfCarrierTupleVal paramsM) y) graph)
  have hRangeM : range ∈ M :=
    satisfiesIn_replacementRange_mem_of_isTransitiveZFModel
      hM (localSolutionFormula classFormula relationFormula stepFormula)
      paramsM predecessorsM hreplacementFun
  let q : ZFSet.{u} := ZFSet.sUnion range
  have hqM : q ∈ M := sUnion_mem_of_isTransitiveZFModel hM hRangeM
  have hqEq : q = predecessorLocalGraphUnion hR step children := by
    apply ZFSet.ext
    intro pair
    constructor
    · intro hpairQ
      rcases ZFSet.mem_sUnion.mp hpairQ with
        ⟨graph, hgraphRange, hpairGraph⟩
      rcases ZFSet.mem_sep.mp hgraphRange with
        ⟨hgraphM, y, hyPredecessor, hgraphFormula⟩
      let yPred : ZFCarrier predecessors := ⟨y, hyPredecessor⟩
      have hySpec :=
        (displayedPredecessors_spec hR.2.2 top.2 y).mp hyPredecessor
      have hchild := hchildren yPred
      have hlocalDomainM : localRecursionDomain A R hR.2.2 y ∈ M :=
        localRecursionDomain_mem_of_isTransitiveZFModel
          hM classFormula relationFormula params hparams hclass
          hrelationFormula hR hclosedIn hsetLikeIn
          (hclosedIn top.1 htopM y hySpec.1 hySpec.2) hySpec.1
      rw [hparamsVal] at hgraphFormula
      have hgraphEq := localSolutionFormula_graph_unique
        (x := y) (graph₁ := graph) (graph₂ := (children yPred).graph)
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hstep
        (hclosedIn top.1 htopM y hySpec.1 hySpec.2) hySpec.1
        hgraphM hchild.1 hlocalDomainM hgraphFormula hchild.2
      rw [predecessorLocalGraphUnion]
      apply ZFSet.mem_iUnion.mpr
      exact ⟨yPred, by simpa only [hgraphEq] using hpairGraph⟩
    · intro hpairUnion
      rw [predecessorLocalGraphUnion] at hpairUnion
      rcases ZFSet.mem_iUnion.mp hpairUnion with ⟨yPred, hpairChild⟩
      apply ZFSet.mem_sUnion.mpr
      refine ⟨(children yPred).graph, ?_, hpairChild⟩
      apply ZFSet.mem_sep.mpr
      refine ⟨(hchildren yPred).1, yPred.1, yPred.2, ?_⟩
      rw [hparamsVal]
      exact (hchildren yPred).2
  let glued := gluedPredecessorValue hR step children
  have hgluedClosed : forall y : ZFSet.{u}, y ∈ predecessors ->
      glued y ∈ M := by
    intro y hyPredecessor
    have hyClosure : y ∈ predecessorClosure A R hR.2.2 top.1 :=
      mem_predecessorClosure_iff.mpr
        ⟨0, by simpa only [predecessorLayer_zero] using hyPredecessor⟩
    have hpairUnion : ZFSet.pair y (glued y) ∈
        predecessorLocalGraphUnion hR step children := by
      rw [predecessorLocalGraphUnion_eq_closureGraph
        (hR := hR) (step := step) (children := children) top.2]
      exact pair_mem_predecessorRestrictionGraph glued hyClosure
    have hpairQ : ZFSet.pair y (glued y) ∈ q := by
      rw [hqEq]
      exact hpairUnion
    have hpairM : ZFSet.pair y (glued y) ∈ M :=
      hM.1.mem_trans hpairQ hqM
    exact (internalTR_orderedPair_components_mem hM.1 hpairM).2
  have hgluedGraph : forall y, y ∈ predecessors -> forall value,
      value ∈ M ->
      (ZFSet.pair y value ∈ q <-> value = glued y) := by
    intro y hyPredecessor value _hvalueM
    have hyClosure : y ∈ predecessorClosure A R hR.2.2 top.1 :=
      mem_predecessorClosure_iff.mpr
        ⟨0, by simpa only [predecessorLayer_zero] using hyPredecessor⟩
    rw [hqEq, predecessorLocalGraphUnion_eq_closureGraph
      (hR := hR) (step := step) (children := children) top.2]
    constructor
    · intro hpair
      rcases mem_predecessorRestrictionGraph_iff.mp hpair with
        ⟨source, _hsourceClosure, hsourcePair⟩
      rcases ZFSet.pair_inj.mp hsourcePair with ⟨hsource, hvalue⟩
      subst source
      exact hvalue.symm
    · intro hvalue
      subst value
      exact pair_mem_predecessorRestrictionGraph glued hyClosure
  have hrestrictionM : predecessorRestrictionGraph predecessors glued ∈ M :=
    predecessorRestrictionGraph_mem_of_internal_graph
      hM hpredecessorsM hqM glued hgluedClosed hgluedGraph
  have htopValueM : localTopValue hR step children ∈ M := by
    unfold localTopValue
    exact hstep.1 top.1 htopM top.2
      (predecessorRestrictionGraph predecessors glued) hrestrictionM
  have htopPairM :
      ZFSet.pair top.1 (localTopValue hR step children) ∈ M :=
    kuratowskiPair_mem_of_isTransitiveZFModel hM htopM htopValueM
  have hinsertM :
      insert (ZFSet.pair top.1 (localTopValue hR step children)) q ∈ M :=
    insert_mem_of_isTransitiveZFModel hM htopPairM hqM
  have hextendedM : extendedLocalGraph hR step children ∈ M := by
    have heq : extendedLocalGraph hR step children =
        insert (ZFSet.pair top.1 (localTopValue hR step children)) q := by
      apply ZFSet.ext
      intro pair
      rw [extendedLocalGraph, ZFSet.mem_union, ZFSet.mem_singleton,
        ZFSet.mem_insert_iff, hqEq, or_comm]
    simpa only [heq] using hinsertM
  let solution := assembleTextbookLocalSolution
    (hR := hR) (step := step) (children := children) top.2
  have hsolutionGraphM : solution.graph ∈ M := by
    change extendedLocalGraph hR step children ∈ M
    exact hextendedM
  refine ⟨solution, hsolutionGraphM, ?_⟩
  exact satisfiesIn_localSolutionFormula_of_textbookLocalSolution
    hM classFormula relationFormula stepFormula params hR hparams hclass
    hrelationFormula hclosedIn hsetLikeIn hstep htopM top.2
    solution hsolutionGraphM

/-- Every point of `A ∩ M` has an internal textbook local solution.

This proof follows the model-internal bad-set argument.  For the internal
local domain `d_x`, Separation forms the set of points having no internal
`localSolutionFormula` graph.  If this set were nonempty, the derived internal
minimum lemma would give an `R`-minimal bad point.  All of its immediate
predecessors then have internal local solutions, and the parent-step theorem
constructs one at the bad point, a contradiction.  Thus this theorem actually
uses the model-relative well-foundedness consequence; it is not an ambient
well-founded induction presented as an internal recursion. -/
theorem exists_internal_textbookLocalSolution
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    exists solution : TextbookLocalSolution A R hR.2.2 step x,
      solution.graph ∈ M ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) solution.graph) := by
  classical
  let domain := localRecursionDomain A R hR.2.2 x
  have hdomainM : domain ∈ M :=
    localRecursionDomain_mem_of_isTransitiveZFModel
      hM classFormula relationFormula params hparams hclass
      hrelationFormula hR hclosedIn hsetLikeIn hxM hxA
  let paramsM : Tuple (ZFCarrier M) n := fun i => ⟨params i, hparams i⟩
  have hparamsVal : zfCarrierTupleVal paramsM = params := by
    funext i
    rfl
  let domainM : ZFCarrier M := ⟨domain, hdomainM⟩
  let bad : ZFSet.{u} := domain.sep fun t =>
    SatisfiesIn (M : Set ZFSet.{u})
      (noLocalSolutionFormula classFormula relationFormula stepFormula)
      (snoc (zfCarrierTupleVal paramsM) t)
  have hbadM : bad ∈ M := by
    exact satisfiesIn_sep_mem_of_isTransitiveZFModel hM
      (noLocalSolutionFormula classFormula relationFormula stepFormula)
      paramsM domainM
  by_contra hnoSolution
  have hxDomain : x ∈ domain :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  have hxNoFormula : Not (exists graph : ZFSet.{u}, graph ∈ M ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) graph)) := by
    rintro ⟨graph, hgraphM, hgraphFormula⟩
    rcases exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hstep hxM hxA hgraphM hdomainM
        hgraphFormula with
      ⟨solution, hsolutionGraph⟩
    apply hnoSolution
    refine ⟨solution, ?_, ?_⟩
    · rw [hsolutionGraph]
      exact hgraphM
    · rw [hsolutionGraph]
      exact hgraphFormula
  have hxBad : x ∈ bad := by
    apply ZFSet.mem_sep.mpr
    refine ⟨hxDomain, ?_⟩
    rw [hparamsVal]
    exact (satisfiesIn_noLocalSolutionFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
      params x).mpr hxNoFormula
  have hbadSubsetFormula : forall t : ZFSet.{u}, t ∈ M -> t ∈ bad ->
      SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params t) := by
    intro t htM htBad
    have htDomain : t ∈ domain := (ZFSet.mem_sep.mp htBad).1
    have htA : t ∈ A :=
      localRecursionDomain_subset hR.2.2 hxA htDomain
    exact (hclass t htM).mpr htA
  rcases exists_internal_relation_minimum hM.1
      classFormula relationFormula params hR.2.1 hparams hclass
      hrelationFormula hbadM ⟨x, hxM, hxBad⟩ hbadSubsetFormula with
    ⟨top, htopM, htopBad, htopMinimal⟩
  have htopDomain : top ∈ domain := (ZFSet.mem_sep.mp htopBad).1
  have htopA : top ∈ A :=
    localRecursionDomain_subset hR.2.2 hxA htopDomain
  have htopNoFormulaRaw := (ZFSet.mem_sep.mp htopBad).2
  rw [hparamsVal] at htopNoFormulaRaw
  have htopNoFormula : Not (exists graph : ZFSet.{u}, graph ∈ M ∧
      SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params top) graph)) :=
    (satisfiesIn_noLocalSolutionFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
      params top).mp htopNoFormulaRaw
  have hpredecessorSolutions : forall y : ZFSet.{u}, y ∈ A ->
      ClassRel R y top -> y ∈ M ->
      exists solution : TextbookLocalSolution A R hR.2.2 step y,
        solution.graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params y) solution.graph) := by
    intro y hyA hyt hyM
    have hyDomain : y ∈ domain :=
      localRecursionDomain_predecessorClosed
        hR.1 hR.2.2 hxA htopDomain hyt
    have hyNotBad : y ∉ bad := by
      intro hyBad
      exact (htopMinimal y hyM hyBad)
        ((hrelationFormula y hyM top htopM).mpr hyt)
    have hyHasFormula : exists graph : ZFSet.{u}, graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params y) graph) := by
      by_contra hyNoFormula
      apply hyNotBad
      apply ZFSet.mem_sep.mpr
      refine ⟨hyDomain, ?_⟩
      rw [hparamsVal]
      exact (satisfiesIn_noLocalSolutionFormula_iff
        (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
        params y).mpr hyNoFormula
    rcases hyHasFormula with ⟨graph, hgraphM, hgraphFormula⟩
    have hyLocalDomainM : localRecursionDomain A R hR.2.2 y ∈ M :=
      localRecursionDomain_mem_of_isTransitiveZFModel
        hM classFormula relationFormula params hparams hclass
        hrelationFormula hR hclosedIn hsetLikeIn hyM hyA
    rcases exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hstep hyM hyA hgraphM hyLocalDomainM
        hgraphFormula with
      ⟨solution, hsolutionGraph⟩
    refine ⟨solution, ?_, ?_⟩
    · rw [hsolutionGraph]
      exact hgraphM
    · rw [hsolutionGraph]
      exact hgraphFormula
  rcases exists_internal_textbookLocalSolution_of_predecessors
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hsetLikeIn hstep htopM htopA
      hpredecessorSolutions with
    ⟨solution, hsolutionGraphM, hsolutionFormula⟩
  exact htopNoFormula
    ⟨solution.graph, hsolutionGraphM, hsolutionFormula⟩

/-! ## The formula-represented global model solution -/

/-- The page-108 global function is closed in `M` on `A ∩ M`.

The proof does not infer closure from the ambient chosen local graph.  It
first constructs an internal local graph at `x`, then identifies its value at
the top with the already defined page-108 global function. -/
theorem textbookGlobalRecursionFromLocalGraphs_mem
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A) :
    textbookGlobalRecursionFromLocalGraphs hR step x ∈ M := by
  rcases exists_internal_textbookLocalSolution
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hsetLikeIn hstep hxM hxA with
    ⟨solution, hgraphM, _hformula⟩
  have hxDomain : x ∈ localRecursionDomain A R hR.2.2 x :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  rw [textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
    hR step hxA solution hxDomain]
  exact textbookLocalSolution_value_mem hM solution hgraphM hxDomain

/-- The recursive-value formula represents exactly the page-108 global
function at the fixed parameter tuple. -/
theorem satisfiesIn_recursionValueFormula_iff_globalLocalRecursion
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    {x value : ZFSet.{u}} (hxM : x ∈ M) (hvalueM : value ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (recursionValueFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) value) <->
      x ∈ A ∧
        value = textbookGlobalRecursionFromLocalGraphs hR step x := by
  rw [satisfiesIn_recursionValueFormula_iff hM.1
    classFormula relationFormula stepFormula params x value
    hparams hxM hvalueM]
  constructor
  · rintro ⟨hclassFormula, graph, hgraphM, hgraphFormula, hpairGraph⟩
    have hxA : x ∈ A := (hclass x hxM).mp hclassFormula
    have hlocalDomainM : localRecursionDomain A R hR.2.2 x ∈ M :=
      localRecursionDomain_mem_of_isTransitiveZFModel
        hM classFormula relationFormula params hparams hclass
        hrelationFormula hR hclosedIn hsetLikeIn hxM hxA
    rcases exists_textbookLocalSolution_of_satisfiesIn_localSolutionFormula
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hstep hxM hxA hgraphM hlocalDomainM
        hgraphFormula with
      ⟨solution, hsolutionGraph⟩
    have hpairSolution : ZFSet.pair x value ∈ solution.graph := by
      rw [hsolutionGraph]
      exact hpairGraph
    rw [solution.graph_eq] at hpairSolution
    rcases mem_predecessorRestrictionGraph_iff.mp hpairSolution with
      ⟨source, _hsourceDomain, hsourcePair⟩
    rcases ZFSet.pair_inj.mp hsourcePair with ⟨hsource, hsourceValue⟩
    subst source
    have hxDomain : x ∈ localRecursionDomain A R hR.2.2 x :=
      mem_localRecursionDomain_iff.mpr (Or.inl rfl)
    have hglobal := textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
      hR step hxA solution hxDomain
    exact ⟨hxA, hsourceValue.symm.trans hglobal.symm⟩
  · rintro ⟨hxA, hvalue⟩
    rcases exists_internal_textbookLocalSolution
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hsetLikeIn hstep hxM hxA with
      ⟨solution, hgraphM, hgraphFormula⟩
    have hxDomain : x ∈ localRecursionDomain A R hR.2.2 x :=
      mem_localRecursionDomain_iff.mpr (Or.inl rfl)
    have hglobal := textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
      hR step hxA solution hxDomain
    refine ⟨(hclass x hxM).mpr hxA, solution.graph, hgraphM,
      hgraphFormula, ?_⟩
    rw [solution.graph_eq]
    have hpair := pair_mem_predecessorRestrictionGraph solution.value hxDomain
    rw [hvalue, hglobal]
    exact hpair

/-! ## The completed fixed-parameter absoluteness theorem -/

/-- Unary function absoluteness at a fixed tuple of parameters.  This is the
parameterized analogue of `UnaryFunctionAbsoluteTo`; unlike a tuple-domain
encoding, it imposes no condition on unrelated parameter prefixes. -/
def UnaryFunctionAbsoluteAt (M : Set ZFSet.{u}) {n : Nat}
    (params : Tuple ZFSet.{u} n) (A : Set ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) (graph : FOFormula (n + 2)) : Prop :=
  (forall x, x ∈ M -> x ∈ A -> F x ∈ M) ∧
    forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn M graph (snoc (snoc params x) y) <->
        x ∈ A ∧ y = F x)

/-- With no parameters, fixed-parameter unary absoluteness is exactly the
existing `UnaryFunctionAbsoluteTo` notion. -/
theorem unaryFunctionAbsoluteAt_zero_iff_unaryFunctionAbsoluteTo
    (M : Set ZFSet.{u}) (params : Tuple ZFSet.{u} 0)
    (A : Set ZFSet.{u}) (F : ZFSet.{u} -> ZFSet.{u})
    (graph : FOFormula 2) :
    UnaryFunctionAbsoluteAt M params A F graph <->
      UnaryFunctionAbsoluteTo M A F graph := by
  have hsingle : forall x : ZFSet.{u}, snoc params x = ![x] := by
    intro x
    funext i
    fin_cases i
    rfl
  constructor
  · rintro ⟨hclosed, hgraph⟩
    refine ⟨hclosed, ?_⟩
    intro x y hxM hyM
    have hsemantic := hgraph x y hxM hyM
    rw [hsingle x] at hsemantic
    exact hsemantic
  · rintro ⟨hclosed, hgraph⟩
    refine ⟨hclosed, ?_⟩
    intro x y hxM hyM
    have hsemantic := hgraph x y hxM hyM
    rw [hsingle x]
    exact hsemantic

/-- Fixed-parameter form of the textbook recursion-absoluteness theorem.

`F` is only assumed to satisfy the ambient recursion equation where the
comparison is needed, namely on `A ∩ M`.  The model solution `H` is the
page-108 global function assembled from local graphs.  Its internal graph
witnesses are constructed above from Replacement, Union, Separation/graph
restriction, and Pairing; agreement with `F` is then the textbook minimal-bad-
point argument packaged by `recursionSolutions_agreeOn_modelIntersection`. -/
theorem unaryFunctionAbsoluteAt_of_textbookRecursion
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hparams : forall i, params i ∈ M)
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F : ZFSet.{u} -> ZFSet.{u}}
    (hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula)
    (hF : forall x, x ∈ modelIntersectionZF M A ->
      F x = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) F)) :
    UnaryFunctionAbsoluteAt (M : Set ZFSet.{u}) params A F
      (recursionValueFormula classFormula relationFormula stepFormula) := by
  let H := textbookGlobalRecursionFromLocalGraphs hR step
  have hH : forall x, x ∈ modelIntersectionZF M A ->
      H x = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) H) := by
    intro x hx
    exact textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
      hR step x (mem_modelIntersectionZF_iff.mp hx).2
  have hHclosed : forall x, x ∈ M -> x ∈ A -> H x ∈ M := by
    intro x hxM hxA
    exact textbookGlobalRecursionFromLocalGraphs_mem
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hsetLikeIn hstep hxM hxA
  have hHgraph : forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u})
          (recursionValueFormula classFormula relationFormula stepFormula)
          (snoc (snoc params x) y) <-> x ∈ A ∧ y = H x) := by
    intro x y hxM hyM
    exact satisfiesIn_recursionValueFormula_iff_globalLocalRecursion
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hsetLikeIn hstep hxM hyM
  have hagree := recursionSolutions_agreeOn_modelIntersection
    hR.1 hR.2.1
    (fun x hxA => displayedPredecessors_spec hR.2.2 hxA)
    hclosedIn hF hH
  constructor
  · intro x hxM hxA
    rw [hagree x hxA hxM]
    exact hHclosed x hxM hxA
  · intro x y hxM hyM
    rw [hHgraph x y hxM hyM]
    constructor
    · rintro ⟨hxA, hyH⟩
      exact ⟨hxA, hyH.trans (hagree x hxA hxM).symm⟩
    · rintro ⟨hxA, hyF⟩
      exact ⟨hxA, hyF.trans (hagree x hxA hxM)⟩

/-! ## Standard parameter-free public interface -/

/-- Parameter-free textbook recursion absoluteness, stated entirely through
the existing library notions `ClassAbsoluteTo`, `RelationAbsoluteTo`, and
`FunctionAbsoluteTo`.

The hypotheses are the textbook conditions: ambient well-founded set-like
`R` on `A`, absoluteness of `A` and `R`, the internal set-likeness assertion,
predecessor closure (condition III), absoluteness of the recursion functional,
and the ambient recursion equation for `F`.  The conclusion is the standard
function-absoluteness statement, not a custom weakened surrogate. -/
theorem functionAbsoluteTo_of_textbookRecursion
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (classFormula : FOFormula 1)
    (relationFormula : FOFormula 2)
    (stepFormula : FOFormula 3)
    (params : Tuple ZFSet.{u} 0)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (hclassAbsolute : ClassAbsoluteTo (M : Set ZFSet.{u}) A classFormula)
    (hrelationAbsolute : RelationAbsoluteTo (M : Set ZFSet.{u})
      R relationFormula)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    (hsetLikeIn : SatisfiesIn (M : Set ZFSet.{u})
      (setLikeRelationOnFormula classFormula relationFormula) params)
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F : ZFSet.{u} -> ZFSet.{u}}
    (hstepAbsolute : FunctionAbsoluteTo (M : Set ZFSet.{u})
      (TextbookStepTupleDomain A) (textbookStepTupleFunction step)
      stepFormula)
    (hF : SatisfiesTextbookClassRecursion A R hR.2.2 step F) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) (UnaryTupleDomain A)
      (fun s : Tuple ZFSet.{u} 1 => F (s 0))
      (recursionValueFormula classFormula relationFormula stepFormula) := by
  have hparams : forall i, params i ∈ M := by
    intro i
    exact Fin.elim0 i
  have hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A) := by
    intro z hzM
    have hassignment : snoc params z = ![z] := by
      funext i
      fin_cases i
      rfl
    rw [hassignment]
    exact hclassAbsolute z hzM
  have hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z) := by
    intro y hyM z hzM
    have hassignment : snoc (snoc params y) z = ![y, z] := by
      funext i
      fin_cases i <;> rfl
    have htupleM : TupleIn (M : Set ZFSet.{u}) ![y, z] := by
      intro i
      fin_cases i
      · exact hyM
      · exact hzM
    rw [hassignment]
    exact hrelationAbsolute ![y, z] htupleM
  have hstep : TextbookStepAbsoluteAt (M : Set ZFSet.{u})
      params A step stepFormula :=
    (textbookStepAbsoluteAt_zero_iff_functionAbsoluteTo
      (M : Set ZFSet.{u}) params A step stepFormula).mpr hstepAbsolute
  let H := textbookGlobalRecursionFromLocalGraphs hR step
  have hFrestricted : forall x, x ∈ modelIntersectionZF M A ->
      F x = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) F) := by
    intro x hx
    exact hF x (mem_modelIntersectionZF_iff.mp hx).2
  have hH : forall x, x ∈ modelIntersectionZF M A ->
      H x = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) H) := by
    intro x hx
    exact textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
      hR step x (mem_modelIntersectionZF_iff.mp hx).2
  have hHclosed : forall x, x ∈ M -> x ∈ A -> H x ∈ M := by
    intro x hxM hxA
    exact textbookGlobalRecursionFromLocalGraphs_mem
      hM classFormula relationFormula stepFormula params hR hparams hclass
      hrelationFormula hclosedIn hsetLikeIn hstep hxM hxA
  have hHgraph : forall x y, x ∈ M -> y ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u})
          (recursionValueFormula classFormula relationFormula stepFormula)
          (snoc ![x] y) <-> x ∈ A ∧ y = H x) := by
    intro x y hxM hyM
    have hsemantic :=
      satisfiesIn_recursionValueFormula_iff_globalLocalRecursion
        hM classFormula relationFormula stepFormula params hR hparams hclass
        hrelationFormula hclosedIn hsetLikeIn hstep hxM hyM
    have hsingle : snoc params x = ![x] := by
      funext i
      fin_cases i
      rfl
    rw [hsingle] at hsemantic
    exact hsemantic
  exact functionAbsoluteTo_of_recursiveModelSolution
    hR.1 hR.2.1
    (fun x hxA => displayedPredecessors_spec hR.2.2 hxA)
    hclosedIn hFrestricted hH
    (recursionValueFormula classFormula relationFormula stepFormula)
    hHclosed hHgraph

end

end Constructible.Model
