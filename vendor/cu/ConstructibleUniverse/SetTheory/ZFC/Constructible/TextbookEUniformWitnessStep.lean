/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessFormula
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.ReplacementFunctionGraphLCarrier

/-!
# One simultaneous textbook E witness step

This file forms the actual internal request set

`(omega x (omega \ {0})) x { finite tuple graphs over seed }`

and applies Replacement to the total formula from
`TextbookEUniformWitnessFormula`.  Replacement produces both its genuine
range and its genuine Kuratowski function graph in `L`.  The resulting step
adjoins the range to the seed and simultaneously closes under every decoded
textbook E witness task.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The internal request domain -/

/-- All task/prefix requests for one seed, represented by an actual set in L. -/
def textbookEUniformWitnessRequestDomain
    (seed : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier textbookEWitnessTaskDomain
    (ContinuumFormula.internalFiniteTupleSpaces seed)

@[simp]
theorem textbookEUniformWitnessRequestDomain_val
    (seed : LCarrier.{u}) :
    (textbookEUniformWitnessRequestDomain seed).1 =
      ZFSet.prod textbookEWitnessTaskDomain.1
        (ContinuumFormula.internalFiniteTupleSpaces seed).1 :=
  rfl

@[simp]
theorem mem_textbookEUniformWitnessRequestDomain_iff
    (seed request : LCarrier.{u}) :
    request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 <->
      ∃ task prefixGraph : LCarrier.{u},
        task.1 ∈ textbookEWitnessTaskDomain.1 /\
        prefixGraph.1 ∈
          (ContinuumFormula.internalFiniteTupleSpaces seed).1 /\
        request.1 = ZFSet.pair task.1 prefixGraph.1 := by
  rw [textbookEUniformWitnessRequestDomain_val, ZFSet.mem_prod]
  constructor
  · rintro ⟨task, htask, prefixGraph, hprefixGraph, hrequest⟩
    let taskL : LCarrier.{u} :=
      ⟨task, mem_L_of_mem htask textbookEWitnessTaskDomain.2⟩
    let prefixGraphL : LCarrier.{u} :=
      ⟨prefixGraph,
        mem_L_of_mem hprefixGraph
          (ContinuumFormula.internalFiniteTupleSpaces seed).2⟩
    exact ⟨taskL, prefixGraphL, htask, hprefixGraph, hrequest⟩
  · rintro ⟨task, prefixGraph, htask, hprefixGraph, hrequest⟩
    exact ⟨task.1, htask, prefixGraph.1, hprefixGraph, hrequest⟩

/-- The canonical internal code of the task `(code, arity + 1)`. -/
def textbookEUniformTaskLCarrier (code arity : Nat) : LCarrier.{u} :=
  orderedPairLCarrier
    (TextbookNatFormula.textbookNatCodeLCarrier code)
    (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1))

/-- The canonical request obtained by pairing a decoded task with a prefix. -/
def textbookEUniformRequestLCarrier
    (code arity : Nat) (prefixGraph : LCarrier.{u}) : LCarrier.{u} :=
  orderedPairLCarrier (textbookEUniformTaskLCarrier code arity) prefixGraph

theorem textbookEUniformTaskLCarrier_mem
    (code arity : Nat) :
    (textbookEUniformTaskLCarrier code arity).1 ∈
      textbookEWitnessTaskDomain.1 := by
  apply (mem_textbookEWitnessTaskDomain_iff
    (textbookEUniformTaskLCarrier code arity).1).mpr
  exact ⟨code, arity, rfl⟩

theorem textbookEUniformRequestLCarrier_mem
    {seed prefixGraph : LCarrier.{u}} {code arity : Nat}
    (hprefixGraph :
      prefixGraph.1 ∈
        (ContinuumFormula.finiteTupleSpaceLCarrier seed arity).1) :
    (textbookEUniformRequestLCarrier code arity prefixGraph).1 ∈
      (textbookEUniformWitnessRequestDomain seed).1 := by
  apply (mem_textbookEUniformWitnessRequestDomain_iff seed
    (textbookEUniformRequestLCarrier code arity prefixGraph)).mpr
  refine ⟨textbookEUniformTaskLCarrier code arity, prefixGraph,
    textbookEUniformTaskLCarrier_mem code arity, ?_, rfl⟩
  apply (ContinuumFormula.mem_internalFiniteTupleSpaces_iff
    seed prefixGraph).mpr
  exact ⟨arity, hprefixGraph⟩

/-! ## Functionality of the total formula -/

private theorem selected_property_of_formula
    {U seed prefixGraph y : LCarrier.{u}} {arity code : Nat}
    (hy :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y]) :
    y.1 ∈
        (textbookEWitnessCandidates U
          (textbookEZFLCarrier U (arity + 1) code)
          prefixGraph
          (TextbookNatFormula.textbookNatCodeLCarrier arity)).1 /\
      ∀ z : LCarrier.{u},
        z.1 ∈
          (textbookEWitnessCandidates U
            (textbookEZFLCarrier U (arity + 1) code)
            prefixGraph
            (TextbookNatFormula.textbookNatCodeLCarrier arity)).1 ->
          ¬ GraphRel (canonicalWitnessOrder U) z y := by
  have hdecoded :=
    (satisfies_textbookEUniformSelectedFormula_decoded_iff
      U seed (canonicalWitnessOrder U) prefixGraph y arity code).mp hy
  constructor
  · apply (mem_textbookEWitnessCandidates_iff
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity) y).mpr
    exact ⟨hdecoded.2.1, hdecoded.2.2.1⟩
  · intro z hz
    have hzData := (mem_textbookEWitnessCandidates_iff
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity) z).mp hz
    exact hdecoded.2.2.2 z hzData.1 hzData.2

theorem textbookEUniformSelected_unique_decoded
    (U seed prefixGraph y y' : LCarrier.{u}) (arity code : Nat)
    (hy :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y])
    (hy' :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y']) :
    y' = y := by
  have hyProperty := selected_property_of_formula hy
  have hy'Property := selected_property_of_formula hy'
  rcases existsUnique_textbookEWitnessMinimum
      U (textbookEZFLCarrier U (arity + 1) code)
      prefixGraph
      (TextbookNatFormula.textbookNatCodeLCarrier arity)
      ⟨y, hyProperty.1⟩ with
    ⟨minimum, hminimum, hunique⟩
  have hyEq : y = minimum := hunique y hyProperty
  have hy'Eq : y' = minimum := hunique y' hy'Property
  exact hy'Eq.trans hyEq.symm

private theorem uniform_total_assignment
    (U seed request output : LCarrier.{u}) :
    snoc (snoc ![U, seed, canonicalWitnessOrder U] request) output =
      ![U, seed, canonicalWitnessOrder U, request, output] := by
  funext i
  fin_cases i <;> rfl

/--
The total formula has exactly one output on every member of the internal
request domain.  The proof decodes the task only in the correctness
argument; the object-language operation itself remains the fixed formula.
-/
theorem textbookEUniformTotalFormula_existsUnique
    (seed U request : LCarrier.{u})
    (hrequest :
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1) :
    ExistsUnique fun output : LCarrier.{u} =>
      FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, canonicalWitnessOrder U, request, output] := by
  rcases (mem_textbookEUniformWitnessRequestDomain_iff seed request).mp
      hrequest with
    ⟨task, prefixGraph, htask, _hprefixAny, hrequestRaw⟩
  rcases (mem_textbookEWitnessTaskDomain_iff task.1).mp htask with
    ⟨code, arity, htaskRaw⟩
  have hrequestEq :
      request =
        textbookEUniformRequestLCarrier code arity prefixGraph := by
    apply Subtype.ext
    change request.1 =
      ZFSet.pair
        (ZFSet.pair (natCode code) (natCode (arity + 1)))
        prefixGraph.1
    rw [hrequestRaw, htaskRaw]
  subst request
  by_cases hselected : ∃ y : LCarrier.{u},
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y]
  · rcases hselected with ⟨y, hy⟩
    refine ⟨y,
      (satisfies_textbookEUniformTotalFormula
        U seed (canonicalWitnessOrder U)
        (textbookEUniformRequestLCarrier code arity prefixGraph) y).mpr
          (Or.inl hy), ?_⟩
    intro other hother
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) other).mp
        hother with
      hotherSelected | ⟨_hotherEmpty, hnone⟩
    · exact textbookEUniformSelected_unique_decoded
        U seed prefixGraph y other arity code hy hotherSelected
    · exact (hnone ⟨y, hy⟩).elim
  · refine ⟨emptyLCarrier,
      (satisfies_textbookEUniformTotalFormula
        U seed (canonicalWitnessOrder U)
        (textbookEUniformRequestLCarrier code arity prefixGraph)
        emptyLCarrier).mpr
          (Or.inr ⟨rfl, hselected⟩), ?_⟩
    intro other hother
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) other).mp
        hother with
      hotherSelected | ⟨hotherEmpty, _hnone⟩
    · exact (hselected ⟨other, hotherSelected⟩).elim
    · exact hotherEmpty

/-! ## Replacement range and graph -/

/-- The actual range and function graph produced by uniform Replacement. -/
structure TextbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) where
  graph : LCarrier.{u}
  range : LCarrier.{u}
  isFunctionGraph :
    IsFunctionGraph LMem graph
      (textbookEUniformWitnessRequestDomain seed) range
  mem_range_iff : ∀ output : LCarrier.{u},
    output.1 ∈ range.1 <->
      ∃ request : LCarrier.{u},
        request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output]
  graphValue_iff : ∀ request output : LCarrier.{u},
    GraphValue LMem graph request output <->
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
      FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, canonicalWitnessOrder U, request, output]
  rangeCovered : ∀ output : LCarrier.{u}, output.1 ∈ range.1 ->
    ∃ request : LCarrier.{u},
      request.1 ∈ (textbookEUniformWitnessRequestDomain seed).1 /\
      GraphValue LMem graph request output

/--
Replacement constructs a genuine internal range and a genuine internal
Kuratowski graph for the total request operation.
-/
theorem exists_textbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) :
    Nonempty (TextbookEUniformWitnessReplacementData seed U) := by
  let params : Tuple LCarrier.{u} 3 :=
    ![U, seed, canonicalWitnessOrder U]
  let domain := textbookEUniformWitnessRequestDomain seed
  have hfun : ∀ request : LCarrier.{u}, request.1 ∈ domain.1 ->
      ExistsUnique fun output : LCarrier.{u} =>
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          (snoc (snoc params request) output) := by
    intro request hrequest
    simpa only [params, uniform_total_assignment] using
      textbookEUniformTotalFormula_existsUnique seed U request hrequest
  rcases exists_replacementLCarrier
      textbookEUniformTotalFormula params domain hfun with
    ⟨range, hrange⟩
  rcases exists_replacementFunctionGraphLCarrier
      textbookEUniformTotalFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : ∀ request output : LCarrier.{u},
      GraphValue LMem graph request output <->
        request.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output] := by
    intro request output
    constructor
    · rintro ⟨pair, hpairGraph, hpairIs⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨request', hrequest', output', houtput', hpairEq⟩
      have hpairCoordinates :=
        ZFSet.pair_inj.mp
          (hpairEq.symm.trans
            ((isKuratowskiPairOf_lCarrier_iff
              pair request output).mp hpairIs))
      have hrequestEq : request' = request :=
        Subtype.ext hpairCoordinates.1
      have houtputEq : output' = output :=
        Subtype.ext hpairCoordinates.2
      subst request'
      subst output'
      simpa only [params, uniform_total_assignment] using
        And.intro hrequest' houtput'
    · rintro ⟨hrequest, houtput⟩
      let pair := orderedPairLCarrier request output
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        refine ⟨request, hrequest, output, ?_, rfl⟩
        simpa only [params, uniform_total_assignment] using houtput
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair request output).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain range := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨request, hrequest, output, houtput, hpairEq⟩
    have houtputRange : output.1 ∈ range.1 := by
      apply (hrange output).mpr
      exact ⟨request, hrequest, houtput⟩
    exact ⟨request, hrequest, output, houtputRange,
      (isKuratowskiPairOf_lCarrier_iff
        pair request output).mpr hpairEq⟩
  have htotal : ∀ request : LCarrier.{u}, request.1 ∈ domain.1 ->
      HasUniqueImage LMem graph request range := by
    intro request hrequest
    rcases hfun request hrequest with
      ⟨output, houtput, houtputUnique⟩
    have houtputRange : output.1 ∈ range.1 := by
      apply (hrange output).mpr
      exact ⟨request, hrequest, houtput⟩
    refine ⟨output, houtputRange,
      (hvalue request output).mpr
        ⟨hrequest, by
          simpa only [params, uniform_total_assignment] using houtput⟩,
      ?_⟩
    intro other _hotherRange hotherValue
    apply houtputUnique other
    have hother := (hvalue request other).mp hotherValue |>.2
    simpa only [params, uniform_total_assignment] using hother
  have hmemRange : ∀ output : LCarrier.{u}, output.1 ∈ range.1 <->
      ∃ request : LCarrier.{u}, request.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, seed, canonicalWitnessOrder U, request, output] := by
    intro output
    rw [hrange]
    simp only [params, uniform_total_assignment]
  refine ⟨{
    graph := graph
    range := range
    isFunctionGraph := ⟨hbetween, htotal⟩
    mem_range_iff := ?_
    graphValue_iff := ?_
    rangeCovered := ?_
  }⟩
  · exact hmemRange
  · intro request output
    simpa only [domain] using hvalue request output
  · intro output houtput
    rcases (hmemRange output).mp houtput with
      ⟨request, hrequest, hformula⟩
    refine ⟨request, hrequest, ?_⟩
    apply (hvalue request output).mpr
    exact ⟨hrequest, hformula⟩

/-- A canonical package of the Replacement witnesses. -/
noncomputable def textbookEUniformWitnessReplacementData
    (seed U : LCarrier.{u}) :
    TextbookEUniformWitnessReplacementData seed U :=
  Classical.choice (exists_textbookEUniformWitnessReplacementData seed U)

/-- Retain the seed and adjoin the whole uniform Replacement range. -/
def textbookEUniformWitnessStep
    (seed U : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier seed
    (textbookEUniformWitnessReplacementData seed U).range

theorem seed_subset_textbookEUniformWitnessStep
    (seed U : LCarrier.{u}) :
    seed.1 ⊆ (textbookEUniformWitnessStep seed U).1 := by
  intro x hx
  let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx seed.2⟩
  exact (mem_unionLCarrier_iff seed
    (textbookEUniformWitnessReplacementData seed U).range xL).mpr
      (Or.inl hx)

theorem textbookEUniformWitnessStep_subset
    {seed U : LCarrier.{u}} (hseed : seed.1 ⊆ U.1)
    (hempty : emptyLCarrier.1 ∈ U.1) :
    (textbookEUniformWitnessStep seed U).1 ⊆ U.1 := by
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx (textbookEUniformWitnessStep seed U).2⟩
  rcases (mem_unionLCarrier_iff seed
      (textbookEUniformWitnessReplacementData seed U).range xL).mp hx with
    hxSeed | hxRange
  · exact hseed hxSeed
  · rcases
      (textbookEUniformWitnessReplacementData seed U).mem_range_iff xL |>.mp
        hxRange with
      ⟨request, _hrequest, htotal⟩
    rcases (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U) request xL).mp htotal with
      hselected | ⟨hemptyEq, _hnone⟩
    · rcases
        (satisfies_textbookEUniformSelectedFormula
          U seed (canonicalWitnessOrder U) request xL).mp hselected with
        ⟨_task, _prefixGraph, _code, _positiveArity, _arity,
          _relation, _space, _hrequestEq, _htaskEq, _hsuccessor,
          _hrelation, _hspace, _hprefix, hxU, _hextension, _hminimal⟩
      exact hxU
    · have hxEq : xL.1 = emptyLCarrier.1 :=
        congrArg Subtype.val hemptyEq
      change x = emptyLCarrier.1 at hxEq
      rw [hxEq]
      exact hempty

/-! ## Simultaneous witness closure -/

/--
One-step witness closure has separate parameter and output sets.  This is
the exact induction invariant used before taking the union of the omega
iteration.
-/
def ClosesUnderTextbookEWitnessAtFrom
    (parameters outputs : Set ZFSet.{u}) (U : ZFSet.{u})
    (arity code : Nat) : Prop :=
  ∀ (params : Tuple (ZFCarrier U) arity),
    (∀ i, (params i).1 ∈ parameters) ->
    (∃ x : ZFCarrier U,
      textbookTupleGraph (snoc params x) ∈
        textbookEZF U (natCode (arity + 1)) (natCode code)) ->
    ∃ x : ZFCarrier U,
      x.1 ∈ outputs /\
      textbookTupleGraph (snoc params x) ∈
        textbookEZF U (natCode (arity + 1)) (natCode code)

private theorem textbookTupleGraph_change_codomain_uniform
    {seed U : ZFSet.{u}} {arity : Nat}
    (params : Tuple (ZFCarrier U) arity)
    (hparams : ∀ i, (params i).1 ∈ seed) :
    textbookTupleGraph (fun i => ⟨(params i).1, hparams i⟩) =
      textbookTupleGraph params := by
  apply ZFSet.ext
  intro q
  rw [mem_textbookTupleGraph_iff, mem_textbookTupleGraph_iff]

/--
The uniform Replacement step simultaneously supplies a witness for every
textbook E task and every seed-valued parameter tuple.
-/
theorem textbookEUniformWitnessStep_closesAt
    (seed U : LCarrier.{u}) (arity code : Nat) :
    ClosesUnderTextbookEWitnessAtFrom seed.1
      (textbookEUniformWitnessStep seed U).1 U.1 arity code := by
  intro params hparams hexists
  let paramsSeed : Tuple (ZFCarrier seed.1) arity :=
    fun i => ⟨(params i).1, hparams i⟩
  have hprefixEq :
      textbookTupleGraph paramsSeed = textbookTupleGraph params :=
    textbookTupleGraph_change_codomain_uniform params hparams
  let prefixGraph : LCarrier.{u} :=
    ⟨textbookTupleGraph params,
      textbookTupleGraph_mem_L U.2 params⟩
  have hprefixSpace :
      prefixGraph.1 ∈
        (ContinuumFormula.finiteTupleSpaceLCarrier seed arity).1 := by
    change textbookTupleGraph params ∈ textbookTupleSpace seed.1 arity
    rw [← hprefixEq]
    exact textbookTupleGraph_mem_tupleSpace paramsSeed
  let relation : LCarrier.{u} :=
    textbookEZFLCarrier U (arity + 1) code
  let arityL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier arity
  rcases hexists with ⟨x, hxRelation⟩
  let xL : LCarrier.{u} := ⟨x.1, mem_L_of_mem x.2 U.2⟩
  have hxExtension :
      insert (ZFSet.pair arityL.1 xL.1) prefixGraph.1 ∈ relation.1 := by
    change
      insert (ZFSet.pair (natCode arity) x.1)
          (textbookTupleGraph params) ∈
        textbookEZF U.1 (natCode (arity + 1)) (natCode code)
    simpa only [textbookTupleGraph_snoc, textbookTupleSnocGraph] using
      hxRelation
  have hxCandidate :
      xL.1 ∈
        (textbookEWitnessCandidates
          U relation prefixGraph arityL).1 :=
    (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL xL).mpr
        ⟨x.2, hxExtension⟩
  rcases existsUnique_textbookEWitnessMinimum
      U relation prefixGraph arityL ⟨xL, hxCandidate⟩ with
    ⟨y, hyMinimum, _hyUnique⟩
  have hyData := (mem_textbookEWitnessCandidates_iff
    U relation prefixGraph arityL y).mp hyMinimum.1
  have hySelected :
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, canonicalWitnessOrder U,
          textbookEUniformRequestLCarrier code arity prefixGraph, y] := by
    apply
      (satisfies_textbookEUniformSelectedFormula_decoded_iff
        U seed (canonicalWitnessOrder U)
        prefixGraph y arity code).mpr
    refine ⟨hprefixSpace, hyData.1, hyData.2, ?_⟩
    intro z hzU hzExtension
    apply hyMinimum.2 z
    exact (mem_textbookEWitnessCandidates_iff
      U relation prefixGraph arityL z).mpr
        ⟨hzU, hzExtension⟩
  have hrequest :
      (textbookEUniformRequestLCarrier code arity prefixGraph).1 ∈
        (textbookEUniformWitnessRequestDomain seed).1 :=
    textbookEUniformRequestLCarrier_mem hprefixSpace
  have hyRange :
      y.1 ∈
        (textbookEUniformWitnessReplacementData seed U).range.1 := by
    apply
      (textbookEUniformWitnessReplacementData seed U).mem_range_iff y |>.mpr
    refine
      ⟨textbookEUniformRequestLCarrier code arity prefixGraph,
        hrequest, ?_⟩
    apply (satisfies_textbookEUniformTotalFormula
      U seed (canonicalWitnessOrder U)
      (textbookEUniformRequestLCarrier code arity prefixGraph) y).mpr
    exact Or.inl hySelected
  have hyStep :
      y.1 ∈ (textbookEUniformWitnessStep seed U).1 := by
    exact (mem_unionLCarrier_iff seed
      (textbookEUniformWitnessReplacementData seed U).range y).mpr
        (Or.inr hyRange)
  let yU : ZFCarrier U.1 := ⟨y.1, hyData.1⟩
  refine ⟨yU, hyStep, ?_⟩
  change textbookTupleGraph (snoc params yU) ∈ relation.1
  rw [textbookTupleGraph_snoc]
  exact hyData.2

/--
At a fixed point of the step, the relative one-step invariant becomes the
standard textbook closure predicate.
-/
theorem closesUnderTextbookEWitnessAt_of_uniformStep_subset
    (seed U : LCarrier.{u}) (arity code : Nat)
    (hfixed :
      (textbookEUniformWitnessStep seed U).1 ⊆ seed.1) :
    ClosesUnderTextbookEWitnessAt seed.1 U.1 arity code := by
  intro params hparams hexists
  rcases textbookEUniformWitnessStep_closesAt
      seed U arity code params hparams hexists with
    ⟨x, hxStep, hxRelation⟩
  exact ⟨x, hfixed hxStep, hxRelation⟩

end

end Constructible.Model
