/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.DefZFTextbookESection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteTupleInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFunctionRangeInjection
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalProductInjections
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalStageInjectionFamily
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessFormula

/-!
# An internal cardinal bound for `DefZF`

This file internalizes the textbook coding of a definable subset by

`<arity, <prefixGraph, formulaCode>>`.

The candidate triples form a genuine internal set.  Separation retains
exactly the triples that define a section, and Replacement constructs the
actual Kuratowski graph from valid triples to their sections.  The range is
proved extensionally equal to `DefZF a`; no external enumeration or external
cardinal comparison is used as the graph witness.
-/

@[expose] public section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The positive-arity reverse bridge -/

/--
At every nonzero arity, each relation in a finite textbook `D` stage is the
relation of an intrinsically scoped first-order formula.

The nonzero hypothesis is essential: the textbook convention makes
zero-arity existential projection empty, whereas ordinary sentence
satisfaction need not be false.
-/
theorem exists_formula_of_mem_textbookDStageZF_of_ne_zero
    (a : ZFSet.{u}) (k n : Nat) (hn : n ≠ 0)
    {relation : ZFSet.{u}}
    (hrelation : relation ∈ textbookDStageZF a k n) :
    ∃ formula : FOFormula n,
      ∀ assignment : Tuple (ZFCarrier a) n,
        textbookTupleGraph assignment ∈ relation ↔
          FOFormula.Satisfies (zfCarrierMem a) formula assignment := by
  induction k generalizing n relation with
  | zero =>
      rw [textbookDStageZF_zero] at hrelation
      rcases mem_textbookDZeroZF_iff.mp hrelation with
        ⟨i, j, hrelation⟩ | ⟨i, j, hrelation⟩
      · subst relation
        exact ⟨.mem i j, fun assignment =>
          textbookTupleGraph_mem_DInZF_iff assignment i j⟩
      · subst relation
        exact ⟨.eq i j, fun assignment =>
          textbookTupleGraph_mem_DEqZF_iff assignment i j⟩
  | succ k ih =>
      rcases mem_textbookDStageZF_succ_iff.mp hrelation with
        hprevious |
        ⟨previous, hprevious, hrelation⟩ |
        ⟨left, hleft, right, hright, hrelation⟩ |
        ⟨previous, hprevious, hrelation⟩
      · exact ih n hn hprevious
      · subst relation
        rcases ih n hn hprevious with ⟨formula, hformula⟩
        refine ⟨.neg formula, ?_⟩
        intro assignment
        simp only [ZFSet.mem_sdiff, textbookTupleGraph_mem_tupleSpace,
          true_and, FOFormula.Satisfies, hformula]
      · subst relation
        rcases ih n hn hleft with ⟨leftFormula, hleftFormula⟩
        rcases ih n hn hright with ⟨rightFormula, hrightFormula⟩
        refine ⟨.conj leftFormula rightFormula, ?_⟩
        intro assignment
        simp only [ZFSet.mem_inter, FOFormula.Satisfies,
          hleftFormula, hrightFormula]
      · subst relation
        rcases ih (n + 1) (Nat.succ_ne_zero n) hprevious with
          ⟨formula, hformula⟩
        refine ⟨.ex formula, ?_⟩
        intro assignment
        rw [textbookTupleGraph_mem_existsProjZF_iff hn]
        simp only [FOFormula.Satisfies]
        apply exists_congr
        intro value
        exact hformula (snoc assignment value)

/-- Every positive-arity textbook `E` value has ordinary formula semantics. -/
theorem exists_formula_for_textbookEZF_positive
    (a : ZFSet.{u}) (n code : Nat) :
    ∃ formula : FOFormula (n + 1),
      ∀ assignment : Tuple (ZFCarrier a) (n + 1),
        textbookTupleGraph assignment ∈
            textbookEZF a (natCode (n + 1)) (natCode code) ↔
          FOFormula.Satisfies (zfCarrierMem a) formula assignment := by
  have hrelation :=
    textbookEZF_mem_textbookDfZF a (n + 1) code
  rcases mem_textbookDfZF_iff.mp hrelation with ⟨k, hk⟩
  exact exists_formula_of_mem_textbookDStageZF_of_ne_zero
    a k (n + 1) (Nat.succ_ne_zero n) hk

/--
A genuine textbook `E` section, with a valid finite prefix graph, belongs to
the original formula-based `DefZF`.
-/
theorem textbookE_section_mem_DefZF
    {a subset prefixGraph : ZFSet.{u}} (n code : Nat)
    (hsubset : subset ⊆ a)
    (hprefix : prefixGraph ∈ textbookTupleSpace a n)
    (hsection : ∀ x : ZFSet.{u}, x ∈ a →
      (x ∈ subset ↔
        textbookTupleSnocGraph prefixGraph n x ∈
          textbookEZF a (natCode (n + 1)) (natCode code))) :
    subset ∈ DefZF a := by
  have hprefixFunction :
      ZFSet.IsFunc (natCode n) a prefixGraph :=
    mem_textbookTupleSpace_iff.mp hprefix
  rcases exists_textbookTupleGraph_eq_of_isFunc hprefixFunction with
    ⟨params, hparams⟩
  rcases exists_formula_for_textbookEZF_positive a n code with
    ⟨formula, hformula⟩
  apply mem_DefZF_iff_exists_satisfies.mpr
  refine ⟨hsubset, n, params, formula, ?_⟩
  intro x
  calc
    x.1 ∈ subset ↔
        textbookTupleSnocGraph prefixGraph n x.1 ∈
          textbookEZF a (natCode (n + 1)) (natCode code) :=
      hsection x.1 x.2
    _ ↔ textbookTupleGraph (snoc params x) ∈
          textbookEZF a (natCode (n + 1)) (natCode code) := by
      rw [textbookTupleGraph_snoc, hparams]
    _ ↔ FOFormula.Satisfies (zfCarrierMem a) formula
          (snoc params x) :=
      hformula (snoc params x)

namespace ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## One fixed formula for a coded section -/

/--
The body layout is

`[a, candidate, output, arity, inner, prefixGraph, code,
  positiveArity, relation, tupleSpace]`.
-/
def internalDefZFOutputBody : FOFormula 10 :=
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (1 : Fin 10) (3 : Fin 10) (4 : Fin 10)).toFO
  <| .conj
    (Delta0Formula.kuratowskiPairEqAt
      (4 : Fin 10) (5 : Fin 10) (6 : Fin 10)).toFO
  <| .conj
    (Delta0Formula.successorAt
      (7 : Fin 10) (3 : Fin 10)).toFO
  <| .conj
    (Model.textbookEZFFormulaAt
      (0 : Fin 10) (7 : Fin 10) (6 : Fin 10) (8 : Fin 10))
  <| .conj
    (Model.finiteTupleSpaceFormulaAt
      (0 : Fin 10) (3 : Fin 10) (9 : Fin 10))
  <| .conj
    (.mem (5 : Fin 10) (9 : Fin 10))
    (.all
      (FOFormula.biimp
        (.mem (Fin.last 10) (2 : Fin 10).castSucc)
        (.conj
          (.mem (Fin.last 10) (0 : Fin 10).castSucc)
          (Model.textbookETupleExtensionAt
            (8 : Fin 10).castSucc
            (5 : Fin 10).castSucc
            (3 : Fin 10).castSucc
            (Fin.last 10)))))

/--
Layout `[a,candidate,output]`.  The seven witnesses decode the candidate and
compute the corresponding textbook relation and finite tuple space.
-/
def internalDefZFOutputFormula : FOFormula 3 :=
  .ex <| .ex <| .ex <| .ex <| .ex <| .ex <| .ex
    internalDefZFOutputBody

private theorem internalDefZFBody_assignment
    (a candidate output arity inner prefixGraph code positiveArity
      relation tupleSpace : LCarrier.{u}) :
    snoc
      (snoc
        (snoc
          (snoc
            (snoc
              (snoc
                (snoc ![a, candidate, output] arity)
                inner)
              prefixGraph)
            code)
          positiveArity)
        relation)
      tupleSpace =
      ![a, candidate, output, arity, inner, prefixGraph, code,
        positiveArity, relation, tupleSpace] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

@[simp]
theorem satisfies_internalDefZFOutputFormula
    (a candidate output : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] ↔
      ∃ arity inner prefixGraph code positiveArity relation tupleSpace :
          LCarrier.{u},
        candidate.1 = ZFSet.pair arity.1 inner.1 ∧
        inner.1 = ZFSet.pair prefixGraph.1 code.1 ∧
        positiveArity.1 = insert arity.1 arity.1 ∧
        (((positiveArity.1 ∈ textbookEOmegaZF ∧
              code.1 ∈ textbookEOmegaZF) ∧
            relation.1 =
              textbookEZF a.1 positiveArity.1 code.1)) ∧
        FOFormula.Satisfies LMem
          finiteTupleSpaceFormula ![a, arity, tupleSpace] ∧
        prefixGraph.1 ∈ tupleSpace.1 ∧
        ∀ x : LCarrier.{u},
          (x.1 ∈ output.1 ↔
            x.1 ∈ a.1 ∧
              insert (ZFSet.pair arity.1 x.1) prefixGraph.1 ∈
                relation.1) := by
  simp only [internalDefZFOutputFormula, FOFormula.Satisfies]
  apply exists_congr
  intro arity
  apply exists_congr
  intro inner
  apply exists_congr
  intro prefixGraph
  apply exists_congr
  intro code
  apply exists_congr
  intro positiveArity
  apply exists_congr
  intro relation
  apply exists_congr
  intro tupleSpace
  rw [internalDefZFBody_assignment]
  simp only [internalDefZFOutputBody, FOFormula.Satisfies,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_successorAt_lCarrier,
    Model.satisfies_textbookEZFFormulaAt_lCarrier,
    Model.satisfies_finiteTupleSpaceFormulaAt_lCarrier,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    Model.satisfies_textbookETupleExtensionAt,
    snoc_last, snoc_castSucc]
  change
    (candidate.1 = ZFSet.pair arity.1 inner.1 ∧
      inner.1 = ZFSet.pair prefixGraph.1 code.1 ∧
      positiveArity.1 = insert arity.1 arity.1 ∧
      (((positiveArity.1 ∈ textbookEOmegaZF ∧
            code.1 ∈ textbookEOmegaZF) ∧
          relation.1 =
            textbookEZF a.1 positiveArity.1 code.1)) ∧
      FOFormula.Satisfies LMem
        finiteTupleSpaceFormula ![a, arity, tupleSpace] ∧
      prefixGraph.1 ∈ tupleSpace.1 ∧
      ∀ x : LCarrier.{u},
        (x.1 ∈ output.1 ↔
          x.1 ∈ a.1 ∧
            insert (ZFSet.pair arity.1 x.1) prefixGraph.1 ∈
              relation.1)) ↔ _
  rfl

/-! ## The separated domain of valid codes -/

/-- Layout `[a,candidate]`: the candidate has a represented section output. -/
def internalDefZFHasOutputFormula : FOFormula 2 :=
  .ex internalDefZFOutputFormula

private theorem internalDefZFOutput_assignment
    (a candidate output : LCarrier.{u}) :
    snoc ![a, candidate] output = ![a, candidate, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_internalDefZFHasOutputFormula
    (a candidate : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalDefZFHasOutputFormula
        ![a, candidate] ↔
      ∃ output : LCarrier.{u},
        FOFormula.Satisfies LMem internalDefZFOutputFormula
          ![a, candidate, output] := by
  simp only [internalDefZFHasOutputFormula, FOFormula.Satisfies]
  apply exists_congr
  intro output
  rw [internalDefZFOutput_assignment]

/-- The ambient internal set containing every possible coded triple. -/
def internalDefZFCandidateContainer (a : LCarrier.{u}) :
    LCarrier.{u} :=
  prodLCarrier (omegaLCarrier : LCarrier.{u})
    (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)

/--
Separation retains exactly the triples in the candidate container that have
an output according to the fixed section formula.
-/
noncomputable def internalDefZFCandidateDomain (a : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    internalDefZFHasOutputFormula ![a]
    (internalDefZFCandidateContainer a))

private theorem internalDefZFCandidate_assignment
    (a candidate : LCarrier.{u}) :
    snoc ![a] candidate = ![a, candidate] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem mem_internalDefZFCandidateDomain_iff
    (a candidate : LCarrier.{u}) :
    candidate.1 ∈ (internalDefZFCandidateDomain a).1 ↔
      candidate.1 ∈ (internalDefZFCandidateContainer a).1 ∧
        ∃ output : LCarrier.{u},
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output] := by
  rw [internalDefZFCandidateDomain]
  rw [Classical.choose_spec (exists_separationLCarrier
    internalDefZFHasOutputFormula ![a]
    (internalDefZFCandidateContainer a)) candidate]
  rw [internalDefZFCandidate_assignment,
    satisfies_internalDefZFHasOutputFormula]

/-! ## Functionality of the coded-section relation -/

theorem internalDefZFOutputFormula_unique
    (a candidate first second : LCarrier.{u})
    (hfirst : FOFormula.Satisfies LMem internalDefZFOutputFormula
      ![a, candidate, first])
    (hsecond : FOFormula.Satisfies LMem internalDefZFOutputFormula
      ![a, candidate, second]) :
    first = second := by
  rcases (satisfies_internalDefZFOutputFormula
    a candidate first).mp hfirst with
    ⟨firstArity, firstInner, firstPrefix, firstCode,
      firstPositiveArity, firstRelation, firstTupleSpace,
      hfirstCandidate, hfirstInner, hfirstSuccessor,
      hfirstRelation, _hfirstSpace, _hfirstPrefix, hfirstMembers⟩
  rcases (satisfies_internalDefZFOutputFormula
    a candidate second).mp hsecond with
    ⟨secondArity, secondInner, secondPrefix, secondCode,
      secondPositiveArity, secondRelation, secondTupleSpace,
      hsecondCandidate, hsecondInner, hsecondSuccessor,
      hsecondRelation, _hsecondSpace, _hsecondPrefix, hsecondMembers⟩
  have houter := ZFSet.pair_inj.mp
    (hfirstCandidate.symm.trans hsecondCandidate)
  have harity : secondArity = firstArity :=
    Subtype.ext houter.1.symm
  have hinner : secondInner = firstInner :=
    Subtype.ext houter.2.symm
  subst secondArity
  subst secondInner
  have hinnerCoordinates := ZFSet.pair_inj.mp
    (hfirstInner.symm.trans hsecondInner)
  have hprefix : secondPrefix = firstPrefix :=
    Subtype.ext hinnerCoordinates.1.symm
  have hcode : secondCode = firstCode :=
    Subtype.ext hinnerCoordinates.2.symm
  subst secondPrefix
  subst secondCode
  have hpositive : secondPositiveArity = firstPositiveArity :=
    Subtype.ext (hsecondSuccessor.trans hfirstSuccessor.symm)
  subst secondPositiveArity
  have hrelation : secondRelation = firstRelation := by
    apply Subtype.ext
    exact hsecondRelation.2.trans hfirstRelation.2.symm
  subst secondRelation
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx first.2⟩
    exact (hsecondMembers xL).mpr ((hfirstMembers xL).mp hx)
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx second.2⟩
    exact (hfirstMembers xL).mpr ((hsecondMembers xL).mp hx)

theorem internalDefZFOutputFormula_existsUnique
    (a candidate : LCarrier.{u})
    (hcandidate :
      candidate.1 ∈ (internalDefZFCandidateDomain a).1) :
    ∃! output : LCarrier.{u},
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] := by
  rcases (mem_internalDefZFCandidateDomain_iff
    a candidate).mp hcandidate with
    ⟨_hcandidateContainer, output, houtput⟩
  refine ⟨output, houtput, ?_⟩
  intro other hother
  exact internalDefZFOutputFormula_unique
    a candidate other output hother houtput

/-! ## Soundness of every represented output -/

theorem mem_DefZF_of_satisfies_internalDefZFOutputFormula
    (a candidate output : LCarrier.{u})
    (hcandidateContainer :
      candidate.1 ∈ (internalDefZFCandidateContainer a).1)
    (hformula :
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output]) :
    output.1 ∈ DefZF a.1 := by
  rcases (satisfies_internalDefZFOutputFormula
    a candidate output).mp hformula with
    ⟨arity, inner, prefixGraph, code, positiveArity, relation,
      tupleSpace, hcandidate, hinner, hsuccessor, hrelation,
      hspace, hprefix, hmembers⟩
  have hcontainer := hcandidateContainer
  change candidate.1 ∈
      ZFSet.prod (omegaLCarrier : LCarrier.{u}).1
        (ZFSet.prod (internalFiniteTupleSpaces a).1
          (omegaLCarrier : LCarrier.{u}).1) at hcontainer
  rw [hcandidate, ZFSet.pair_mem_prod] at hcontainer
  have harityOmega : arity.1 ∈
      (omegaLCarrier : LCarrier.{u}).1 :=
    hcontainer.1
  have hinnerContainer := hcontainer.2
  rw [hinner, ZFSet.pair_mem_prod] at hinnerContainer
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      arity.1).mp harityOmega with
    ⟨n, harityValue⟩
  have harityEq :
      arity = TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst arity
  have hpositiveEq :
      positiveArity =
        TextbookNatFormula.textbookNatCodeLCarrier (n + 1) := by
    apply Subtype.ext
    exact hsuccessor.trans (natCode_succ_eq_insert n).symm
  subst positiveArity
  have hcodeOmega :
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    exact hrelation.1.2
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      code.1).mp hcodeOmega with
    ⟨m, hcodeValue⟩
  have hcodeEq :
      code = TextbookNatFormula.textbookNatCodeLCarrier m := by
    apply Subtype.ext
    exact hcodeValue
  subst code
  have hrelationValue :
      relation.1 =
        textbookEZF a.1 (natCode (n + 1)) (natCode m) := by
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
      hrelation.2
  have hspaceValue :
      tupleSpace.1 = textbookTupleSpace a.1 n :=
    (satisfies_finiteTupleSpaceFormula_natCode_iff
      a tupleSpace n).mp hspace
  have hprefixValue :
      prefixGraph.1 ∈ textbookTupleSpace a.1 n := by
    rwa [hspaceValue] at hprefix
  have houtputSubset : output.1 ⊆ a.1 := by
    intro x hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx output.2⟩
    exact (hmembers xL).mp hx |>.1
  apply textbookE_section_mem_DefZF n m houtputSubset hprefixValue
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx a.2⟩
  calc
    x ∈ output.1 ↔
        x ∈ a.1 ∧
          insert (ZFSet.pair (natCode n) x) prefixGraph.1 ∈
            relation.1 := by
      simpa only [xL,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hmembers xL
    _ ↔ insert (ZFSet.pair (natCode n) x) prefixGraph.1 ∈
          relation.1 :=
      and_iff_right hx
    _ ↔ textbookTupleSnocGraph prefixGraph.1 n x ∈
          textbookEZF a.1 (natCode (n + 1)) (natCode m) := by
      rw [textbookTupleSnocGraph, hrelationValue]

/-! ## Completeness of the coded candidates -/

theorem exists_internalDefZFCandidate_of_mem_DefZF
    (a : LCarrier.{u}) {z : ZFSet.{u}}
    (hz : z ∈ DefZF a.1) :
    ∃ candidate output : LCarrier.{u},
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] ∧
      output.1 = z := by
  rcases exists_textbookE_section_of_mem_DefZF hz with
    ⟨n, m, prefixRaw, hprefixRaw, hsection⟩
  let arity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let code : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier m
  let positiveArity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier (n + 1)
  let prefixGraph : LCarrier.{u} :=
    ⟨prefixRaw,
      mem_L_of_mem hprefixRaw (textbookTupleSpace_mem_L a.2 n)⟩
  let inner : LCarrier.{u} :=
    orderedPairLCarrier prefixGraph code
  let candidate : LCarrier.{u} :=
    orderedPairLCarrier arity inner
  let relation : LCarrier.{u} :=
    textbookEZFLCarrier a (n + 1) m
  let tupleSpace : LCarrier.{u} :=
    finiteTupleSpaceLCarrier a n
  let output : LCarrier.{u} :=
    textbookEWitnessCandidates a relation prefixGraph arity
  have harityOmega :
      arity.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩
  have hpositiveOmega :
      positiveArity.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode (n + 1) : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode (n + 1))).mpr ⟨n + 1, rfl⟩
  have hcodeOmega :
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode m)).mpr ⟨m, rfl⟩
  have hprefixFinite :
      prefixGraph.1 ∈ (internalFiniteTupleSpaces a).1 := by
    apply (mem_internalFiniteTupleSpaces_iff a prefixGraph).mpr
    refine ⟨n, ?_⟩
    simpa only [prefixGraph, finiteTupleSpaceLCarrier_val] using
      hprefixRaw
  have hcandidateContainer :
      candidate.1 ∈ (internalDefZFCandidateContainer a).1 := by
    change ZFSet.pair arity.1 inner.1 ∈
      ZFSet.prod (omegaLCarrier : LCarrier.{u}).1
        (ZFSet.prod (internalFiniteTupleSpaces a).1
          (omegaLCarrier : LCarrier.{u}).1)
    rw [ZFSet.pair_mem_prod]
    refine ⟨harityOmega, ?_⟩
    change ZFSet.pair prefixGraph.1 code.1 ∈
      ZFSet.prod (internalFiniteTupleSpaces a).1
        (omegaLCarrier : LCarrier.{u}).1
    rw [ZFSet.pair_mem_prod]
    exact ⟨hprefixFinite, hcodeOmega⟩
  have hformula :
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] := by
    apply (satisfies_internalDefZFOutputFormula
      a candidate output).mpr
    refine ⟨arity, inner, prefixGraph, code, positiveArity,
      relation, tupleSpace, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact natCode_succ_eq_insert n
    · exact ⟨⟨hpositiveOmega, hcodeOmega⟩, rfl⟩
    · exact (satisfies_finiteTupleSpaceFormula_natCode_iff
        a tupleSpace n).mpr rfl
    · exact hprefixRaw
    · intro x
      exact mem_textbookEWitnessCandidates_iff
        a relation prefixGraph arity x
  have hcandidate :
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 :=
    (mem_internalDefZFCandidateDomain_iff a candidate).mpr
      ⟨hcandidateContainer, output, hformula⟩
  refine ⟨candidate, output, hcandidate, hformula, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx output.2⟩
    have hxData := (mem_textbookEWitnessCandidates_iff
      a relation prefixGraph arity xL).mp hx
    apply (hsection x hxData.1).mpr
    simpa only [relation, textbookEZFLCarrier_val, prefixGraph,
      arity, TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookTupleSnocGraph] using hxData.2
  · intro hx
    have hza : z ⊆ a.1 := (mem_DefZF_iff.mp hz).1
    have hxa : x ∈ a.1 := hza hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hxa a.2⟩
    apply (mem_textbookEWitnessCandidates_iff
      a relation prefixGraph arity xL).mpr
    refine ⟨hxa, ?_⟩
    have hxSection := (hsection x hxa).mp hx
    simpa only [relation, textbookEZFLCarrier_val, prefixGraph,
      arity, TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookTupleSnocGraph] using hxSection

/-! ## Replacement and the genuine internal `DefZF` set -/

/--
The represented data produced by Replacement.  Its range is not merely a
surrogate: `range_eq_DefZF` identifies its underlying set with the original
`DefZF a`.
-/
structure InternalDefZFData (a : LCarrier.{u}) where
  graph : LCarrier.{u}
  range : LCarrier.{u}
  isFunctionGraph :
    IsFunctionGraph LMem graph (internalDefZFCandidateDomain a) range
  mem_range_iff : ∀ output : LCarrier.{u},
    output.1 ∈ range.1 ↔
      ∃ candidate : LCarrier.{u},
        candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output]
  graphValue_iff : ∀ candidate output : LCarrier.{u},
    GraphValue LMem graph candidate output ↔
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
        FOFormula.Satisfies LMem internalDefZFOutputFormula
          ![a, candidate, output]
  range_eq_DefZF : range.1 = DefZF a.1

private theorem internalDefZFReplacement_assignment
    (a candidate output : LCarrier.{u}) :
    snoc (snoc ![a] candidate) output =
      ![a, candidate, output] := by
  funext i
  fin_cases i <;> rfl

/--
Replacement simultaneously constructs the actual function graph and the
actual set representing `DefZF a`.
-/
theorem exists_internalDefZFData (a : LCarrier.{u}) :
    Nonempty (InternalDefZFData a) := by
  let params : Tuple LCarrier.{u} 1 := ![a]
  let domain : LCarrier.{u} := internalDefZFCandidateDomain a
  have hfun : ∀ candidate : LCarrier.{u},
      candidate.1 ∈ domain.1 →
        ∃! output : LCarrier.{u},
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            (snoc (snoc params candidate) output) := by
    intro candidate hcandidate
    simpa only [params, domain,
      internalDefZFReplacement_assignment] using
        internalDefZFOutputFormula_existsUnique
          a candidate hcandidate
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      internalDefZFOutputFormula params domain hfun with
    ⟨graph, range, hfunction, hrange, hvalue⟩
  have hrangeVector : ∀ output : LCarrier.{u},
      output.1 ∈ range.1 ↔
        ∃ candidate : LCarrier.{u},
          candidate.1 ∈ domain.1 ∧
            FOFormula.Satisfies LMem internalDefZFOutputFormula
              ![a, candidate, output] := by
    intro output
    simpa only [params,
      internalDefZFReplacement_assignment] using hrange output
  have hvalueVector : ∀ candidate output : LCarrier.{u},
      GraphValue LMem graph candidate output ↔
        candidate.1 ∈ domain.1 ∧
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output] := by
    intro candidate output
    simpa only [params,
      internalDefZFReplacement_assignment] using
        hvalue candidate output
  have hrangeEq : range.1 = DefZF a.1 := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz range.2⟩
      rcases (hrangeVector zL).mp hz with
        ⟨candidate, hcandidate, hformula⟩
      have hcandidateContainer :=
        (mem_internalDefZFCandidateDomain_iff
          a candidate).mp hcandidate |>.1
      exact mem_DefZF_of_satisfies_internalDefZFOutputFormula
        a candidate zL hcandidateContainer hformula
    · intro hz
      rcases exists_internalDefZFCandidate_of_mem_DefZF
          a hz with
        ⟨candidate, output, hcandidate, hformula, houtput⟩
      rw [← houtput]
      exact (hrangeVector output).mpr
        ⟨candidate, hcandidate, hformula⟩
  refine ⟨{
    graph := graph
    range := range
    isFunctionGraph := by simpa only [domain] using hfunction
    mem_range_iff := by
      intro output
      simpa only [domain] using hrangeVector output
    graphValue_iff := by
      intro candidate output
      simpa only [domain] using hvalueVector candidate output
    range_eq_DefZF := hrangeEq
  }⟩

/-- A canonical internally represented copy of the original `DefZF a`. -/
noncomputable def internalDefZFData (a : LCarrier.{u}) :
    InternalDefZFData a :=
  Classical.choice (exists_internalDefZFData a)

/--
The genuine `LCarrier` whose underlying `ZFSet` is exactly `DefZF a`.
Its membership proof is obtained from Separation and Replacement above.
-/
noncomputable def DefZFLCarrier (a : LCarrier.{u}) :
    LCarrier.{u} :=
  (internalDefZFData a).range

@[simp]
theorem DefZFLCarrier_val (a : LCarrier.{u}) :
    (DefZFLCarrier a).1 = DefZF a.1 :=
  (internalDefZFData a).range_eq_DefZF

/-! ## The internal cardinal injection -/

/-- The separated valid-code domain injects into its full candidate set. -/
theorem injects_internalDefZFCandidateDomain_container_lCarrier
    (a : LCarrier.{u}) :
    Injects LMem (internalDefZFCandidateDomain a)
      (internalDefZFCandidateContainer a) := by
  apply injects_of_subset_lCarrier
  intro candidate hcandidate
  exact (mem_internalDefZFCandidateDomain_iff
    a candidate).mp hcandidate |>.1

/--
The textbook one-step cardinal bound, represented entirely by internal
Kuratowski graphs:

* `a` injects into `kappa`;
* the internal omega is a subset of `kappa`;
* `kappa x kappa` injects into `kappa`;
* therefore the genuine internally represented `DefZF a` injects into
  `kappa`.
-/
theorem injects_DefZFLCarrier_lCarrier
    {a kappa : LCarrier.{u}}
    (ha : Injects LMem a kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (hsquare : Injects LMem
      (prodLCarrier kappa kappa) kappa) :
    Injects LMem (DefZFLCarrier a) kappa := by
  rcases ha with ⟨aInjection, haInjection⟩
  rcases hsquare with ⟨squareInjection, hsquareInjection⟩
  have hsquare' : Injects LMem
      (prodLCarrier kappa kappa) kappa :=
    ⟨squareInjection, hsquareInjection⟩
  have homegaInjection :
      Injects LMem (omegaLCarrier : LCarrier.{u}) kappa :=
    injects_of_subset_lCarrier homega
  have hfiniteTuples :
      Injects LMem (internalFiniteTupleSpaces a) kappa :=
    injects_internalFiniteTupleSpaces_of_square_lCarrier
      homega haInjection hsquareInjection
  have hprefixCodeProduct :
      Injects LMem
        (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)
        (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier
      hfiniteTuples homegaInjection
  have hprefixCode :
      Injects LMem
        (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)
        kappa :=
    hprefixCodeProduct.trans_lCarrier hsquare'
  have hcandidateProduct :
      Injects LMem
        (prodLCarrier omegaLCarrier
          (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier))
        (prodLCarrier kappa kappa) :=
    injects_prod_of_injects_lCarrier
      homegaInjection hprefixCode
  have hcontainer :
      Injects LMem (internalDefZFCandidateContainer a) kappa := by
    apply Injects.trans_lCarrier
      (middle := prodLCarrier kappa kappa)
    · simpa only [internalDefZFCandidateContainer] using
        hcandidateProduct
    · exact hsquare'
  have hdomain :
      Injects LMem (internalDefZFCandidateDomain a) kappa :=
    (injects_internalDefZFCandidateDomain_container_lCarrier a).trans_lCarrier
      hcontainer
  let data : InternalDefZFData a := internalDefZFData a
  have hcovered : ∀ output : LCarrier.{u},
      output.1 ∈ data.range.1 →
        ∃ candidate : LCarrier.{u},
          candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
            GraphValue LMem data.graph candidate output := by
    intro output houtput
    rcases (data.mem_range_iff output).mp houtput with
      ⟨candidate, hcandidate, hformula⟩
    exact ⟨candidate, hcandidate,
      (data.graphValue_iff candidate output).mpr
        ⟨hcandidate, hformula⟩⟩
  have hrangeDomain :
      Injects LMem data.range (internalDefZFCandidateDomain a) :=
    Model.injects_range_into_domain_of_functionGraph
      data.graph (internalDefZFCandidateDomain a) data.range
      data.isFunctionGraph hcovered
  have hrangeKappa : Injects LMem data.range kappa :=
    hrangeDomain.trans_lCarrier hdomain
  simpa only [DefZFLCarrier, data] using hrangeKappa

/-- Raw-set restatement: `DefZF a` itself is constructible whenever `a` is. -/
theorem DefZF_mem_L_of_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) :
    DefZF a ∈ L := by
  let aL : LCarrier.{u} := ⟨a, ha⟩
  rw [← DefZFLCarrier_val aL]
  exact (DefZFLCarrier aL).2

end ContinuumFormula

end

end Constructible
