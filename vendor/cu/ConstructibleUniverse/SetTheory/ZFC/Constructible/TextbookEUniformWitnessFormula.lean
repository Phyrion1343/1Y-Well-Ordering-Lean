/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteTupleSpaces
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEInternalTasks
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookESingleWitnessStep

/-!
# A uniform first-order selector for all textbook E witness requests

A request is the Kuratowski pair

`<<code, arity + 1>, prefixGraph>`.

The selected formula decodes this pair internally, verifies that `prefixGraph`
belongs to `seed^arity`, computes the corresponding textbook relation
`E(U, arity + 1, code)`, and selects the canonical least witness in its
fiber.  The total formula returns that witness when it exists and the empty
set otherwise.  Both are fixed first-order formulas; no external decoder or
choice function occurs in their definitions.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Coordinate embeddings -/

/-- Put the four-place textbook E formula at arbitrary coordinates. -/
def textbookEZFFormulaAt {n : Nat}
    (ambient positiveArity code relation : Fin n) : FOFormula n :=
  FOFormula.rename ![ambient, positiveArity, code, relation]
    TextbookEFormula.textbookEZFFormula

@[simp]
theorem satisfies_textbookEZFFormulaAt_lCarrier {n : Nat}
    (ambient positiveArity code relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (textbookEZFFormulaAt ambient positiveArity code relation) s <->
      ((s positiveArity).1 ∈ textbookEOmegaZF /\
        (s code).1 ∈ textbookEOmegaZF) /\
        (s relation).1 =
          textbookEZF (s ambient).1 (s positiveArity).1 (s code).1 := by
  rw [textbookEZFFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![ambient, positiveArity, code, relation] i)) =
        ![s ambient, s positiveArity, s code, s relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_textbookEZFFormula_lCarrier_iff]

/-- Put the finite tuple-space formula at arbitrary coordinates. -/
def finiteTupleSpaceFormulaAt {n : Nat}
    (seed arity space : Fin n) : FOFormula n :=
  FOFormula.rename ![seed, arity, space]
    ContinuumFormula.finiteTupleSpaceFormula

theorem satisfies_finiteTupleSpaceFormulaAt_lCarrier {n : Nat}
    (seed arity space : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (finiteTupleSpaceFormulaAt seed arity space) s <->
      FOFormula.Satisfies LMem
        ContinuumFormula.finiteTupleSpaceFormula
        ![s seed, s arity, s space] := by
  rw [finiteTupleSpaceFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![seed, arity, space] i)) =
        ![s seed, s arity, s space] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

/-! ## The selected-witness formula -/

/--
The quantifier-free core of the uniform selector.

The layout is

`[U, seed, order, request, output, task, prefixGraph, code,
  positiveArity, arity, relation, space]`.
-/
def textbookEUniformSelectedBody : FOFormula 12 :=
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (3 : Fin 12) (5 : Fin 12) (6 : Fin 12)).toFO
    <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (5 : Fin 12) (7 : Fin 12) (8 : Fin 12)).toFO
    <| .conj
      (Delta0Formula.successorAt
        (8 : Fin 12) (9 : Fin 12)).toFO
    <| .conj
      (textbookEZFFormulaAt
        (0 : Fin 12) (8 : Fin 12) (7 : Fin 12) (10 : Fin 12))
    <| .conj
      (finiteTupleSpaceFormulaAt
        (1 : Fin 12) (9 : Fin 12) (11 : Fin 12))
    <| .conj
      (.mem (6 : Fin 12) (11 : Fin 12))
    <| .conj
      (.mem (4 : Fin 12) (0 : Fin 12))
    <| .conj
      (textbookETupleExtensionAt
        (10 : Fin 12) (6 : Fin 12)
        (9 : Fin 12) (4 : Fin 12))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (Fin.last 12) (0 : Fin 12).castSucc)
            (textbookETupleExtensionAt
              (10 : Fin 12).castSucc
              (6 : Fin 12).castSucc
              (9 : Fin 12).castSucc
              (Fin.last 12)))
          (.neg
            (graphRelAt
              (2 : Fin 12).castSucc
              (Fin.last 12)
              (4 : Fin 12).castSucc))))

/--
Layout `[U, seed, order, request, output]`.  The seven existentially bound
coordinates are respectively `task`, `prefixGraph`, `code`, positive arity,
predecessor arity, the E relation, and `seed^arity`.
-/
def textbookEUniformSelectedFormula : FOFormula 5 :=
  .ex <| .ex <| .ex <| .ex <| .ex <| .ex <| .ex
    textbookEUniformSelectedBody

@[simp]
theorem satisfies_textbookEUniformSelectedFormula
    (U seed order request output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, order, request, output] <->
      ∃ task prefixGraph code positiveArity arity relation space : LCarrier.{u},
        request.1 = ZFSet.pair task.1 prefixGraph.1 /\
        task.1 = ZFSet.pair code.1 positiveArity.1 /\
        positiveArity.1 = insert arity.1 arity.1 /\
        ((positiveArity.1 ∈ textbookEOmegaZF /\
            code.1 ∈ textbookEOmegaZF) /\
          relation.1 =
            textbookEZF U.1 positiveArity.1 code.1) /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![seed, arity, space] /\
        prefixGraph.1 ∈ space.1 /\
        output.1 ∈ U.1 /\
        insert (ZFSet.pair arity.1 output.1) prefixGraph.1 ∈ relation.1 /\
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 ->
          insert (ZFSet.pair arity.1 z.1) prefixGraph.1 ∈ relation.1 ->
            ¬ GraphRel order z output := by
  simp only [textbookEUniformSelectedFormula, FOFormula.Satisfies]
  apply exists_congr
  intro task
  apply exists_congr
  intro prefixGraph
  apply exists_congr
  intro code
  apply exists_congr
  intro positiveArity
  apply exists_congr
  intro arity
  apply exists_congr
  intro relation
  apply exists_congr
  intro space
  simp only [textbookEUniformSelectedBody, FOFormula.Satisfies,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_successorAt_lCarrier,
    satisfies_textbookEZFFormulaAt_lCarrier,
    satisfies_finiteTupleSpaceFormulaAt_lCarrier,
    satisfies_textbookETupleExtensionAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt, snoc_last, snoc_castSucc]
  aesop

/-! ## Exact semantics at a decoded request -/

private theorem decoded_request_pair_injective
    {request task prefixGraph code positiveArity : LCarrier.{u}}
    {arityCode codeCode : ZFSet.{u}}
    (hrequest :
      request.1 = ZFSet.pair
        (ZFSet.pair codeCode arityCode) prefixGraph.1)
    (hrequest' : request.1 = ZFSet.pair task.1 prefixGraph.1)
    (htask : task.1 = ZFSet.pair code.1 positiveArity.1) :
    code.1 = codeCode /\ positiveArity.1 = arityCode := by
  have houter := ZFSet.pair_inj.mp (hrequest'.symm.trans hrequest)
  have hinner : ZFSet.pair code.1 positiveArity.1 =
      ZFSet.pair codeCode arityCode := by
    exact htask.symm.trans houter.1
  exact ZFSet.pair_inj.mp hinner

/--
At a decoded request, the selected formula is exactly the canonical
least-witness condition for the intended E fiber.
-/
theorem satisfies_textbookEUniformSelectedFormula_decoded_iff
    (U seed order prefixGraph output : LCarrier.{u}) (arity code : Nat) :
    FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, order,
          orderedPairLCarrier
            (orderedPairLCarrier
              (TextbookNatFormula.textbookNatCodeLCarrier code)
              (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)))
            prefixGraph,
          output] <->
      prefixGraph.1 ∈ textbookTupleSpace seed.1 arity /\
      output.1 ∈ U.1 /\
      insert (ZFSet.pair (natCode arity) output.1) prefixGraph.1 ∈
        textbookEZF U.1 (natCode (arity + 1)) (natCode code) /\
      ∀ z : LCarrier.{u}, z.1 ∈ U.1 ->
        insert (ZFSet.pair (natCode arity) z.1) prefixGraph.1 ∈
          textbookEZF U.1 (natCode (arity + 1)) (natCode code) ->
            ¬ GraphRel order z output := by
  rw [satisfies_textbookEUniformSelectedFormula]
  constructor
  · rintro ⟨task, prefixGraph', code', positiveArity, arity', relation, space,
      hrequest, htask, hsuccessor, hrelation, hspace, hprefix,
      houtput, hextension, hminimal⟩
    have hrequestRaw :
        (orderedPairLCarrier
          (orderedPairLCarrier
            (TextbookNatFormula.textbookNatCodeLCarrier code)
            (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)))
          prefixGraph).1 =
          ZFSet.pair
            (ZFSet.pair (natCode code) (natCode (arity + 1)))
            prefixGraph.1 := by
      rfl
    have houter := ZFSet.pair_inj.mp (hrequest.symm.trans hrequestRaw)
    have hprefixEq : prefixGraph' = prefixGraph := by
      exact Subtype.ext houter.2
    subst prefixGraph'
    have hinner :
        ZFSet.pair code'.1 positiveArity.1 =
          ZFSet.pair (natCode code) (natCode (arity + 1)) := by
      exact htask.symm.trans houter.1
    have hcoordinates := ZFSet.pair_inj.mp hinner
    have hcodeEq :
        code' = TextbookNatFormula.textbookNatCodeLCarrier code := by
      exact Subtype.ext hcoordinates.1
    have hpositiveEq :
        positiveArity =
          TextbookNatFormula.textbookNatCodeLCarrier (arity + 1) := by
      exact Subtype.ext hcoordinates.2
    subst code'
    subst positiveArity
    have harityRaw : arity'.1 = natCode arity := by
      apply insert_self_injective
      calc
        insert arity'.1 arity'.1 =
            (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)).1 :=
          hsuccessor.symm
        _ = natCode (arity + 1) := rfl
        _ = insert (natCode arity) (natCode arity) :=
          natCode_succ_eq_insert arity
    have harityEq :
        arity' =
          TextbookNatFormula.textbookNatCodeLCarrier arity := by
      exact Subtype.ext harityRaw
    subst arity'
    have hrelationRaw :
        relation.1 =
          textbookEZF U.1 (natCode (arity + 1)) (natCode code) := by
      simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
        hrelation.2
    have hspaceRaw :
        space.1 = textbookTupleSpace seed.1 arity := by
      exact (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
        seed space arity).mp hspace
    rw [hspaceRaw] at hprefix
    rw [hrelationRaw] at hextension
    rw [hrelationRaw] at hminimal
    refine ⟨hprefix, houtput, hextension, ?_⟩
    intro z hzU hzRelation
    apply hminimal z hzU
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
      hzRelation
  · rintro ⟨hprefix, houtput, hextension, hminimal⟩
    let codeL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier code
    let positiveArityL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)
    let arityL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier arity
    let task : LCarrier.{u} := orderedPairLCarrier codeL positiveArityL
    let request : LCarrier.{u} := orderedPairLCarrier task prefixGraph
    let relation : LCarrier.{u} := textbookEZFLCarrier U (arity + 1) code
    let space : LCarrier.{u} :=
      ContinuumFormula.finiteTupleSpaceLCarrier seed arity
    refine ⟨task, prefixGraph, codeL, positiveArityL, arityL, relation, space,
      ?_, ?_, ?_, ?_, ?_, ?_, houtput, ?_, ?_⟩
    · rfl
    · rfl
    · exact natCode_succ_eq_insert arity
    · constructor
      · constructor
        · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode (arity + 1))).mpr ⟨arity + 1, rfl⟩
        · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode code)).mpr ⟨code, rfl⟩
      · rfl
    · exact
        (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
          seed space arity).mpr rfl
    · exact hprefix
    · exact hextension
    · intro z hzU hzRelation
      exact hminimal z hzU hzRelation

/-! ## The total output formula -/

/--
Layout `[U, seed, order, request, output]`.  Return the selected witness if
one exists; otherwise return the empty set.
-/
def textbookEUniformTotalFormula : FOFormula 5 :=
  .disj textbookEUniformSelectedFormula
    (.conj
      (Delta0Formula.emptyDeltaAt (4 : Fin 5)).toFO
      (.neg (.ex
        (FOFormula.rename
          ![(0 : Fin 5).castSucc, (1 : Fin 5).castSucc,
            (2 : Fin 5).castSucc, (3 : Fin 5).castSucc, Fin.last 5]
          textbookEUniformSelectedFormula))))

private theorem total_selected_assignment
    (U seed order request output y : LCarrier.{u}) :
    (fun i =>
      (snoc ![U, seed, order, request, output] y)
        (![((0 : Fin 5).castSucc), ((1 : Fin 5).castSucc),
          ((2 : Fin 5).castSucc), ((3 : Fin 5).castSucc),
          (Fin.last 5)] i)) =
      ![U, seed, order, request, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_textbookEUniformTotalFormula
    (U seed order request output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, order, request, output] <->
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
          ![U, seed, order, request, output] \/
        (output = emptyLCarrier /\
          ¬ ∃ y : LCarrier.{u},
            FOFormula.Satisfies LMem textbookEUniformSelectedFormula
              ![U, seed, order, request, y]) := by
  simp only [textbookEUniformTotalFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_emptyDeltaAt_lCarrier,
    FOFormula.satisfies_rename]
  simp only [total_selected_assignment]
  constructor
  · rintro (hselected | ⟨hempty, hnone⟩)
    · exact Or.inl hselected
    · right
      refine ⟨Subtype.ext hempty, ?_⟩
      intro h
      exact hnone h
  · rintro (hselected | ⟨hempty, hnone⟩)
    · exact Or.inl hselected
    · right
      constructor
      · exact congrArg Subtype.val hempty
      · exact hnone

end

end Constructible.Model
