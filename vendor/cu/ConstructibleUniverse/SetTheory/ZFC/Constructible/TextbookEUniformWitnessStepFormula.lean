/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookEUniformWitnessStep
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDfFormulaExactLCarrier
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0GodelGraph

/-!
# A fixed first-order graph for the simultaneous textbook E witness step

The formula in this file does not mention the externally chosen value of
`textbookEUniformWitnessStep`.  Internally it:

1. forms the Replacement range `{current^n | n in omega}`;
2. takes its union to obtain all finite tuple graphs over `current`;
3. forms the product of the fixed task domain with that tuple set;
4. forms the Replacement range of the uniform total witness formula; and
5. takes the binary union of `current` with that range.

The exact semantics theorem identifies the unique output with the previously
constructed internal step.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Extensional range, union, and product formulas -/

/-- Insert the bound range member into the layout `(params,domain,range)`. -/
def replacementRangeEqRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2))
    (fun i => i.castSucc.castSucc)

private theorem comp_replacementRangeEqRename
    {A : Type u} {n : Nat}
    (params : Tuple A n) (domain range output : A) :
    (fun i =>
      snoc (snoc (snoc params domain) range) output
        (replacementRangeEqRename i)) =
      snoc (snoc params domain) output := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementRangeEqRename]
  · simp [replacementRangeEqRename]

/--
Layout `(params,domain,range)`: `range` consists exactly of the outputs of
`phi` on members of `domain`.
-/
def replacementRangeEqFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc)
      (FOFormula.rename replacementRangeEqRename
        (replacementRangeFormula phi)))

@[simp]
theorem satisfies_replacementRangeEqFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (domain range : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementRangeEqFormula phi)
        (snoc (snoc params domain) range) <->
      ∀ output : LCarrier.{u},
        output.1 ∈ range.1 <->
          ∃ input : LCarrier.{u}, input.1 ∈ domain.1 /\
            FOFormula.Satisfies LMem phi
              (snoc (snoc params input) output) := by
  simp only [replacementRangeEqFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_rename,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    comp_replacementRangeEqRename,
    satisfies_replacementRangeFormula_lCarrier]

/-- Layout with arbitrary coordinates: `output` is `sUnion family`. -/
def sUnionEqAt {n : Nat} (output family : Fin n) : FOFormula n :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last n) output.castSucc)
      (.ex
        (.conj
          (.mem (Fin.last (n + 1)) family.castSucc.castSucc)
          (.mem (Fin.last n).castSucc (Fin.last (n + 1))))))

@[simp]
theorem satisfies_sUnionEqAt_lCarrier {n : Nat}
    (output family : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (sUnionEqAt output family) s <->
      s output = sUnionLCarrier (s family) := by
  simp only [sUnionEqAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (s output).2⟩
      rcases (h zL).mp hz with
        ⟨member, hmember, hzMember⟩
      exact ZFSet.mem_sUnion.mpr
        ⟨member.1, hmember, hzMember⟩
    · intro hz
      rcases ZFSet.mem_sUnion.mp hz with
        ⟨member, hmember, hzMember⟩
      let memberL : LCarrier.{u} :=
        ⟨member, mem_L_of_mem hmember (s family).2⟩
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hzMember memberL.2⟩
      exact (h zL).mpr ⟨memberL, hmember, hzMember⟩
  · intro h z
    rw [h]
    change z.1 ∈ (sUnionLCarrier (s family)).1 <->
      ∃ member : LCarrier.{u},
        member.1 ∈ (s family).1 /\ z.1 ∈ member.1
    exact mem_sUnionLCarrier_iff (s family) z

/-- Layout with arbitrary coordinates: `output = left x right`. -/
def productEqAt {n : Nat}
    (output left right : Fin n) : FOFormula n :=
  FOFormula.rename ![output, left, right]
    Godel.graphF2Formula.toFO

@[simp]
theorem satisfies_productEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (productEqAt output left right) s <->
      s output = prodLCarrier (s left) (s right) := by
  rw [productEqAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![output, left, right] i)) =
        ![s output, s left, s right] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hrawAssign :
      (fun i => (![s output, s left, s right] i).1) =
        ![(s output).1, (s left).1, (s right).1] := by
    funext i
    fin_cases i <;> rfl
  rw [hrawAssign, Delta0Formula.satisfies_toFO,
    Godel.satisfies_graphF2Formula]
  constructor
  · intro h
    apply Subtype.ext
    simpa only [Godel.F2, prodLCarrier_val] using h
  · intro h
    have hraw := congrArg Subtype.val h
    simpa only [Godel.F2, prodLCarrier_val] using hraw

/-- Layout with arbitrary coordinates: `output = left union right`. -/
def binaryUnionEqAt {n : Nat}
    (output left right : Fin n) : FOFormula n :=
  .all
    (FOFormula.biimp
      (.mem (Fin.last n) output.castSucc)
      (FOFormula.disj
        (.mem (Fin.last n) left.castSucc)
        (.mem (Fin.last n) right.castSucc)))

@[simp]
theorem satisfies_binaryUnionEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (binaryUnionEqAt output left right) s <->
      s output = unionLCarrier (s left) (s right) := by
  simp only [binaryUnionEqAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (s output).2⟩
      exact (mem_unionLCarrier_iff (s left) (s right) zL).mpr
        ((h zL).mp hz)
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz (unionLCarrier (s left) (s right)).2⟩
      rcases (mem_unionLCarrier_iff
          (s left) (s right) zL).mp hz with
        hzLeft | hzRight
      · let zL : LCarrier.{u} :=
          ⟨z, mem_L_of_mem hzLeft (s left).2⟩
        exact (h zL).mpr (Or.inl hzLeft)
      · let zL : LCarrier.{u} :=
          ⟨z, mem_L_of_mem hzRight (s right).2⟩
        exact (h zL).mpr (Or.inr hzRight)
  · intro h z
    rw [h]
    exact mem_unionLCarrier_iff (s left) (s right) z

/-! ## The fixed step graph -/

/--
The body layout is

`[U,order,tasks,omega,current,next,tupleFamily,prefixSpaces,
  requestDomain,selectedRange]`.
-/
def textbookEUniformWitnessStepBody : FOFormula 10 :=
  .conj
    (FOFormula.rename ![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)]
      (replacementRangeEqFormula
        ContinuumFormula.finiteTupleSpaceFormula))
  <| .conj
    (sUnionEqAt (7 : Fin 10) (6 : Fin 10))
  <| .conj
    (productEqAt (8 : Fin 10) (2 : Fin 10) (7 : Fin 10))
  <| .conj
    (FOFormula.rename
      ![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
        (8 : Fin 10), (9 : Fin 10)]
      (replacementRangeEqFormula textbookEUniformTotalFormula))
    (binaryUnionEqAt
      (5 : Fin 10) (4 : Fin 10) (9 : Fin 10))

/--
Layout `[U,order,tasks,omega,current,next]`.  The remaining four coordinates
are internally quantified intermediate sets.
-/
def textbookEUniformWitnessStepFormula : FOFormula 6 :=
  .ex <| .ex <| .ex <| .ex
    textbookEUniformWitnessStepBody

@[simp]
theorem satisfies_textbookEUniformWitnessStepFormula
    (U order tasks omega current next : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformWitnessStepFormula
        ![U, order, tasks, omega, current, next] <->
      ∃ tupleFamily prefixSpaces requestDomain selectedRange : LCarrier.{u},
        (∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
          ∃ index : LCarrier.{u}, index.1 ∈ omega.1 /\
            FOFormula.Satisfies LMem
              ContinuumFormula.finiteTupleSpaceFormula
              ![current, index, space]) /\
        prefixSpaces = sUnionLCarrier tupleFamily /\
        requestDomain = prodLCarrier tasks prefixSpaces /\
        (∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u}, request.1 ∈ requestDomain.1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, order, request, output]) /\
        next = unionLCarrier current selectedRange := by
  simp only [textbookEUniformWitnessStepFormula, FOFormula.Satisfies]
  apply exists_congr
  intro tupleFamily
  apply exists_congr
  intro prefixSpaces
  apply exists_congr
  intro requestDomain
  apply exists_congr
  intro selectedRange
  let assignment : Tuple LCarrier.{u} 10 :=
    snoc (snoc (snoc (snoc
      ![U, order, tasks, omega, current, next]
      tupleFamily) prefixSpaces) requestDomain) selectedRange
  change
    (FOFormula.Satisfies LMem
        (FOFormula.rename ![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)]
          (replacementRangeEqFormula
            ContinuumFormula.finiteTupleSpaceFormula)) assignment /\
      FOFormula.Satisfies LMem
        (sUnionEqAt (7 : Fin 10) (6 : Fin 10)) assignment /\
      FOFormula.Satisfies LMem
        (productEqAt (8 : Fin 10) (2 : Fin 10) (7 : Fin 10)) assignment /\
      FOFormula.Satisfies LMem
        (FOFormula.rename
          ![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
            (8 : Fin 10), (9 : Fin 10)]
          (replacementRangeEqFormula textbookEUniformTotalFormula))
          assignment /\
      FOFormula.Satisfies LMem
        (binaryUnionEqAt
          (5 : Fin 10) (4 : Fin 10) (9 : Fin 10)) assignment) <->
      _
  simp only [FOFormula.satisfies_rename]
  have htuple :
      (fun i =>
        assignment
          (![(4 : Fin 10), (3 : Fin 10), (6 : Fin 10)] i)) =
        ![current, omega, tupleFamily] := by
    funext i
    fin_cases i <;> rfl
  have hrange :
      (fun i =>
        assignment
          (![(0 : Fin 10), (4 : Fin 10), (1 : Fin 10),
            (8 : Fin 10), (9 : Fin 10)] i)) =
        ![U, current, order, requestDomain, selectedRange] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, hrange]
  have htupleSemantics :
      FOFormula.Satisfies LMem
          (replacementRangeEqFormula
            ContinuumFormula.finiteTupleSpaceFormula)
          ![current, omega, tupleFamily] <->
        ∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
          ∃ index : LCarrier.{u}, index.1 ∈ omega.1 /\
            FOFormula.Satisfies LMem
              ContinuumFormula.finiteTupleSpaceFormula
              ![current, index, space] := by
    have h := satisfies_replacementRangeEqFormula_lCarrier
      ContinuumFormula.finiteTupleSpaceFormula
      ![current] omega tupleFamily
    have hinputAssignment :
        ∀ index space : LCarrier.{u},
          snoc (snoc ![current] index) space =
            ![current, index, space] := by
      intro index space
      funext i
      fin_cases i <;> rfl
    simpa only [hinputAssignment, show
      snoc (snoc ![current] omega) tupleFamily =
        ![current, omega, tupleFamily] by
          funext i
          fin_cases i <;> rfl] using h
  have hselectedSemantics :
      FOFormula.Satisfies LMem
          (replacementRangeEqFormula textbookEUniformTotalFormula)
          ![U, current, order, requestDomain, selectedRange] <->
        ∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u}, request.1 ∈ requestDomain.1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, order, request, output] := by
    have h := satisfies_replacementRangeEqFormula_lCarrier
      textbookEUniformTotalFormula
      ![U, current, order] requestDomain selectedRange
    have hinputAssignment :
        ∀ request output : LCarrier.{u},
          snoc (snoc ![U, current, order] request) output =
            ![U, current, order, request, output] := by
      intro request output
      funext i
      fin_cases i <;> rfl
    simpa only [hinputAssignment, show
      snoc (snoc ![U, current, order] requestDomain) selectedRange =
        ![U, current, order, requestDomain, selectedRange] by
          funext i
          fin_cases i <;> rfl] using h
  rw [htupleSemantics, hselectedSemantics]
  simp only [satisfies_sUnionEqAt_lCarrier,
    satisfies_productEqAt_lCarrier,
    satisfies_binaryUnionEqAt_lCarrier]
  have ha2 : assignment (2 : Fin 10) = tasks := by rfl
  have ha4 : assignment (4 : Fin 10) = current := by rfl
  have ha5 : assignment (5 : Fin 10) = next := by rfl
  have ha6 : assignment (6 : Fin 10) = tupleFamily := by rfl
  have ha7 : assignment (7 : Fin 10) = prefixSpaces := by rfl
  have ha8 : assignment (8 : Fin 10) = requestDomain := by rfl
  have ha9 : assignment (9 : Fin 10) = selectedRange := by rfl
  rw [ha2, ha4, ha5, ha6, ha7, ha8, ha9]

/-! ## Identification with the constructed step -/

private theorem mem_internalFiniteTupleSpaceFamily_iff_replacement
    (current space : LCarrier.{u}) :
    space.1 ∈
        (ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family.1 <->
      ∃ index : LCarrier.{u},
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![current, index, space] := by
  constructor
  · intro hspace
    rcases
        (ContinuumFormula.internalFiniteTupleSpaceFamilyData current)
          |>.mem_family_iff space |>.mp hspace with
      ⟨n, hspaceEq⟩
    let index :=
      TextbookNatFormula.textbookNatCodeLCarrier n
    refine ⟨index, ?_, ?_⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · subst space
      exact
        (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
          current
          (ContinuumFormula.finiteTupleSpaceLCarrier current n) n).mpr
            rfl
  · rintro ⟨index, hindex, hspace⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with
      ⟨n, hindexRaw⟩
    have hindexEq :
        index = TextbookNatFormula.textbookNatCodeLCarrier n :=
      Subtype.ext hindexRaw
    subst index
    have hspaceRaw :
        space.1 = textbookTupleSpace current.1 n :=
      (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
        current space n).mp hspace
    have hspaceEq :
        space = ContinuumFormula.finiteTupleSpaceLCarrier current n :=
      Subtype.ext hspaceRaw
    exact
      (ContinuumFormula.internalFiniteTupleSpaceFamilyData current)
        |>.mem_family_iff space |>.mpr ⟨n, hspaceEq⟩

private theorem tupleFamily_eq_internal
    (current tupleFamily : LCarrier.{u})
    (hfamily : ∀ space : LCarrier.{u}, space.1 ∈ tupleFamily.1 <->
      ∃ index : LCarrier.{u},
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![current, index, space]) :
    tupleFamily =
      (ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family := by
  apply Subtype.ext
  apply ZFSet.ext
  intro space
  constructor
  · intro hspace
    let spaceL : LCarrier.{u} :=
      ⟨space, mem_L_of_mem hspace tupleFamily.2⟩
    exact
      (mem_internalFiniteTupleSpaceFamily_iff_replacement
        current spaceL).mpr ((hfamily spaceL).mp hspace)
  · intro hspace
    let spaceL : LCarrier.{u} :=
      ⟨space,
        mem_L_of_mem hspace
          (ContinuumFormula.internalFiniteTupleSpaceFamilyData
            current).family.2⟩
    exact (hfamily spaceL).mpr
      ((mem_internalFiniteTupleSpaceFamily_iff_replacement
        current spaceL).mp hspace)

private theorem selectedRange_eq_internal
    (U current selectedRange : LCarrier.{u})
    (hrange : ∀ output : LCarrier.{u}, output.1 ∈ selectedRange.1 <->
      ∃ request : LCarrier.{u},
        request.1 ∈
          (textbookEUniformWitnessRequestDomain current).1 /\
        FOFormula.Satisfies LMem textbookEUniformTotalFormula
          ![U, current, canonicalWitnessOrder U, request, output]) :
    selectedRange =
      (textbookEUniformWitnessReplacementData current U).range := by
  apply Subtype.ext
  apply ZFSet.ext
  intro output
  constructor
  · intro houtput
    let outputL : LCarrier.{u} :=
      ⟨output, mem_L_of_mem houtput selectedRange.2⟩
    exact
      (textbookEUniformWitnessReplacementData current U)
        |>.mem_range_iff outputL |>.mpr ((hrange outputL).mp houtput)
  · intro houtput
    let outputL : LCarrier.{u} :=
      ⟨output,
        mem_L_of_mem houtput
          (textbookEUniformWitnessReplacementData current U).range.2⟩
    exact (hrange outputL).mpr
      ((textbookEUniformWitnessReplacementData current U)
        |>.mem_range_iff outputL |>.mp houtput)

/-- Exact LCarrier semantics of the fixed graph at its canonical parameters. -/
@[simp]
theorem satisfies_textbookEUniformWitnessStepFormula_iff
    (U current next : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformWitnessStepFormula
        ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain,
          omegaLCarrier, current, next] <->
      next = textbookEUniformWitnessStep current U := by
  rw [satisfies_textbookEUniformWitnessStepFormula]
  constructor
  · rintro ⟨tupleFamily, prefixSpaces, requestDomain, selectedRange,
      htupleFamily, hprefixSpaces, hrequestDomain, hselectedRange, hnext⟩
    have htupleEq :=
      tupleFamily_eq_internal current tupleFamily htupleFamily
    have hprefixEq :
        prefixSpaces =
          ContinuumFormula.internalFiniteTupleSpaces current := by
      rw [hprefixSpaces, htupleEq]
      rfl
    have hrequestEq :
        requestDomain =
          textbookEUniformWitnessRequestDomain current := by
      rw [hrequestDomain, hprefixEq]
      rfl
    have hselectedSpec : ∀ output : LCarrier.{u},
        output.1 ∈ selectedRange.1 <->
          ∃ request : LCarrier.{u},
            request.1 ∈
              (textbookEUniformWitnessRequestDomain current).1 /\
            FOFormula.Satisfies LMem textbookEUniformTotalFormula
              ![U, current, canonicalWitnessOrder U, request, output] := by
      simpa only [hrequestEq] using hselectedRange
    have hselectedEq :=
      selectedRange_eq_internal U current selectedRange hselectedSpec
    rw [hnext, hselectedEq]
    rfl
  · intro hnext
    subst next
    refine
      ⟨(ContinuumFormula.internalFiniteTupleSpaceFamilyData current).family,
        ContinuumFormula.internalFiniteTupleSpaces current,
        textbookEUniformWitnessRequestDomain current,
        (textbookEUniformWitnessReplacementData current U).range,
        ?_, rfl, rfl, ?_, rfl⟩
    · exact mem_internalFiniteTupleSpaceFamily_iff_replacement current
    · exact
        (textbookEUniformWitnessReplacementData current U).mem_range_iff

/-- The fixed graph has exactly one next stage for every current stage. -/
theorem textbookEUniformWitnessStepFormula_existsUnique
    (U current : LCarrier.{u}) :
    ExistsUnique fun next : LCarrier.{u} =>
      FOFormula.Satisfies LMem textbookEUniformWitnessStepFormula
        ![U, canonicalWitnessOrder U, textbookEWitnessTaskDomain,
          omegaLCarrier, current, next] := by
  refine ⟨textbookEUniformWitnessStep current U, ?_, ?_⟩
  · exact
      (satisfies_textbookEUniformWitnessStepFormula_iff
        U current (textbookEUniformWitnessStep current U)).mpr rfl
  · intro next hnext
    exact
      (satisfies_textbookEUniformWitnessStepFormula_iff
        U current next).mp hnext

end

end Constructible.Model
