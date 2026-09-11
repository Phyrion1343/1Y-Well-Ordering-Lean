/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalFiniteTupleSpaces
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalInfiniteCardinalSquare
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.FormulaRestrictionLCarrier

/-!
# An internal injection for all finite tuples

Let `a` inject into an infinite internal cardinal `kappa`, and let
`kappa x kappa` inject into `kappa`.  A finite tuple is folded from left to
right with the latter injection.  Its arity is folded into the result once
more, so tuples of different lengths have different codes.

The fold is described by one first-order formula.  Its finite history is an
actual member of `L`, and Separation therefore produces one genuine
Kuratowski graph for the injection.  No externally chosen family of graphs
is used as the represented function.
-/

@[expose] public section

universe u

namespace Constructible.ContinuumFormula

open Constructible
open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The uniform finite-fold formula -/

/-- The semantic transition made at each tuple index. -/
def FiniteTupleFoldStep
    (aInjection squareInjection tuple history arity : LCarrier.{u}) : Prop :=
  forall index : LCarrier.{u}, index.1 ∈ arity.1 ->
    exists indexSucc entry entryCode current next pair : LCarrier.{u},
      indexSucc.1 = insert index.1 index.1 /\
        ZFSet.pair index.1 entry.1 ∈ tuple.1 /\
        ZFSet.pair entry.1 entryCode.1 ∈ aInjection.1 /\
        ZFSet.pair index.1 current.1 ∈ history.1 /\
        ZFSet.pair indexSucc.1 next.1 ∈ history.1 /\
        pair.1 = ZFSet.pair current.1 entryCode.1 /\
        ZFSet.pair pair.1 next.1 ∈ squareInjection.1

def finiteTupleFoldStepBodyFormula : FOFormula 12 :=
  .conj
    (Delta0Formula.successorFOAt (6 : Fin 12) (5 : Fin 12))
    (.conj
      (TextbookDefFormula.graphValueAt
        (2 : Fin 12) (5 : Fin 12) (7 : Fin 12))
      (.conj
        (TextbookDefFormula.graphValueAt
          (0 : Fin 12) (7 : Fin 12) (8 : Fin 12))
        (.conj
          (TextbookDefFormula.graphValueAt
            (3 : Fin 12) (5 : Fin 12) (9 : Fin 12))
          (.conj
            (TextbookDefFormula.graphValueAt
              (3 : Fin 12) (6 : Fin 12) (10 : Fin 12))
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                (11 : Fin 12) (9 : Fin 12) (8 : Fin 12)).toFO
              (TextbookDefFormula.graphValueAt
                (1 : Fin 12) (11 : Fin 12) (10 : Fin 12)))))))

@[simp]
theorem satisfies_finiteTupleFoldStepBodyFormula
    (s : Tuple LCarrier.{u} 12) :
    FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula s <->
      (s 6).1 = insert (s 5).1 (s 5).1 /\
        ZFSet.pair (s 5).1 (s 7).1 ∈ (s 2).1 /\
        ZFSet.pair (s 7).1 (s 8).1 ∈ (s 0).1 /\
        ZFSet.pair (s 5).1 (s 9).1 ∈ (s 3).1 /\
        ZFSet.pair (s 6).1 (s 10).1 ∈ (s 3).1 /\
        (s 11).1 = ZFSet.pair (s 9).1 (s 8).1 /\
        ZFSet.pair (s 11).1 (s 10).1 ∈ (s 1).1 := by
  simp only [finiteTupleFoldStepBodyFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    Constructible.Model.satisfies_graphValueAt_lCarrier,
    Constructible.Model.satisfies_kuratowskiPairEqAt_lCarrier_generic]

/--
Layout `[aInjection, squareInjection, tuple, history, arity]`.
The six witnesses are the successor index, tuple entry, entry code, current
fold value, next fold value, and their Kuratowski input pair.
-/
def finiteTupleFoldStepFormula : FOFormula 5 :=
  FOFormula.boundedAll (4 : Fin 5)
    (.ex (.ex (.ex (.ex (.ex (.ex
      finiteTupleFoldStepBodyFormula))))))

private theorem satisfies_finiteTupleFoldStepExistentials
    (s : Tuple LCarrier.{u} 6) :
    FOFormula.Satisfies LMem
        (.ex (.ex (.ex (.ex (.ex (.ex
          finiteTupleFoldStepBodyFormula)))))) s ↔
      ∃ indexSucc entry entryCode current next pair : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula
          (snoc (snoc (snoc (snoc (snoc (snoc
            s indexSucc) entry) entryCode) current) next) pair) := by
  rfl

private theorem snoc_eq_finSnoc
    {A : Type u} {n : Nat} (s : Tuple A n) (x : A) :
    snoc s x = Fin.snoc s x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last, Fin.snoc_last]
  · rw [snoc_castSucc, Fin.snoc_castSucc]

private theorem finiteTupleFoldStep_assignment
    (aInjection squareInjection tuple history arity index
      indexSucc entry entryCode current next pair : LCarrier.{u}) :
    snoc (snoc (snoc (snoc (snoc (snoc
      (snoc ![aInjection, squareInjection, tuple, history, arity] index)
      indexSucc) entry) entryCode) current) next) pair =
      ![aInjection, squareInjection, tuple, history, arity, index,
        indexSucc, entry, entryCode, current, next, pair] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

@[simp]
theorem satisfies_finiteTupleFoldStepFormula
    (aInjection squareInjection tuple history arity : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldStepFormula
        ![aInjection, squareInjection, tuple, history, arity] <->
      FiniteTupleFoldStep
        aInjection squareInjection tuple history arity := by
  rw [finiteTupleFoldStepFormula, FOFormula.satisfies_boundedAll]
  simp only [satisfies_finiteTupleFoldStepExistentials]
  change
    (∀ index : LCarrier.{u}, index.1 ∈ arity.1 →
      ∃ indexSucc entry entryCode current next pair : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula
          (snoc (snoc (snoc (snoc (snoc (snoc
            (snoc ![aInjection, squareInjection, tuple, history, arity]
              index)
            indexSucc) entry) entryCode) current) next) pair)) ↔
      FiniteTupleFoldStep
        aInjection squareInjection tuple history arity
  constructor
  · intro h index hindex
    rcases h index hindex with
      ⟨indexSucc, entry, entryCode, current, next, pair, hbody⟩
    refine ⟨indexSucc, entry, entryCode, current, next, pair, ?_⟩
    rw [finiteTupleFoldStep_assignment,
      satisfies_finiteTupleFoldStepBodyFormula] at hbody
    exact hbody
  · intro h index hindex
    rcases h index hindex with
      ⟨indexSucc, entry, entryCode, current, next, pair, hbody⟩
    refine ⟨indexSucc, entry, entryCode, current, next, pair, ?_⟩
    rw [finiteTupleFoldStep_assignment,
      satisfies_finiteTupleFoldStepBodyFormula]
    exact hbody

/-- Semantic content of one complete finite-fold certificate. -/
def FiniteTupleFoldCertificate
    (zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) : Prop :=
  ZFSet.IsFunc arity.1 a.1 tuple.1 /\
    ZFSet.IsFunc aritySucc.1 kappa.1 history.1 /\
    ZFSet.pair zero.1 zero.1 ∈ history.1 /\
    FiniteTupleFoldStep
      aInjection squareInjection tuple history arity /\
    exists current pair : LCarrier.{u},
      ZFSet.pair arity.1 current.1 ∈ history.1 /\
        pair.1 = ZFSet.pair arity.1 current.1 /\
        ZFSet.pair pair.1 output.1 ∈ squareInjection.1

/-- Select the five parameters of `finiteTupleFoldStepFormula` from the
certificate layout. -/
def finiteTupleFoldStepRename : Fin 5 -> Fin 11 :=
  ![4, 5, 6, 10, 8]

private theorem comp_finiteTupleFoldStepRename
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    (fun i =>
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history]
        (finiteTupleFoldStepRename i)) =
      ![aInjection, squareInjection, tuple, history, arity] := by
  funext i
  fin_cases i <;> rfl

/--
Layout
`[omega, zero, a, kappa, aInjection, squareInjection, tuple, output,
  arity, aritySucc, history]`.
-/
def finiteTupleFoldCertificateFormula : FOFormula 11 :=
  .conj
    (TextbookDefFormula.isFunctionAt
      (6 : Fin 11) (8 : Fin 11) (2 : Fin 11))
    (.conj
      (TextbookDefFormula.isFunctionAt
        (10 : Fin 11) (9 : Fin 11) (3 : Fin 11))
      (.conj
        (TextbookDefFormula.graphValueAt
          (10 : Fin 11) (1 : Fin 11) (1 : Fin 11))
        (.conj
          (FOFormula.rename finiteTupleFoldStepRename
            finiteTupleFoldStepFormula)
          (.ex (.ex
            (.conj
              (TextbookDefFormula.graphValueAt
                (10 : Fin 13) (8 : Fin 13) (11 : Fin 13))
              (.conj
                (Delta0Formula.kuratowskiPairEqAt
                  (12 : Fin 13) (8 : Fin 13) (11 : Fin 13)).toFO
                (TextbookDefFormula.graphValueAt
                  (5 : Fin 13) (12 : Fin 13) (7 : Fin 13)))))))))

private theorem finiteTupleFoldCertificate_final_assignment
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history current pair : LCarrier.{u}) :
    snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history] current) pair =
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history, current, pair] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_finiteTupleFoldCertificateFormula
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldCertificateFormula
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history] <->
      FiniteTupleFoldCertificate zero a kappa aInjection squareInjection
        tuple output arity aritySucc history := by
  simp only [finiteTupleFoldCertificateFormula, FOFormula.Satisfies,
    Constructible.Model.satisfies_isFunctionAt_lCarrier,
    Constructible.Model.satisfies_graphValueAt_lCarrier,
    FOFormula.satisfies_rename,
    comp_finiteTupleFoldStepRename,
    satisfies_finiteTupleFoldStepFormula,
    Constructible.Model.satisfies_kuratowskiPairEqAt_lCarrier_generic,
    FiniteTupleFoldCertificate]
  constructor
  · rintro ⟨htuple, hhistory, hzero, hstep,
      current, pair, hfinal⟩
    rw [finiteTupleFoldCertificate_final_assignment] at hfinal
    exact ⟨htuple, hhistory, hzero, hstep, current, pair, hfinal⟩
  · rintro ⟨htuple, hhistory, hzero, hstep,
      current, pair, hfinal⟩
    refine ⟨htuple, hhistory, hzero, hstep,
      current, pair, ?_⟩
    rw [finiteTupleFoldCertificate_final_assignment]
    exact hfinal

/-- A tuple/output pair is related when some standard finite arity and some
finite fold history give the output. -/
def FiniteTupleFoldRel
    (omega zero a kappa aInjection squareInjection
      tuple output : LCarrier.{u}) : Prop :=
  exists arity : LCarrier.{u}, arity.1 ∈ omega.1 /\
    exists aritySucc : LCarrier.{u},
      aritySucc.1 = insert arity.1 arity.1 /\
        exists history : LCarrier.{u},
          FiniteTupleFoldCertificate zero a kappa
            aInjection squareInjection tuple output
            arity aritySucc history

/--
Layout
`[omega, zero, a, kappa, aInjection, squareInjection, tuple, output]`.
-/
def finiteTupleFoldRelationFormula : FOFormula 8 :=
  .ex
    (.conj
      (.mem (8 : Fin 9) (0 : Fin 9))
      (.ex
        (.conj
          (Delta0Formula.successorFOAt
            (9 : Fin 10) (8 : Fin 10))
          (.ex finiteTupleFoldCertificateFormula))))

private theorem finiteTupleFoldRelation_assignment
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    snoc (snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output]
      arity) aritySucc) history =
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output,
        arity, aritySucc, history] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_finiteTupleFoldRelationFormula
    (omega zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output] <->
      FiniteTupleFoldRel omega zero a kappa
        aInjection squareInjection tuple output := by
  simp only [finiteTupleFoldRelationFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    FiniteTupleFoldRel]
  constructor
  · rintro ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
    rw [finiteTupleFoldRelation_assignment,
      satisfies_finiteTupleFoldCertificateFormula] at hcertificate
    exact ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
  · rintro ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
    refine ⟨arity, harity, aritySucc, hsucc, history, ?_⟩
    rw [finiteTupleFoldRelation_assignment,
      satisfies_finiteTupleFoldCertificateFormula]
    exact hcertificate

/-! ## Raw functionality and the two finite inductions -/

/-- Two set-theoretic function graphs with the same underlying set have the
same domain. -/
private theorem isFunc_domain_eq
    {left right codomain graph : ZFSet.{u}}
    (hleft : ZFSet.IsFunc left codomain graph)
    (hright : ZFSet.IsFunc right codomain graph) :
    left = right := by
  apply ZFSet.ext
  intro index
  constructor
  · intro hindex
    rcases hleft.2 index hindex with ⟨value, hvalue, _⟩
    exact (ZFSet.pair_mem_prod.mp (hright.1 hvalue)).1
  · intro hindex
    rcases hright.2 index hindex with ⟨value, hvalue, _⟩
    exact (ZFSet.pair_mem_prod.mp (hleft.1 hvalue)).1

/-- A `ZFSet.IsFunc` graph has at most one value at every displayed input. -/
private theorem isFunc_raw_value_unique
    {domain codomain graph index left right : ZFSet.{u}}
    (hfunc : ZFSet.IsFunc domain codomain graph)
    (hleft : ZFSet.pair index left ∈ graph)
    (hright : ZFSet.pair index right ∈ graph) :
    left = right := by
  have hindex : index ∈ domain :=
    (ZFSet.pair_mem_prod.mp (hfunc.1 hleft)).1
  rcases hfunc.2 index hindex with
    ⟨value, _hvalue, hvalueUnique⟩
  exact (hvalueUnique left hleft).trans
    (hvalueUnique right hright).symm

/-- Raw membership in an internal injection graph has unique output. -/
private theorem injection_raw_output_unique
    {graph domain codomain x left right : LCarrier.{u}}
    (hinjection : IsInjection LMem graph domain codomain)
    (hleft : ZFSet.pair x.1 left.1 ∈ graph.1)
    (hright : ZFSet.pair x.1 right.1 ∈ graph.1) :
    left = right := by
  have hleftValue : GraphValue LMem graph x left :=
    (graphValue_lCarrier_iff_graphRel graph x left).mpr hleft
  have hrightValue : GraphValue LMem graph x right :=
    (graphValue_lCarrier_iff_graphRel graph x right).mpr hright
  have hleftMem :=
    hinjection.1.graphValue_mem_lCarrier hleftValue
  have hrightMem :=
    hinjection.1.graphValue_mem_lCarrier hrightValue
  exact hinjection.toIsFunctionGraph.graphValue_unique
    hleftMem.1 hleftMem.2 hrightMem.2 hleftValue hrightValue

/-- Raw membership in an internal injection graph has unique input. -/
private theorem injection_raw_input_unique
    {graph domain codomain left right output : LCarrier.{u}}
    (hinjection : IsInjection LMem graph domain codomain)
    (hleft : ZFSet.pair left.1 output.1 ∈ graph.1)
    (hright : ZFSet.pair right.1 output.1 ∈ graph.1) :
    left = right := by
  have hleftValue : GraphValue LMem graph left output :=
    (graphValue_lCarrier_iff_graphRel graph left output).mpr hleft
  have hrightValue : GraphValue LMem graph right output :=
    (graphValue_lCarrier_iff_graphRel graph right output).mpr hright
  have hleftMem :=
    hinjection.1.graphValue_mem_lCarrier hleftValue
  have hrightMem :=
    hinjection.1.graphValue_mem_lCarrier hrightValue
  exact (hinjection.2.2 output hleftMem.2
    left hleftMem.1 hleftValue
    right hrightMem.1 hrightValue).symm

private theorem natCode_mem_succ_of_mem
    {n : Nat} {index : ZFSet.{u}}
    (hindex : index ∈ (natCode n : ZFSet.{u})) :
    index ∈ (natCode (n + 1) : ZFSet.{u}) := by
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
      index n).mp hindex with ⟨i, hi, rfl⟩
  exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
    (natCode i) (n + 1)).mpr ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/--
Forward induction through two valid fold histories: for a fixed input tuple,
the values displayed at the final index agree.
-/
private theorem finiteTupleFold_final_unique
    {a kappa aInjection squareInjection tuple
      firstHistory secondHistory zero : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (htupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ tuple.1 →
        ZFSet.pair index right ∈ tuple.1 →
        left = right)
    (hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right)
    (hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right)
    (hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}))
    (hfirstZero : ZFSet.pair zero.1 zero.1 ∈ firstHistory.1)
    (hsecondZero : ZFSet.pair zero.1 zero.1 ∈ secondHistory.1)
    (n : Nat)
    (hfirstStep : FiniteTupleFoldStep aInjection squareInjection
      tuple firstHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    (hsecondStep : FiniteTupleFoldStep aInjection squareInjection
      tuple secondHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    {firstValue secondValue : LCarrier.{u}}
    (hfirstValue :
      ZFSet.pair (natCode n) firstValue.1 ∈ firstHistory.1)
    (hsecondValue :
      ZFSet.pair (natCode n) secondValue.1 ∈ secondHistory.1) :
    firstValue = secondValue := by
  induction n generalizing firstValue secondValue with
  | zero =>
      apply Subtype.ext
      have hfirstRaw : firstValue.1 = zero.1 := by
        apply hfirstHistoryFunctional hfirstValue
        simpa only [hzeroValue] using hfirstZero
      have hsecondRaw : secondValue.1 = zero.1 := by
        apply hsecondHistoryFunctional hsecondValue
        simpa only [hzeroValue] using hsecondZero
      exact hfirstRaw.trans hsecondRaw.symm
  | succ n ih =>
      let index : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier n
      have hindex :
          index.1 ∈
            (TextbookNatFormula.textbookNatCodeLCarrier (n + 1)).1 := by
        change (natCode n : ZFSet.{u}) ∈ natCode (n + 1)
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode n) (n + 1)).mpr ⟨n, Nat.lt_succ_self n, rfl⟩
      rcases hfirstStep index hindex with
        ⟨firstIndexSucc, firstEntry, firstEntryCode,
          firstCurrent, firstNext, firstPair,
          hfirstSucc, hfirstEntry, hfirstEntryCode,
          hfirstCurrent, hfirstNext, hfirstPair, hfirstSquare⟩
      rcases hsecondStep index hindex with
        ⟨secondIndexSucc, secondEntry, secondEntryCode,
          secondCurrent, secondNext, secondPair,
          hsecondSucc, hsecondEntry, hsecondEntryCode,
          hsecondCurrent, hsecondNext, hsecondPair, hsecondSquare⟩
      have hfirstNextAt :
          ZFSet.pair (natCode (n + 1)) firstNext.1 ∈ firstHistory.1 := by
        have hsucc :
            firstIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hfirstSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hfirstNext
      have hsecondNextAt :
          ZFSet.pair (natCode (n + 1)) secondNext.1 ∈
            secondHistory.1 := by
        have hsucc :
            secondIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hsecondSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hsecondNext
      have hfirstValueNext : firstValue = firstNext := by
        apply Subtype.ext
        exact hfirstHistoryFunctional hfirstValue hfirstNextAt
      have hsecondValueNext : secondValue = secondNext := by
        apply Subtype.ext
        exact hsecondHistoryFunctional hsecondValue hsecondNextAt
      have hfirstStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection tuple firstHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hfirstStep earlier (natCode_mem_succ_of_mem hearlier)
      have hsecondStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection tuple secondHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hsecondStep earlier (natCode_mem_succ_of_mem hearlier)
      have hcurrentEq : firstCurrent = secondCurrent :=
        ih hfirstStepRestricted hsecondStepRestricted
          hfirstCurrent hsecondCurrent
      have hentryRaw : firstEntry.1 = secondEntry.1 :=
        htupleFunctional hfirstEntry hsecondEntry
      have hentryEq : firstEntry = secondEntry :=
        Subtype.ext hentryRaw
      subst secondEntry
      have hentryCodeEq : firstEntryCode = secondEntryCode :=
        injection_raw_output_unique haInjection
          hfirstEntryCode hsecondEntryCode
      subst secondEntryCode
      subst secondCurrent
      have hpairEq : firstPair = secondPair := by
        apply Subtype.ext
        exact hfirstPair.trans hsecondPair.symm
      subst secondPair
      have hnextEq : firstNext = secondNext :=
        injection_raw_output_unique hsquareInjection
          hfirstSquare hsecondSquare
      exact hfirstValueNext.trans (hnextEq.trans hsecondValueNext.symm)

/--
Backward induction through two fold histories: equality of the final fold
values recovers every entry of the two input tuples.
-/
private theorem finiteTupleFold_entries_unique
    {a kappa aInjection squareInjection
      firstTuple secondTuple firstHistory secondHistory : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirstTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstTuple.1 →
        ZFSet.pair index right ∈ firstTuple.1 →
        left = right)
    (hsecondTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondTuple.1 →
        ZFSet.pair index right ∈ secondTuple.1 →
        left = right)
    (hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right)
    (hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right)
    (n : Nat)
    (hfirstStep : FiniteTupleFoldStep aInjection squareInjection
      firstTuple firstHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    (hsecondStep : FiniteTupleFoldStep aInjection squareInjection
      secondTuple secondHistory
        (TextbookNatFormula.textbookNatCodeLCarrier n))
    {firstFinal secondFinal : LCarrier.{u}}
    (hfirstFinal :
      ZFSet.pair (natCode n) firstFinal.1 ∈ firstHistory.1)
    (hsecondFinal :
      ZFSet.pair (natCode n) secondFinal.1 ∈ secondHistory.1)
    (hfinalEq : firstFinal = secondFinal) :
    ∀ i : Nat, i < n →
      ∀ firstEntry secondEntry : LCarrier.{u},
        ZFSet.pair (natCode i) firstEntry.1 ∈ firstTuple.1 →
        ZFSet.pair (natCode i) secondEntry.1 ∈ secondTuple.1 →
        firstEntry = secondEntry := by
  induction n generalizing firstFinal secondFinal with
  | zero =>
      intro i hi
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      let index : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier n
      have hindex :
          index.1 ∈
            (TextbookNatFormula.textbookNatCodeLCarrier (n + 1)).1 := by
        change (natCode n : ZFSet.{u}) ∈ natCode (n + 1)
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode n) (n + 1)).mpr ⟨n, Nat.lt_succ_self n, rfl⟩
      rcases hfirstStep index hindex with
        ⟨firstIndexSucc, firstEntry, firstEntryCode,
          firstCurrent, firstNext, firstPair,
          hfirstSucc, hfirstEntry, hfirstEntryCode,
          hfirstCurrent, hfirstNext, hfirstPair, hfirstSquare⟩
      rcases hsecondStep index hindex with
        ⟨secondIndexSucc, secondEntry, secondEntryCode,
          secondCurrent, secondNext, secondPair,
          hsecondSucc, hsecondEntry, hsecondEntryCode,
          hsecondCurrent, hsecondNext, hsecondPair, hsecondSquare⟩
      have hfirstNextAt :
          ZFSet.pair (natCode (n + 1)) firstNext.1 ∈ firstHistory.1 := by
        have hsucc :
            firstIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hfirstSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hfirstNext
      have hsecondNextAt :
          ZFSet.pair (natCode (n + 1)) secondNext.1 ∈
            secondHistory.1 := by
        have hsucc :
            secondIndexSucc.1 = (natCode (n + 1) : ZFSet.{u}) :=
          hsecondSucc.trans (FiniteSequenceZF.natCode_succ_eq_insert n).symm
        simpa only [hsucc] using hsecondNext
      have hfirstFinalNext : firstFinal = firstNext := by
        apply Subtype.ext
        exact hfirstHistoryFunctional hfirstFinal hfirstNextAt
      have hsecondFinalNext : secondFinal = secondNext := by
        apply Subtype.ext
        exact hsecondHistoryFunctional hsecondFinal hsecondNextAt
      have hnextEq : firstNext = secondNext :=
        hfirstFinalNext.symm.trans (hfinalEq.trans hsecondFinalNext)
      have hsecondSquare' :
          ZFSet.pair secondPair.1 firstNext.1 ∈ squareInjection.1 := by
        rw [hnextEq]
        exact hsecondSquare
      have hfoldInputEq : firstPair = secondPair :=
        injection_raw_input_unique hsquareInjection
          hfirstSquare hsecondSquare'
      have hfoldCoordinates : firstCurrent.1 = secondCurrent.1 ∧
          firstEntryCode.1 = secondEntryCode.1 := by
        apply ZFSet.pair_inj.mp
        exact hfirstPair.symm.trans
          (congrArg Subtype.val hfoldInputEq |>.trans hsecondPair)
      have hcurrentEq : firstCurrent = secondCurrent :=
        Subtype.ext hfoldCoordinates.1
      have hentryCodeEq : firstEntryCode = secondEntryCode :=
        Subtype.ext hfoldCoordinates.2
      subst secondEntryCode
      have hentryEq : firstEntry = secondEntry :=
        injection_raw_input_unique haInjection
          hfirstEntryCode hsecondEntryCode
      have hfirstStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection firstTuple firstHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hfirstStep earlier (natCode_mem_succ_of_mem hearlier)
      have hsecondStepRestricted : FiniteTupleFoldStep
          aInjection squareInjection secondTuple secondHistory
          (TextbookNatFormula.textbookNatCodeLCarrier n) := by
        intro earlier hearlier
        exact hsecondStep earlier (natCode_mem_succ_of_mem hearlier)
      intro i hi leftEntry rightEntry hleftEntry hrightEntry
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hiEarlier | rfl
      · exact ih hfirstStepRestricted hsecondStepRestricted
          hfirstCurrent hsecondCurrent hcurrentEq
          i hiEarlier leftEntry rightEntry hleftEntry hrightEntry
      · have hleftEq : leftEntry = firstEntry := by
          apply Subtype.ext
          exact hfirstTupleFunctional hleftEntry hfirstEntry
        have hrightEq : rightEntry = secondEntry := by
          apply Subtype.ext
          exact hsecondTupleFunctional hrightEntry hsecondEntry
        exact hleftEq.trans (hentryEq.trans hrightEq.symm)

/-! ## Semantic uniqueness of the fold relation -/

private theorem finiteTupleFoldRel_output_unique
    {zero a kappa aInjection squareInjection tuple
      firstOutput secondOutput : LCarrier.{u}}
    (hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}))
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirst : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple firstOutput)
    (hsecond : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple secondOutput) :
    firstOutput = secondOutput := by
  rcases hfirst with
    ⟨firstArity, hfirstArityOmega, firstAritySucc, hfirstSucc,
      firstHistory, hfirstTuple, hfirstHistory, hfirstZero, hfirstStep,
      firstCurrent, firstPair, hfirstCurrent, hfirstPair, hfirstOutput⟩
  rcases hsecond with
    ⟨secondArity, _hsecondArityOmega, secondAritySucc, hsecondSucc,
      secondHistory, hsecondTuple, hsecondHistory, hsecondZero, hsecondStep,
      secondCurrent, secondPair, hsecondCurrent, hsecondPair, hsecondOutput⟩
  have harityRaw : firstArity.1 = secondArity.1 :=
    isFunc_domain_eq hfirstTuple hsecondTuple
  have harityEq : firstArity = secondArity :=
    Subtype.ext harityRaw
  subst secondArity
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      firstArity.1).mp hfirstArityOmega with ⟨n, harityValue⟩
  have harityEqNat :
      firstArity =
        TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst firstArity
  have hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstHistory hleft hright
  have hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondHistory hleft hright
  have htupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ tuple.1 →
        ZFSet.pair index right ∈ tuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstTuple hleft hright
  have hcurrentEq : firstCurrent = secondCurrent :=
    finiteTupleFold_final_unique haInjection hsquareInjection
      htupleFunctional hfirstHistoryFunctional hsecondHistoryFunctional
      hzeroValue hfirstZero hsecondZero n hfirstStep hsecondStep
      hfirstCurrent hsecondCurrent
  subst secondCurrent
  have hpairEq : firstPair = secondPair := by
    apply Subtype.ext
    exact hfirstPair.trans hsecondPair.symm
  subst secondPair
  exact injection_raw_output_unique hsquareInjection
    hfirstOutput hsecondOutput

private theorem finiteTupleFoldRel_input_unique
    {zero a kappa aInjection squareInjection
      firstTuple secondTuple output : LCarrier.{u}}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hfirst : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection firstTuple output)
    (hsecond : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection secondTuple output) :
    firstTuple = secondTuple := by
  rcases hfirst with
    ⟨firstArity, hfirstArityOmega, firstAritySucc, hfirstSucc,
      firstHistory, hfirstTupleFunc, hfirstHistoryFunc, _hfirstZero,
      hfirstStep, firstCurrent, firstPair, hfirstCurrent,
      hfirstPair, hfirstOutput⟩
  rcases hsecond with
    ⟨secondArity, _hsecondArityOmega, secondAritySucc, hsecondSucc,
      secondHistory, hsecondTupleFunc, hsecondHistoryFunc, _hsecondZero,
      hsecondStep, secondCurrent, secondPair, hsecondCurrent,
      hsecondPair, hsecondOutput⟩
  have hfinalPairEq : firstPair = secondPair :=
    injection_raw_input_unique hsquareInjection
      hfirstOutput hsecondOutput
  have hcoordinates : firstArity.1 = secondArity.1 ∧
      firstCurrent.1 = secondCurrent.1 := by
    apply ZFSet.pair_inj.mp
    exact hfirstPair.symm.trans
      (congrArg Subtype.val hfinalPairEq |>.trans hsecondPair)
  have harityEq : firstArity = secondArity :=
    Subtype.ext hcoordinates.1
  have hcurrentEq : firstCurrent = secondCurrent :=
    Subtype.ext hcoordinates.2
  subst secondArity
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      firstArity.1).mp hfirstArityOmega with ⟨n, harityValue⟩
  have harityEqNat :
      firstArity =
        TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst firstArity
  have hfirstTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstTuple.1 →
        ZFSet.pair index right ∈ firstTuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstTupleFunc hleft hright
  have hsecondTupleFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondTuple.1 →
        ZFSet.pair index right ∈ secondTuple.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondTupleFunc hleft hright
  have hfirstHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ firstHistory.1 →
        ZFSet.pair index right ∈ firstHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hfirstHistoryFunc hleft hright
  have hsecondHistoryFunctional :
      ∀ {index left right : ZFSet.{u}},
        ZFSet.pair index left ∈ secondHistory.1 →
        ZFSet.pair index right ∈ secondHistory.1 →
        left = right :=
    fun {_index _left _right} hleft hright =>
      isFunc_raw_value_unique hsecondHistoryFunc hleft hright
  have hentries :=
    finiteTupleFold_entries_unique haInjection hsquareInjection
      hfirstTupleFunctional hsecondTupleFunctional
      hfirstHistoryFunctional hsecondHistoryFunctional
      n hfirstStep hsecondStep hfirstCurrent hsecondCurrent hcurrentEq
  rcases exists_textbookTupleGraph_eq_of_isFunc hfirstTupleFunc with
    ⟨firstEntries, hfirstGraph⟩
  rcases exists_textbookTupleGraph_eq_of_isFunc hsecondTupleFunc with
    ⟨secondEntries, hsecondGraph⟩
  have hentryTuples : firstEntries = secondEntries := by
    funext i
    let firstEntry : LCarrier.{u} :=
      ⟨(firstEntries i).1,
        mem_L_of_mem (firstEntries i).2 a.2⟩
    let secondEntry : LCarrier.{u} :=
      ⟨(secondEntries i).1,
        mem_L_of_mem (secondEntries i).2 a.2⟩
    have hfirstEntry :
        ZFSet.pair (natCode i.1) firstEntry.1 ∈ firstTuple.1 := by
      rw [← hfirstGraph]
      exact textbookTupleGraph_value firstEntries i
    have hsecondEntry :
        ZFSet.pair (natCode i.1) secondEntry.1 ∈ secondTuple.1 := by
      rw [← hsecondGraph]
      exact textbookTupleGraph_value secondEntries i
    exact Subtype.ext (congrArg (fun x : LCarrier.{u} => x.1)
      (hentries i.1 i.2 firstEntry secondEntry
        hfirstEntry hsecondEntry))
  apply Subtype.ext
  exact hfirstGraph.symm.trans
    ((congrArg textbookTupleGraph hentryTuples).trans hsecondGraph)

/-! ## A genuine finite history for every tuple -/

/-- Package two members of `kappa` as a member of `kappa × kappa`. -/
private def finiteTupleProductPoint
    (kappa : LCarrier.{u})
    (left right : RelationCarrier LMem kappa) :
    RelationCarrier LMem (prodLCarrier kappa kappa) :=
  ⟨orderedPairLCarrier left.1 right.1, by
    change ZFSet.pair left.1.1 right.1.1 ∈
      ZFSet.prod kappa.1 kappa.1
    rw [ZFSet.pair_mem_prod]
    exact ⟨left.2, right.2⟩⟩

/-- The external recursion used only to exhibit one finite internal history.
Every value lies in `kappa`, because each successor is read from the genuine
internal square-injection graph. -/
private noncomputable def finiteTupleFoldValues
    {a kappa aInjection squareInjection : LCarrier.{u}}
    {n : Nat}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (zero : RelationCarrier LMem kappa)
    (entries : Fin n → RelationCarrier LMem a) :
    Nat → RelationCarrier LMem kappa
  | 0 => zero
  | i + 1 =>
      if hi : i < n then
        hsquareInjection.toFun
          (finiteTupleProductPoint kappa
            (finiteTupleFoldValues
              haInjection hsquareInjection zero entries i)
            (haInjection.toFun (entries ⟨i, hi⟩)))
      else
        finiteTupleFoldValues
          haInjection hsquareInjection zero entries i

private theorem finiteTupleFoldValues_succ
    {a kappa aInjection squareInjection : LCarrier.{u}}
    {n i : Nat}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (zero : RelationCarrier LMem kappa)
    (entries : Fin n → RelationCarrier LMem a)
    (hi : i < n) :
    finiteTupleFoldValues
        haInjection hsquareInjection zero entries (i + 1) =
      hsquareInjection.toFun
        (finiteTupleProductPoint kappa
          (finiteTupleFoldValues
            haInjection hsquareInjection zero entries i)
          (haInjection.toFun (entries ⟨i, hi⟩))) := by
  simp only [finiteTupleFoldValues, hi, dite_true]

private theorem exists_finiteTupleFoldRel
    {a kappa aInjection squareInjection tuple : LCarrier.{u}}
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (htuple : tuple.1 ∈ (internalFiniteTupleSpaces a).1) :
    ∃ output : LCarrier.{u},
      output.1 ∈ kappa.1 ∧
        FiniteTupleFoldRel omegaLCarrier
          (TextbookNatFormula.textbookNatCodeLCarrier 0)
          a kappa aInjection squareInjection tuple output := by
  rcases (mem_internalFiniteTupleSpaces_iff a tuple).mp htuple with
    ⟨n, htupleSpace⟩
  have htupleFunc :
      ZFSet.IsFunc (natCode n) a.1 tuple.1 := by
    apply mem_textbookTupleSpace_iff.mp
    simpa only [finiteTupleSpaceLCarrier_val] using htupleSpace
  rcases exists_textbookTupleGraph_eq_of_isFunc htupleFunc with
    ⟨rawEntries, htupleGraph⟩
  let entries : Fin n → RelationCarrier LMem a :=
    fun i =>
      ⟨⟨(rawEntries i).1,
          mem_L_of_mem (rawEntries i).2 a.2⟩,
        (rawEntries i).2⟩
  have hnatOmega (m : Nat) :
      (TextbookNatFormula.textbookNatCodeLCarrier m).1 ∈
        (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode m : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode m)).mpr ⟨m, rfl⟩
  let natInKappa (m : Nat) : RelationCarrier LMem kappa :=
    ⟨TextbookNatFormula.textbookNatCodeLCarrier m,
      homega _ (hnatOmega m)⟩
  let values : Nat → RelationCarrier LMem kappa :=
    finiteTupleFoldValues haInjection hsquareInjection
      (natInKappa 0) entries
  let historyEntries : Tuple (ZFCarrier kappa.1) (n + 1) :=
    fun i => ⟨(values i.1).1.1, (values i.1).2⟩
  let history : LCarrier.{u} :=
    ⟨textbookTupleGraph historyEntries,
      textbookTupleGraph_mem_L kappa.2 historyEntries⟩
  let arity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let aritySucc : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier (n + 1)
  let finalPairPoint : RelationCarrier LMem (prodLCarrier kappa kappa) :=
    finiteTupleProductPoint kappa (natInKappa n) (values n)
  let outputPoint : RelationCarrier LMem kappa :=
    hsquareInjection.toFun finalPairPoint
  let output : LCarrier.{u} := outputPoint.1
  refine ⟨output, outputPoint.2, ?_⟩
  refine ⟨arity, hnatOmega n, aritySucc, ?_, history, ?_⟩
  · change (natCode (n + 1) : ZFSet.{u}) =
      insert (natCode n) (natCode n)
    exact FiniteSequenceZF.natCode_succ_eq_insert n
  · refine ⟨htupleFunc, ?_, ?_, ?_, ?_⟩
    · simpa only [history, aritySucc,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using
        textbookTupleGraph_isFunc historyEntries
    · have hzeroHistory :=
        textbookTupleGraph_value historyEntries
          (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
      simpa only [history, historyEntries, values,
        finiteTupleFoldValues, natInKappa,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using hzeroHistory
    · intro index hindex
      rcases (mem_natCode_iff_exists_fin index.1 n).mp
          (by simpa only [arity,
            TextbookNatFormula.textbookNatCodeLCarrier_val] using
              hindex) with
        ⟨i, hindexValue⟩
      have hindexEq :
          index =
            TextbookNatFormula.textbookNatCodeLCarrier i.1 := by
        apply Subtype.ext
        exact hindexValue
      subst index
      let indexSucc : LCarrier.{u} :=
        TextbookNatFormula.textbookNatCodeLCarrier (i.1 + 1)
      let entry : LCarrier.{u} := (entries i).1
      let entryCode : LCarrier.{u} :=
        (haInjection.toFun (entries i)).1
      let current : LCarrier.{u} := (values i.1).1
      let next : LCarrier.{u} := (values (i.1 + 1)).1
      let pairPoint : RelationCarrier LMem (prodLCarrier kappa kappa) :=
        finiteTupleProductPoint kappa
          (values i.1) (haInjection.toFun (entries i))
      let pair : LCarrier.{u} := pairPoint.1
      refine ⟨indexSucc, entry, entryCode, current, next, pair,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change (natCode (i.1 + 1) : ZFSet.{u}) =
          insert (natCode i.1) (natCode i.1)
        exact FiniteSequenceZF.natCode_succ_eq_insert i.1
      · have hentry :=
          textbookTupleGraph_value rawEntries i
        rw [htupleGraph] at hentry
        simpa only [entry, entries,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using hentry
      · have hentryCodeValue :=
          haInjection.toFun_graphValue (entries i)
        exact (graphValue_lCarrier_iff_graphRel
          aInjection entry entryCode).mp (by
            simpa only [entry, entryCode] using hentryCodeValue)
      · have hcurrentHistory :=
          textbookTupleGraph_value historyEntries
            (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1))
        simpa only [history, historyEntries, current,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hcurrentHistory
      · have hnextHistory :=
          textbookTupleGraph_value historyEntries
            (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1))
        simpa only [history, historyEntries, next, indexSucc,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hnextHistory
      · rfl
      · have hsquareValue :=
          hsquareInjection.toFun_graphValue pairPoint
        have hsquareRaw :=
          (graphValue_lCarrier_iff_graphRel
            squareInjection pair
              (hsquareInjection.toFun pairPoint).1).mp (by
                simpa only [pair, pairPoint] using hsquareValue)
        have hvaluesSucc :
            values (i.1 + 1) =
              hsquareInjection.toFun pairPoint := by
          simpa only [values, pairPoint] using
            finiteTupleFoldValues_succ
              haInjection hsquareInjection
              (natInKappa 0) entries i.2
        simpa only [next, hvaluesSucc,
          Constructible.Model.GraphRel] using hsquareRaw
    · refine ⟨(values n).1, finalPairPoint.1, ?_, ?_, ?_⟩
      · have hfinalHistory :=
          textbookTupleGraph_value historyEntries
            (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
        simpa only [history, historyEntries, arity,
          TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hfinalHistory
      · rfl
      · have houtputValue :=
          hsquareInjection.toFun_graphValue finalPairPoint
        exact (graphValue_lCarrier_iff_graphRel
          squareInjection finalPairPoint.1 output).mp (by
            simpa only [output, outputPoint] using houtputValue)

/-! ## Replacement constructs the complete injection graph -/

private theorem finiteTupleFoldRel_output_mem
    {zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}}
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (hrel : FiniteTupleFoldRel omegaLCarrier zero a kappa
      aInjection squareInjection tuple output) :
    output.1 ∈ kappa.1 := by
  rcases hrel with
    ⟨arity, _harityOmega, aritySucc, _hsucc, history,
      _htuple, _hhistory, _hzero, _hstep,
      current, pair, _hcurrent, _hpair, houtput⟩
  have hvalue : GraphValue LMem squareInjection pair output :=
    (graphValue_lCarrier_iff_graphRel
      squareInjection pair output).mpr houtput
  exact (hsquareInjection.1.graphValue_mem_lCarrier hvalue).2

private theorem finiteTupleFoldGraph_assignment
    (omega zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}) :
    snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection]
      tuple) output =
      ![omega, zero, a, kappa, aInjection, squareInjection,
        tuple, output] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

/--
Given genuine internal injections `a → kappa` and
`kappa × kappa → kappa`, Replacement constructs one genuine internal
injection from all finite tuples over `a` into `kappa`.
-/
theorem injects_internalFiniteTupleSpaces_of_square_lCarrier
    {a kappa aInjection squareInjection : LCarrier.{u}}
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa)
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa) :
    Injects LMem (internalFiniteTupleSpaces a) kappa := by
  let zero : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier 0
  let domain : LCarrier.{u} := internalFiniteTupleSpaces a
  let params : Tuple LCarrier.{u} 6 :=
    ![omegaLCarrier, zero, a, kappa, aInjection, squareInjection]
  have hzeroValue : zero.1 = (natCode 0 : ZFSet.{u}) :=
    TextbookNatFormula.textbookNatCodeLCarrier_val 0
  have hfun : ∀ tuple : LCarrier.{u}, tuple.1 ∈ domain.1 →
      ∃! output : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          (snoc (snoc params tuple) output) := by
    intro tuple htuple
    rcases exists_finiteTupleFoldRel homega haInjection
        hsquareInjection htuple with
      ⟨output, _houtputKappa, houtput⟩
    refine ⟨output, ?_, ?_⟩
    · change FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
        (snoc (snoc params tuple) output)
      rw [show snoc (snoc params tuple) output =
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] by
        simpa only [params] using finiteTupleFoldGraph_assignment
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple output]
      exact (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mpr houtput
    · intro other hother
      have hother' :
          FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
            ![omegaLCarrier, zero, a, kappa, aInjection,
              squareInjection, tuple, other] := by
        rw [← finiteTupleFoldGraph_assignment
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple other]
        simpa only [params] using hother
      have hotherRel :=
        (satisfies_finiteTupleFoldRelationFormula
          omegaLCarrier zero a kappa aInjection squareInjection
          tuple other).mp hother'
      exact finiteTupleFoldRel_output_unique hzeroValue
        haInjection hsquareInjection hotherRel houtput
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      finiteTupleFoldRelationFormula params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : ∀ tuple output : LCarrier.{u},
      GraphValue LMem graph tuple output ↔
        tuple.1 ∈ domain.1 ∧
          FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
            (snoc (snoc params tuple) output) := by
    intro tuple output
    constructor
    · rintro ⟨pair, hpairGraph, hpairTO⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨tuple', htuple', output', houtput', hpairEq⟩
      have hpairTORaw :=
        (isKuratowskiPairOf_lCarrier_iff
          pair tuple output).mp hpairTO
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairTORaw)
      have htupleEq : tuple' = tuple :=
        Subtype.ext hcoordinates.1
      have houtputEq : output' = output :=
        Subtype.ext hcoordinates.2
      subst tuple'
      subst output'
      exact ⟨htuple', houtput'⟩
    · rintro ⟨htuple, houtput⟩
      let pair := orderedPairLCarrier tuple output
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨tuple, htuple, output, houtput, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair tuple output).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain kappa := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨tuple, htuple, output, houtput, hpairEq⟩
    have houtput' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using houtput
    have hrel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp houtput'
    have houtputKappa :=
      finiteTupleFoldRel_output_mem hsquareInjection hrel
    exact ⟨tuple, htuple, output, houtputKappa,
      (isKuratowskiPairOf_lCarrier_iff
        pair tuple output).mpr hpairEq⟩
  refine ⟨graph, hbetween, ?_, ?_⟩
  · intro tuple htuple
    rcases hfun tuple htuple with
      ⟨output, houtput, houtputUnique⟩
    have houtput' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using houtput
    have hrel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp houtput'
    have houtputKappa :=
      finiteTupleFoldRel_output_mem hsquareInjection hrel
    refine ⟨output, houtputKappa,
      (hvalue tuple output).mpr ⟨htuple, houtput⟩, ?_⟩
    intro other _hotherKappa htupleOther
    apply houtputUnique other
    exact (hvalue tuple other).mp htupleOther |>.2
  · intro output _houtputKappa tuple htuple htupleOutput
      other hother hotherOutput
    have htupleFormula :=
      (hvalue tuple output).mp htupleOutput |>.2
    have hotherFormula :=
      (hvalue other output).mp hotherOutput |>.2
    have htupleFormula' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, tuple, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output]
      simpa only [params] using htupleFormula
    have hotherFormula' :
        FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
          ![omegaLCarrier, zero, a, kappa, aInjection,
            squareInjection, other, output] := by
      rw [← finiteTupleFoldGraph_assignment
        omegaLCarrier zero a kappa aInjection squareInjection
        other output]
      simpa only [params] using hotherFormula
    have htupleRel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        tuple output).mp htupleFormula'
    have hotherRel :=
      (satisfies_finiteTupleFoldRelationFormula
        omegaLCarrier zero a kappa aInjection squareInjection
        other output).mp hotherFormula'
    exact finiteTupleFoldRel_input_unique
      haInjection hsquareInjection hotherRel htupleRel

/-- The standard infinite-cardinal form: the square injection is supplied by
the internal theorem `kappa × kappa ↪ kappa`. -/
theorem injects_internalFiniteTupleSpaces_lCarrier
    {a kappa : LCarrier.{u}}
    (ha : Injects LMem a kappa)
    (hcardinal : IsCardinal LMem kappa)
    (homega : IsSubsetOf LMem
      (omegaLCarrier : LCarrier.{u}) kappa) :
    Injects LMem (internalFiniteTupleSpaces a) kappa := by
  rcases ha with ⟨aInjection, haInjection⟩
  rcases injects_infiniteCardinalSquare_lCarrier
      hcardinal homega with
    ⟨squareInjection, hsquareInjection⟩
  exact injects_internalFiniteTupleSpaces_of_square_lCarrier
    homega haInjection hsquareInjection

end

end Constructible.ContinuumFormula
