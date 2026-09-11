/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookClassWellFounded
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel

/-!
# First-order formulas for textbook class recursion

This file begins the syntax layer needed to interpret the recursion theorem of
Section 6.1 of Wang Fangting, *Axiomatic Set Theory*, inside a transitive model.
The formulas are uniformly parameterized.  Their variable layouts are

* `classFormula(params, x)`,
* `relationFormula(params, y, x)`,
* `stepFormula(params, x, q, z)`, and
* the output formulas use `(params, x, output)`.

At this stage the file formalizes the assertion that the relation is set-like,
its displayed predecessor sets, and the canonical local domain

`d_x = {x} union cl(A,x,R)`.

The local domain is described syntactically as the least downward-closed set
containing `x`.  The final theorem proves that this description is exactly the
previously constructed `localRecursionDomain` whenever that actual set and the
candidate interpretation belong to the transitive carrier.  Thus the formula
does not silently replace the textbook definition.

The final formulas describe a candidate local solution graph and its value at
one point.  They do not assert that such a graph belongs to a model; that
existence theorem is a separate mathematical obligation.  In particular,
the formulas below do not refer to a recursively defined function and contain
no syntactic self-reference.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-! ## Raw restricted-semantics helpers -/

private theorem satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_imp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s <->
      (SatisfiesIn M left s -> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

private theorem satisfiesIn_biimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn,
    satisfiesIn_imp_iff]
  tauto

private theorem satisfiesIn_boundedAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall x : ZFSet.{u}, x ∈ M -> x ∈ s set ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h x hxM hxSet
    by_contra hx
    exact h ⟨x, hxM, by simpa using hxSet, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxSet, hx⟩
    exact hx (h x hxM (by simpa using hxSet))

private theorem satisfiesIn_rename_iff
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s <->
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-! ## Formula insertion at named coordinates -/

/-- Insert `classFormula(params,x)` into a larger variable context. -/
def classFormulaAt {n m : Nat} (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (x : Fin m) : FOFormula m :=
  FOFormula.rename (Fin.lastCases x params) classFormula

/-- Insert `relationFormula(params,y,x)` into a larger variable context. -/
def relationFormulaAt {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (y x : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases x (fun j => Fin.lastCases y params j))
    relationFormula

/-- Insert `stepFormula(params,x,graph,value)` into a larger context. -/
def stepFormulaAt {n m : Nat} (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases value (fun k =>
      Fin.lastCases graph (fun j => Fin.lastCases x params j) k))
    stepFormula

@[simp]
theorem satisfiesIn_classFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (x : Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (classFormulaAt classFormula params x) s <->
      SatisfiesIn M classFormula
        (snoc (fun i => s (params i)) (s x)) := by
  rw [classFormulaAt, satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s (Fin.lastCases x params i)) =
        snoc (fun i => s (params i)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hassignment]

@[simp]
theorem satisfiesIn_relationFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (y x : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (relationFormulaAt relationFormula params y x) s <->
      SatisfiesIn M relationFormula
        (snoc (snoc (fun i => s (params i)) (s y)) (s x)) := by
  rw [relationFormulaAt, satisfiesIn_rename_iff]
  have hassignment :
      (fun i =>
        s (Fin.lastCases x (fun j => Fin.lastCases y params j) i)) =
        snoc (snoc (fun i => s (params i)) (s y)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfiesIn_stepFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (stepFormulaAt stepFormula params x graph value) s <->
      SatisfiesIn M stepFormula
        (snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value)) := by
  rw [stepFormulaAt, satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s (Fin.lastCases value (fun k =>
        Fin.lastCases graph (fun j => Fin.lastCases x params j) k) i)) =
        snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simp
        · simp
  rw [hassignment]

/-! ## Kuratowski graph values -/

/-- In a context containing `graph`, `input`, and `value`, this formula says
that the Kuratowski pair `<input,value>` belongs to `graph`. -/
def graphValueFormulaAt {m : Nat}
    (graph input value : Fin m) : FOFormula m :=
  .ex (.conj
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last m) input.castSucc value.castSucc).toFO
    (.mem (Fin.last m) graph.castSucc))

private theorem satisfiesIn_kuratowskiPairEqAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (pair input value : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO s <->
      s pair = ZFSet.pair (s input) (s value) := by
  let sM : Tuple (ZFCarrier M) m := fun i => ⟨s i, hs i⟩
  calc
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO s <->
        FOFormula.Satisfies (zfCarrierMem M)
          (Delta0Formula.kuratowskiPairEqAt pair input value).toFO sM :=
      (satisfies_subtype_iff_satisfiesIn
        (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO sM).symm
    _ <-> Delta0Formula.Satisfies (zfCarrierMem M)
          (Delta0Formula.kuratowskiPairEqAt pair input value) sM :=
      Delta0Formula.satisfies_toFO (zfCarrierMem M) _ sM
    _ <-> Delta0Formula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.kuratowskiPairEqAt pair input value) s := by
      exact Delta0Formula.satisfies_absolute hM _ sM
    _ <-> s pair = ZFSet.pair (s input) (s value) :=
      Delta0Formula.satisfies_kuratowskiPairEqAt pair input value s

@[simp]
theorem satisfiesIn_graphValueFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (graph input value : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (graphValueFormulaAt graph input value) s <->
      ZFSet.pair (s input) (s value) ∈ s graph := by
  rw [graphValueFormulaAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨pair, hpairM, hpairEq, hpairGraph⟩
    have hs' : forall i, snoc s pair i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hpairM
      · simpa using hs j
    have hpair := (satisfiesIn_kuratowskiPairEqAt_iff hM
      (Fin.last m) input.castSucc value.castSucc (snoc s pair) hs').mp hpairEq
    have hpairRaw : pair = ZFSet.pair (s input) (s value) := by
      simpa only [snoc_last, snoc_castSucc] using hpair
    rw [hpairRaw] at hpairGraph
    simpa only [snoc_last, snoc_castSucc] using hpairGraph
  · intro hpairGraph
    have hpairM : ZFSet.pair (s input) (s value) ∈ M :=
      hM.mem_trans hpairGraph (hs graph)
    refine ⟨ZFSet.pair (s input) (s value), hpairM, ?_, ?_⟩
    · have hs' : forall i,
          snoc s (ZFSet.pair (s input) (s value)) i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hpairM
        · simpa using hs j
      apply (satisfiesIn_kuratowskiPairEqAt_iff hM
        (Fin.last m) input.castSucc value.castSucc
        (snoc s (ZFSet.pair (s input) (s value))) hs').mpr
      simp
    · simpa using hpairGraph

/-! ## Set-coded function graphs -/

/-- `graph` is a Kuratowski graph with domain exactly `domain`.  Totality and
uniqueness are asserted first; the second conjunct excludes non-pair or
off-domain elements of the graph. -/
def functionGraphOnFormulaAt {m : Nat}
    (graph domain : Fin m) : FOFormula m :=
  .conj
    (FOFormula.boundedAll domain <| .ex <| .conj
      (graphValueFormulaAt graph.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m + 1)))
      (FOFormula.all <| FOFormula.imp
        (graphValueFormulaAt graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
        (.eq (Fin.last (m + 2)) (Fin.last (m + 1)).castSucc)))
    (FOFormula.boundedAll graph <| .ex <| .conj
      (.mem (Fin.last (m + 1)) domain.castSucc.castSucc)
      (.ex
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2))).toFO))

@[simp]
theorem satisfiesIn_functionGraphOnFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (graph domain : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (functionGraphOnFormulaAt graph domain) s <->
      ((forall input : ZFSet.{u}, input ∈ M -> input ∈ s domain ->
          exists value : ZFSet.{u}, value ∈ M ∧
            ZFSet.pair input value ∈ s graph ∧
            forall other : ZFSet.{u}, other ∈ M ->
              ZFSet.pair input other ∈ s graph -> other = value) ∧
        forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ s graph ->
          exists input : ZFSet.{u}, input ∈ M ∧ input ∈ s domain ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value) := by
  rw [functionGraphOnFormulaAt]
  simp only [SatisfiesIn, satisfiesIn_boundedAll_iff,
    satisfiesIn_all_iff, satisfiesIn_imp_iff]
  constructor
  · rintro ⟨htotal, hcovered⟩
    constructor
    · intro input hinputM hinputDomain
      rcases htotal input hinputM hinputDomain with
        ⟨value, hvalueM, hvalue, hunique⟩
      have hsValue : forall i, snoc (snoc s input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · simpa using hs k
      have hvaluePair := (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m + 1))
        (snoc (snoc s input) value) hsValue).mp hvalue
      refine ⟨value, hvalueM, by simpa using hvaluePair, ?_⟩
      intro other hotherM hotherPair
      have hsOther : forall i,
          snoc (snoc (snoc s input) value) other i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hotherM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hinputM
            · simpa using hs l
      have hotherFormula : SatisfiesIn (M : Set ZFSet.{u})
          (graphValueFormulaAt graph.castSucc.castSucc.castSucc
            (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
          (snoc (snoc (snoc s input) value) other) := by
        apply (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s input) value) other) hsOther).mpr
        simpa using hotherPair
      have heq := hunique other hotherM hotherFormula
      simpa only [snoc_last, snoc_castSucc, SatisfiesIn] using heq
    · intro pair hpairM hpairGraph
      rcases hcovered pair hpairM hpairGraph with
        ⟨input, hinputM, hinputDomain, value, hvalueM, hpairFormula⟩
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨input, hinputM, ?_, value, hvalueM, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hinputDomain
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
  · rintro ⟨htotal, hcovered⟩
    constructor
    · intro input hinputM hinputDomain
      rcases htotal input hinputM hinputDomain with
        ⟨value, hvalueM, hvaluePair, hunique⟩
      refine ⟨value, hvalueM, ?_, ?_⟩
      · have hsValue : forall i, snoc (snoc s input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · simpa using hs k
        apply (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m + 1))
          (snoc (snoc s input) value) hsValue).mpr
        simpa using hvaluePair
      · intro other hotherM hotherFormula
        have hsOther : forall i,
            snoc (snoc (snoc s input) value) other i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hotherM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hvalueM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hinputM
              · simpa using hs l
        have hotherPair := (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s input) value) other) hsOther).mp
            hotherFormula
        have heq := hunique other hotherM (by simpa using hotherPair)
        simpa only [snoc_last, snoc_castSucc, SatisfiesIn] using heq
    · intro pair hpairM hpairGraph
      rcases hcovered pair hpairM hpairGraph with
        ⟨input, hinputM, hinputDomain, value, hvalueM, hpairEq⟩
      refine ⟨input, hinputM, ?_, value, hvalueM, ?_⟩
      · simpa using hinputDomain
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq

/-! ## Restricting a graph to the predecessors of one point -/

/-- `restriction` consists exactly of the pairs in `graph` whose first
coordinate belongs to the formula class and is related to `top`. -/
def restrictionGraphFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph top restriction : Fin m) :
    FOFormula m :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last m) restriction.castSucc)
    (.conj
      (.mem (Fin.last m) graph.castSucc)
      (.ex <| .ex <| .conj
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2))).toFO
        (.conj
          (classFormulaAt classFormula
            (fun i => (params i).castSucc.castSucc.castSucc)
            (Fin.last (m + 1)).castSucc)
          (relationFormulaAt relationFormula
            (fun i => (params i).castSucc.castSucc.castSucc)
            (Fin.last (m + 1)).castSucc top.castSucc.castSucc.castSucc))))

@[simp]
theorem satisfiesIn_restrictionGraphFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph top restriction : Fin m)
    (s : Tuple ZFSet.{u} m) (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (restrictionGraphFormulaAt classFormula relationFormula
          params graph top restriction) s <->
      forall pair : ZFSet.{u}, pair ∈ M ->
        (pair ∈ s restriction <->
          pair ∈ s graph ∧
          exists input : ZFSet.{u}, input ∈ M ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value ∧
              SatisfiesIn (M : Set ZFSet.{u}) classFormula
                (snoc (fun i => s (params i)) input) ∧
              SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                (snoc (snoc (fun i => s (params i)) input) (s top))) := by
  rw [restrictionGraphFormulaAt, satisfiesIn_all_iff]
  simp only [satisfiesIn_biimp_iff, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff,
    snoc_last, snoc_castSucc]
  constructor
  · intro h pair hpairM
    have hpairSemantic := h pair hpairM
    constructor
    · intro hpairRestriction
      rcases hpairSemantic.mp hpairRestriction with
        ⟨hpairGraph, input, hinputM, value, hvalueM,
          hpairFormula, hclass, hrelation⟩
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
    · rintro ⟨hpairGraph, input, hinputM, value, hvalueM,
        hpairEq, hclass, hrelation⟩
      apply hpairSemantic.mpr
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
  · intro h pair hpairM
    have hpairRaw := h pair hpairM
    constructor
    · intro hpairRestriction
      rcases hpairRaw.mp hpairRestriction with
        ⟨hpairGraph, input, hinputM, value, hvalueM,
          hpairEq, hclass, hrelation⟩
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
    · rintro ⟨hpairGraph, input, hinputM, value, hvalueM,
        hpairFormula, hclass, hrelation⟩
      apply hpairRaw.mpr
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation

/-- Public parameter layout `(params,graph,top,restriction)`. -/
def restrictionGraphFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 3) :=
  restrictionGraphFormulaAt classFormula relationFormula
    (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc
    (Fin.last (n + 1)).castSucc
    (Fin.last (n + 2))

@[simp]
theorem satisfiesIn_restrictionGraphFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (graph top restriction : ZFSet.{u})
    (hparams : forall i, params i ∈ M)
    (hgraph : graph ∈ M) (htop : top ∈ M)
    (hrestriction : restriction ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (restrictionGraphFormula classFormula relationFormula)
        (snoc (snoc (snoc params graph) top) restriction) <->
      forall pair : ZFSet.{u}, pair ∈ M ->
        (pair ∈ restriction <->
          pair ∈ graph ∧
          exists input : ZFSet.{u}, input ∈ M ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value ∧
              SatisfiesIn (M : Set ZFSet.{u}) classFormula
                (snoc params input) ∧
              SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                (snoc (snoc params input) top)) := by
  let s := snoc (snoc (snoc params graph) top) restriction
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hrestriction
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using htop
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simpa [s] using hgraph
        · simpa [s] using hparams l
  simpa only [restrictionGraphFormula, s, snoc_last, snoc_castSucc] using
    (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
      relationFormula (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) s hs)

/-! ## Reusable set predicates -/

/-- Every member of `set` satisfies `classFormula`. -/
def subsetClassFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (set : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) set.castSucc)
    (classFormulaAt classFormula
      (fun i => (params i).castSucc) (Fin.last m))

/-- The set at `left` is a subset of the set at `right`. -/
def subsetFormulaAt {m : Nat} (left right : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) left.castSucc)
    (.mem (Fin.last m) right.castSucc)

/-- `set` is downward closed under the formula relation, relative to the
formula class. -/
def downwardClosedFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (set : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) set.castSucc)
    (FOFormula.all <| FOFormula.imp
      (.conj
        (classFormulaAt classFormula
          (fun i => (params i).castSucc.castSucc) (Fin.last (m + 1)))
        (relationFormulaAt relationFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last (m + 1)) (Fin.last m).castSucc))
      (.mem (Fin.last (m + 1)) set.castSucc.castSucc))

@[simp]
theorem satisfiesIn_subsetClassFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (set : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (subsetClassFormulaAt classFormula params set) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s set ->
        SatisfiesIn M classFormula
          (snoc (fun i => s (params i)) z) := by
  rw [subsetClassFormulaAt, satisfiesIn_all_iff]
  simp only [satisfiesIn_imp_iff, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff, snoc_last, snoc_castSucc]

@[simp]
theorem satisfiesIn_subsetFormulaAt_iff
    (M : Set ZFSet.{u}) {m : Nat} (left right : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (subsetFormulaAt left right) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s left -> z ∈ s right := by
  rw [subsetFormulaAt, satisfiesIn_all_iff]
  simp only [satisfiesIn_imp_iff, SatisfiesIn,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfiesIn_downwardClosedFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (set : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (downwardClosedFormulaAt classFormula relationFormula params set) s <->
      forall t : ZFSet.{u}, t ∈ M -> t ∈ s set ->
        forall y : ZFSet.{u}, y ∈ M ->
          SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) y) ->
          SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) y) t) ->
          y ∈ s set := by
  rw [downwardClosedFormulaAt, satisfiesIn_all_iff]
  simp only [satisfiesIn_imp_iff, SatisfiesIn, snoc_last,
    snoc_castSucc, satisfiesIn_all_iff,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff]
  constructor
  · intro h t htM htSet y hyM hyClass hyRelation
    exact h t htM htSet y hyM ⟨hyClass, hyRelation⟩
  · intro h t htM htSet y hyM hy
    exact h t htM htSet y hyM hy.1 hy.2

/-! ## Displayed predecessor sets -/

/-- In the layout `(params,x,predecessors)`, this formula says that
`predecessors` has exactly the members of the formula class which are related
to `x`. -/
def predecessorSetFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc)
    (.conj
      (classFormulaAt classFormula
        (fun i => i.castSucc.castSucc.castSucc) (Fin.last (n + 2)))
      (relationFormulaAt relationFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc))

@[simp]
theorem satisfiesIn_predecessorSetFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (x predecessors : ZFSet.{u}) :
    SatisfiesIn M (predecessorSetFormula classFormula relationFormula)
        (snoc (snoc params x) predecessors) <->
      forall y : ZFSet.{u}, y ∈ M ->
        (y ∈ predecessors <->
          SatisfiesIn M classFormula (snoc params y) ∧
          SatisfiesIn M relationFormula (snoc (snoc params y) x)) := by
  rw [predecessorSetFormula, satisfiesIn_all_iff]
  simp only [satisfiesIn_biimp_iff, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc]

/-! ## The internal assertion that the relation is set-like -/

/-- The formula, in the parameter context, saying that `relationFormula`
defines a relation on `classFormula` and every point of that class has a
displayed predecessor set. -/
def setLikeRelationOnFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula n :=
  .conj
    (FOFormula.all <| FOFormula.all <| FOFormula.imp
      (relationFormulaAt relationFormula
        (fun i => i.castSucc.castSucc)
        (Fin.last n).castSucc (Fin.last (n + 1)))
      (.conj
        (classFormulaAt classFormula
          (fun i => i.castSucc.castSucc) (Fin.last n).castSucc)
        (classFormulaAt classFormula
          (fun i => i.castSucc.castSucc) (Fin.last (n + 1)))))
    (FOFormula.all <| FOFormula.imp
      (classFormulaAt classFormula (fun i => i.castSucc) (Fin.last n))
      (.ex (predecessorSetFormula classFormula relationFormula)))

@[simp]
theorem satisfiesIn_setLikeRelationOnFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) :
    SatisfiesIn M (setLikeRelationOnFormula classFormula relationFormula)
        params <->
      (forall y : ZFSet.{u}, y ∈ M ->
        forall x : ZFSet.{u}, x ∈ M ->
          SatisfiesIn M relationFormula (snoc (snoc params y) x) ->
            SatisfiesIn M classFormula (snoc params y) ∧
            SatisfiesIn M classFormula (snoc params x)) ∧
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M classFormula (snoc params x) ->
          exists predecessors : ZFSet.{u}, predecessors ∈ M ∧
            forall y : ZFSet.{u}, y ∈ M ->
              (y ∈ predecessors <->
                SatisfiesIn M classFormula (snoc params y) ∧
                SatisfiesIn M relationFormula
                  (snoc (snoc params y) x)) := by
  rw [setLikeRelationOnFormula]
  simp only [SatisfiesIn, satisfiesIn_all_iff,
    satisfiesIn_imp_iff, satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc,
    satisfiesIn_predecessorSetFormula_iff]

/-! ## The canonical local recursion domain -/

/-- In the layout `(params,x,domain)`, this formula says that `domain` is the
least subset of the formula class which contains `x` and is downward closed
under the formula relation. -/
def localDomainFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let domain : Fin (n + 2) := Fin.last (n + 1)
  .conj
    (classFormulaAt classFormula params x)
    (.conj
      (.mem x domain)
      (.conj
        (subsetClassFormulaAt classFormula params domain)
        (.conj
          (downwardClosedFormulaAt classFormula relationFormula params domain)
          (FOFormula.all <| FOFormula.imp
            (.conj
              (.mem x.castSucc (Fin.last (n + 2)))
              (.conj
                (subsetClassFormulaAt classFormula
                  (fun i => (params i).castSucc) (Fin.last (n + 2)))
                (downwardClosedFormulaAt classFormula relationFormula
                  (fun i => (params i).castSucc) (Fin.last (n + 2)))))
            (subsetFormulaAt domain.castSucc (Fin.last (n + 2)))))))

@[simp]
theorem satisfiesIn_localDomainFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (x domain : ZFSet.{u}) :
    SatisfiesIn M (localDomainFormula classFormula relationFormula)
        (snoc (snoc params x) domain) <->
      SatisfiesIn M classFormula (snoc params x) ∧
      x ∈ domain ∧
      (forall z : ZFSet.{u}, z ∈ M -> z ∈ domain ->
        SatisfiesIn M classFormula (snoc params z)) ∧
      (forall t : ZFSet.{u}, t ∈ M -> t ∈ domain ->
        forall y : ZFSet.{u}, y ∈ M ->
          SatisfiesIn M classFormula (snoc params y) ->
          SatisfiesIn M relationFormula (snoc (snoc params y) t) ->
          y ∈ domain) ∧
      forall candidate : ZFSet.{u}, candidate ∈ M ->
        x ∈ candidate ->
        (forall z : ZFSet.{u}, z ∈ M -> z ∈ candidate ->
          SatisfiesIn M classFormula (snoc params z)) ->
        (forall t : ZFSet.{u}, t ∈ M -> t ∈ candidate ->
          forall y : ZFSet.{u}, y ∈ M ->
            SatisfiesIn M classFormula (snoc params y) ->
            SatisfiesIn M relationFormula (snoc (snoc params y) t) ->
            y ∈ candidate) ->
        forall z : ZFSet.{u}, z ∈ M -> z ∈ domain -> z ∈ candidate := by
  rw [localDomainFormula]
  simp only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
    satisfiesIn_subsetClassFormulaAt_iff,
    satisfiesIn_downwardClosedFormulaAt_iff,
    satisfiesIn_all_iff, satisfiesIn_imp_iff,
    satisfiesIn_subsetFormulaAt_iff, snoc_last, snoc_castSucc]
  have hparams : (fun i => params i) = params := rfl
  simp only [hparams]
  constructor
  · rintro ⟨hxFormula, hxDomain, hsubset, hclosed, hleast⟩
    refine ⟨hxFormula, hxDomain, hsubset, hclosed, ?_⟩
    intro candidate hcandidateM hxCandidate hcandidateSubset
      hcandidateClosed
    exact hleast candidate hcandidateM
      ⟨hxCandidate, hcandidateSubset, hcandidateClosed⟩
  · rintro ⟨hxFormula, hxDomain, hsubset, hclosed, hleast⟩
    refine ⟨hxFormula, hxDomain, hsubset, hclosed, ?_⟩
    intro candidate hcandidateM hcandidate
    exact hleast candidate hcandidateM hcandidate.1
      hcandidate.2.1 hcandidate.2.2

/-- Insert the public local-domain formula into a larger variable context. -/
def localDomainFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases domain (fun j => Fin.lastCases x params j))
    (localDomainFormula classFormula relationFormula)

@[simp]
theorem satisfiesIn_localDomainFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (localDomainFormulaAt classFormula relationFormula params x domain) s <->
      SatisfiesIn M (localDomainFormula classFormula relationFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s domain)) := by
  rw [localDomainFormulaAt, satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s
        (Fin.lastCases domain (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s domain) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

/-! ## Agreement with the textbook `d_x` -/

/-- The actual textbook local domain is the least downward-closed subclass of
`A` containing its top point. -/
theorem localRecursionDomain_subset_of_closed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hxA : x ∈ A) {D : Set ZFSet.{u}} (hxD : x ∈ D)
    (hclosed : forall t, t ∈ D -> forall y,
      y ∈ A -> ClassRel R y t -> y ∈ D) :
    (localRecursionDomain A R hsetLike x : Set ZFSet.{u}) ⊆ D := by
  have hlayers : forall k,
      (predecessorLayer A R hsetLike x k : Set ZFSet.{u}) ⊆ D := by
    intro k
    induction k with
    | zero =>
        intro y hy
        have hySpec := (displayedPredecessors_spec hsetLike hxA y).mp hy
        exact hclosed x hxD y hySpec.1 hySpec.2
    | succ k ih =>
        intro y hy
        rcases (mem_predecessorLayer_succ_iff hsetLike hxA k).mp hy with
          ⟨t, htLayer, hyA, hyt⟩
        exact hclosed t (ih htLayer) y hyA hyt
  intro z hz
  rcases mem_localRecursionDomain_iff.mp hz with rfl | hzClosure
  · exact hxD
  · rcases mem_predecessorClosure_iff.mp hzClosure with ⟨k, hzk⟩
    exact hlayers k hzk

/-- Under the exact absoluteness and predecessor-closure assumptions from the
textbook, the least-closed-set formula denotes the already constructed
`d_x`.  Both the candidate and the actual `d_x` are explicitly required to
belong to `M`; this theorem does not claim either membership fact. -/
theorem satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params z) <->
        z ∈ A))
    (hrelationFormula : forall y, y ∈ M -> forall z, z ∈ M ->
      (SatisfiesIn (M : Set ZFSet.{u}) relationFormula
          (snoc (snoc params y) z) <-> ClassRel R y z))
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (M : Set ZFSet.{u}) A R)
    {x domain : ZFSet.{u}} (hxM : x ∈ M) (hxA : x ∈ A)
    (hdomainM : domain ∈ M)
    (hlocalM : localRecursionDomain A R hsetLike x ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (localDomainFormula classFormula relationFormula)
        (snoc (snoc params x) domain) <->
      domain = localRecursionDomain A R hsetLike x := by
  let dlocal := localRecursionDomain A R hsetLike x
  have hlocalSubsetA : (dlocal : Set ZFSet.{u}) ⊆ A :=
    localRecursionDomain_subset hsetLike hxA
  have hlocalClosed : forall t, t ∈ dlocal -> forall y,
      y ∈ A -> ClassRel R y t -> y ∈ dlocal := by
    intro t ht y _hyA hyt
    exact localRecursionDomain_predecessorClosed hrelation hsetLike hxA ht hyt
  constructor
  · intro hformula
    rcases (satisfiesIn_localDomainFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula params x domain).mp
        hformula with
      ⟨_hxFormula, hxDomain, hdomainSubset, hdomainClosed, hleast⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hzDomain
      have hzM : z ∈ M := htrans.mem_trans hzDomain hdomainM
      exact hleast dlocal hlocalM
        (mem_localRecursionDomain_iff.mpr (Or.inl rfl))
        (by
          intro w hwM hwLocal
          exact (hclass w hwM).mpr (hlocalSubsetA hwLocal))
        (by
          intro t htM htLocal y hyM hyFormula hyRelFormula
          have hyA : y ∈ A := (hclass y hyM).mp hyFormula
          have hyt : ClassRel R y t :=
            (hrelationFormula y hyM t htM).mp hyRelFormula
          exact hlocalClosed t htLocal y hyA hyt)
        z hzM hzDomain
    · intro hzLocal
      have hdomainSubsetA : (domain : Set ZFSet.{u}) ⊆ A := by
        intro w hwDomain
        have hwM : w ∈ M := htrans.mem_trans hwDomain hdomainM
        exact (hclass w hwM).mp (hdomainSubset w hwM hwDomain)
      have hdomainClosedAmbient : forall t, t ∈ domain -> forall y,
          y ∈ A -> ClassRel R y t -> y ∈ domain := by
        intro t htDomain y hyA hyt
        have htM : t ∈ M := htrans.mem_trans htDomain hdomainM
        have hyM : y ∈ M := hclosedIn t htM y hyA hyt
        exact hdomainClosed t htM htDomain y hyM
          ((hclass y hyM).mpr hyA)
          ((hrelationFormula y hyM t htM).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxDomain
        hdomainClosedAmbient hzLocal
  · intro hdomain
    subst domain
    apply (satisfiesIn_localDomainFormula_iff
      (M : Set ZFSet.{u}) classFormula relationFormula params x dlocal).mpr
    refine ⟨(hclass x hxM).mpr hxA,
      mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_, ?_, ?_⟩
    · intro z hzM hzLocal
      exact (hclass z hzM).mpr (hlocalSubsetA hzLocal)
    · intro t htM htLocal y hyM hyFormula hyRelFormula
      have hyA : y ∈ A := (hclass y hyM).mp hyFormula
      have hyt : ClassRel R y t :=
        (hrelationFormula y hyM t htM).mp hyRelFormula
      exact hlocalClosed t htLocal y hyA hyt
    · intro candidate hcandidateM hxCandidate hcandidateSubset
        hcandidateClosed z hzM hzLocal
      have hcandidateClosedAmbient : forall t, t ∈ candidate -> forall y,
          y ∈ A -> ClassRel R y t -> y ∈ candidate := by
        intro t htCandidate y hyA hyt
        have htM : t ∈ M := htrans.mem_trans htCandidate hcandidateM
        have hyM : y ∈ M := hclosedIn t htM y hyA hyt
        exact hcandidateClosed t htM htCandidate y hyM
          ((hclass y hyM).mpr hyA)
          ((hrelationFormula y hyM t htM).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxCandidate
        hcandidateClosedAmbient hzLocal

/-! ## Local solution graphs -/

/-- In the layout `(params,x,graph)`, assert that `graph` is a local solution
on the canonical domain of `x`.  The restriction graph supplied to the step
formula at `t` is quantified independently; the definition contains no
self-reference and makes no claim that a witness exists in a given model. -/
def localSolutionFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let graph : Fin (n + 2) := Fin.last (n + 1)
  let domain : Fin (n + 3) := Fin.last (n + 2)
  let top : Fin (n + 4) := Fin.last (n + 3)
  let restriction : Fin (n + 5) := Fin.last (n + 4)
  let value : Fin (n + 6) := Fin.last (n + 5)
  .ex <| .conj
    (localDomainFormulaAt classFormula relationFormula
      (fun i => (params i).castSucc) x.castSucc domain)
    (.conj
      (functionGraphOnFormulaAt graph.castSucc domain)
      (FOFormula.boundedAll domain <| .ex <| .ex <| .conj
        (restrictionGraphFormulaAt classFormula relationFormula
          (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
          graph.castSucc.castSucc.castSucc.castSucc
          top.castSucc.castSucc restriction.castSucc)
        (.conj
          (graphValueFormulaAt
            graph.castSucc.castSucc.castSucc.castSucc
            top.castSucc.castSucc value)
          (stepFormulaAt stepFormula
            (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
            top.castSucc.castSucc restriction.castSucc value))))

@[simp]
theorem satisfiesIn_localSolutionFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x graph : ZFSet.{u})
    (hparams : forall i, params i ∈ M) (hx : x ∈ M)
    (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) graph) <->
      exists domain : ZFSet.{u}, domain ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localDomainFormula classFormula relationFormula)
          (snoc (snoc params x) domain) ∧
        (((forall input : ZFSet.{u}, input ∈ M -> input ∈ domain ->
              exists value : ZFSet.{u}, value ∈ M ∧
                ZFSet.pair input value ∈ graph ∧
                forall other : ZFSet.{u}, other ∈ M ->
                  ZFSet.pair input other ∈ graph -> other = value) ∧
            forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ graph ->
              exists input : ZFSet.{u}, input ∈ M ∧ input ∈ domain ∧
                exists value : ZFSet.{u}, value ∈ M ∧
                  pair = ZFSet.pair input value) ∧
          forall top : ZFSet.{u}, top ∈ M -> top ∈ domain ->
            exists restriction : ZFSet.{u}, restriction ∈ M ∧
              exists value : ZFSet.{u}, value ∈ M ∧
                (forall pair : ZFSet.{u}, pair ∈ M ->
                  (pair ∈ restriction <->
                    pair ∈ graph ∧
                    exists input : ZFSet.{u}, input ∈ M ∧
                      exists output : ZFSet.{u}, output ∈ M ∧
                        pair = ZFSet.pair input output ∧
                        SatisfiesIn (M : Set ZFSet.{u}) classFormula
                          (snoc params input) ∧
                        SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                          (snoc (snoc params input) top))) ∧
                ZFSet.pair top value ∈ graph ∧
                SatisfiesIn (M : Set ZFSet.{u}) stepFormula
                  (snoc (snoc (snoc params top) restriction) value)) := by
  let s := snoc (snoc params x) graph
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hgraph
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hx
      · simpa [s] using hparams k
  change SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula) s <-> _
  rw [localSolutionFormula]
  constructor
  · rintro ⟨domain, hdomainM, hlocalRaw, hfunctionRaw, hstepsRaw⟩
    have hsDomain : forall i, snoc s domain i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hdomainM
      · simpa using hs j
    have hlocal := (satisfiesIn_localDomainFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula relationFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
      (snoc s domain)).mp hlocalRaw
    have hfunction := (satisfiesIn_functionGraphOnFormulaAt_iff hM
      (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
      (snoc s domain) hsDomain).mp hfunctionRaw
    refine ⟨domain, hdomainM, ?_, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hlocal
    · simpa only [s, snoc_last, snoc_castSucc] using hfunction
    · have hsteps := (satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u}) (Fin.last (n + 2)) _
        (snoc s domain)).mp hstepsRaw
      intro top htopM htopDomain
      have hstepRaw := hsteps top htopM (by simpa using htopDomain)
      rcases hstepRaw with
        ⟨restriction, hrestrictionM, value, hvalueM,
          hrestrictionRaw, hvalueRaw, hformulaRaw⟩
      let sFinal := snoc (snoc (snoc (snoc s domain) top)
        restriction) value
      have hsFinal : forall i, sFinal i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [sFinal] using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [sFinal] using hrestrictionM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa [sFinal] using htopM
            · refine Fin.lastCases ?_ (fun a => ?_) l
              · simpa [sFinal] using hdomainM
              · simpa [sFinal] using hs a
      have hrestriction :=
        (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
          relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc sFinal hsFinal).mp hrestrictionRaw
      have hvalue := (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
        (Fin.last (n + 3)).castSucc.castSucc (Fin.last (n + 5))
        sFinal hsFinal).mp hvalueRaw
      have hformula := (satisfiesIn_stepFormulaAt_iff
        (M : Set ZFSet.{u}) stepFormula
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 3)).castSucc.castSucc
        (Fin.last (n + 4)).castSucc (Fin.last (n + 5)) sFinal).mp
          hformulaRaw
      refine ⟨restriction, hrestrictionM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hrestriction
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hvalue
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hformula
  · rintro ⟨domain, hdomainM, hlocal, hfunction, hsteps⟩
    have hsDomain : forall i, snoc s domain i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hdomainM
      · simpa using hs j
    refine ⟨domain, hdomainM, ?_, ?_, ?_⟩
    · apply (satisfiesIn_localDomainFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
        (snoc s domain)).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hlocal
    · apply (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (snoc s domain) hsDomain).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hfunction
    · apply (satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u}) (Fin.last (n + 2)) _
        (snoc s domain)).mpr
      intro top htopM htopDomain
      rcases hsteps top htopM (by simpa using htopDomain) with
        ⟨restriction, hrestrictionM, value, hvalueM,
          hrestriction, hvalue, hformula⟩
      let sFinal := snoc (snoc (snoc (snoc s domain) top)
        restriction) value
      have hsFinal : forall i, sFinal i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [sFinal] using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [sFinal] using hrestrictionM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa [sFinal] using htopM
            · refine Fin.lastCases ?_ (fun a => ?_) l
              · simpa [sFinal] using hdomainM
              · simpa [sFinal] using hs a
      refine ⟨restriction, hrestrictionM, value, hvalueM, ?_, ?_, ?_⟩
      · apply (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
          relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc sFinal hsFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hrestriction
      · apply (satisfiesIn_graphValueFormulaAt_iff hM
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc (Fin.last (n + 5))
          sFinal hsFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hvalue
      · apply (satisfiesIn_stepFormulaAt_iff
          (M : Set ZFSet.{u}) stepFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)) sFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hformula

/-- Insert the public local-solution formula into a larger context. -/
def localSolutionFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases graph (fun j => Fin.lastCases x params j))
    (localSolutionFormula classFormula relationFormula stepFormula)

@[simp]
theorem satisfiesIn_localSolutionFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (localSolutionFormulaAt classFormula relationFormula stepFormula
          params x graph) s <->
      SatisfiesIn M
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s graph)) := by
  rw [localSolutionFormulaAt, satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s
        (Fin.lastCases graph (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s graph) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

/-! ## The value relation defined by local recursion -/

/-- In the layout `(params,x,value)`, assert that `x` belongs to the formula
class and some model-internal local solution graph takes `x` to `value`.
This is a non-self-referential first-order formula; existence of such a graph
is not part of the definition. -/
def recursionValueFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let value : Fin (n + 2) := Fin.last (n + 1)
  .conj
    (classFormulaAt classFormula params x)
    (.ex <| .conj
      (localSolutionFormulaAt classFormula relationFormula stepFormula
        (fun i => (params i).castSucc) x.castSucc (Fin.last (n + 2)))
      (graphValueFormulaAt
        (Fin.last (n + 2)) x.castSucc value.castSucc))

@[simp]
theorem satisfiesIn_recursionValueFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x value : ZFSet.{u})
    (hparams : forall i, params i ∈ M) (hx : x ∈ M)
    (hvalue : value ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (recursionValueFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) value) <->
      SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params x) ∧
      exists graph : ZFSet.{u}, graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params x) graph) ∧
        ZFSet.pair x value ∈ graph := by
  let s := snoc (snoc params x) value
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hvalue
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hx
      · simpa [s] using hparams k
  change SatisfiesIn (M : Set ZFSet.{u})
      (recursionValueFormula classFormula relationFormula stepFormula) s <-> _
  rw [recursionValueFormula]
  constructor
  · rintro ⟨hclassRaw, graph, hgraphM, hsolutionRaw, hpairRaw⟩
    have hclass := (satisfiesIn_classFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula
      (fun i => i.castSucc.castSucc) (Fin.last n).castSucc s).mp hclassRaw
    have hsolution := (satisfiesIn_localSolutionFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
      (snoc s graph)).mp hsolutionRaw
    have hsGraph : forall i, snoc s graph i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hgraphM
      · simpa using hs j
    have hpair := (satisfiesIn_graphValueFormulaAt_iff hM
      (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc (snoc s graph) hsGraph).mp hpairRaw
    refine ⟨?_, graph, hgraphM, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hclass
    · simpa only [s, snoc_last, snoc_castSucc] using hsolution
    · simpa only [s, snoc_last, snoc_castSucc] using hpair
  · rintro ⟨hclass, graph, hgraphM, hsolution, hpair⟩
    have hsGraph : forall i, snoc s graph i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hgraphM
      · simpa using hs j
    refine ⟨?_, graph, hgraphM, ?_, ?_⟩
    · apply (satisfiesIn_classFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula
        (fun i => i.castSucc.castSucc) (Fin.last n).castSucc s).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hclass
    · apply (satisfiesIn_localSolutionFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
        (snoc s graph)).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hsolution
    · apply (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc
        (Fin.last (n + 1)).castSucc (snoc s graph) hsGraph).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hpair

end

end Constructible.Model
