/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.Absoluteness
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalLiterals

/-!
# Absolute lookup in an arbitrary set-coded graph

For a set `graph` and a key `key`, `uniqueGraphLookupZF graph key` returns the
unique `value` whose Kuratowski pair `<key,value>` belongs to `graph`.  If
there is no such unique value, it returns the empty set.  This is a genuinely
total metatheoretic operation: `Classical.choose` is used only after the
existence-and-uniqueness proposition has been established, and is not used to
assert that an arbitrary relation is functional.

The graph formula has free-variable layout `[graph,key,output]`.  Its success
branch says that `output` is a graph value at `key` and is the only such
value.  Its failure branch says that no unique graph value exists and that
`output` is empty.  The formula uses only membership, equality, logical
connectives, and quantifiers.

The main point in the restricted-semantics proof is not assumed: if `graph`
belongs to a transitive model and `<key,value>` belongs to `graph`, then the
Kuratowski pair and hence its right coordinate `value` belong to the model.
Thus model-internal and ambient existence-and-uniqueness agree even when
`graph` is not a function.
-/

@[expose] public section

open Set

universe u

namespace Constructible

noncomputable section

/-- `value` is the unique value occurring at `key` in the arbitrary
Kuratowski-pair relation `graph`. -/
def IsUniqueGraphValue (graph key value : ZFSet.{u}) : Prop :=
  ZFSet.pair key value ∈ graph ∧
    ∀ other : ZFSet.{u}, ZFSet.pair key other ∈ graph → other = value

/-- The unique value at `key`, totalized by the empty set when the relation
does not have exactly one value there.  Choice is only metatheoretic here. -/
noncomputable def uniqueGraphLookupZF
    (graph key : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph then
      Classical.choose h
    else
      ∅

theorem existsUnique_graphValue_iff
    {graph key : ZFSet.{u}} :
    (∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph) ↔
      ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value := by
  rfl

/-- A displayed value with the required uniqueness is the total lookup. -/
theorem uniqueGraphLookupZF_eq_of_unique
    {graph key value : ZFSet.{u}}
    (hvalue : ZFSet.pair key value ∈ graph)
    (hunique : ∀ other : ZFSet.{u},
      ZFSet.pair key other ∈ graph → other = value) :
    uniqueGraphLookupZF graph key = value := by
  let h : ∃! other : ZFSet.{u}, ZFSet.pair key other ∈ graph :=
    ⟨value, hvalue, hunique⟩
  rw [uniqueGraphLookupZF, dif_pos h]
  exact ((Classical.choose_spec h).2 value hvalue).symm

/-- In the non-unique case the total lookup is exactly the empty set. -/
theorem uniqueGraphLookupZF_eq_empty_of_not_unique
    {graph key : ZFSet.{u}}
    (h : ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph) :
    uniqueGraphLookupZF graph key = (∅ : ZFSet.{u}) := by
  simp only [uniqueGraphLookupZF, dif_neg h]

/-- For a genuine `ZFSet.IsFunc`, lookup agrees with every displayed graph
value at a key in the function's domain. -/
theorem uniqueGraphLookupZF_eq_of_isFunc
    {domain codomain graph key value : ZFSet.{u}}
    (hfunc : ZFSet.IsFunc domain codomain graph)
    (hkey : key ∈ domain)
    (hvalue : ZFSet.pair key value ∈ graph) :
    uniqueGraphLookupZF graph key = value := by
  rcases hfunc.2 key hkey with ⟨canonical, hcanonical, hunique⟩
  apply uniqueGraphLookupZF_eq_of_unique hvalue
  intro other hother
  exact (hunique other hother).trans (hunique value hvalue).symm

/-- At a key in the domain of a genuine set-coded function, lookup itself is
represented by a pair in the graph. -/
theorem pair_uniqueGraphLookupZF_mem_of_isFunc
    {domain codomain graph key : ZFSet.{u}}
    (hfunc : ZFSet.IsFunc domain codomain graph)
    (hkey : key ∈ domain) :
    ZFSet.pair key (uniqueGraphLookupZF graph key) ∈ graph := by
  rcases hfunc.2 key hkey with ⟨value, hvalue, hunique⟩
  rw [uniqueGraphLookupZF_eq_of_unique hvalue hunique]
  exact hvalue

namespace TextbookDefFormula

/-- The output coordinate is a graph value at the key and every other graph
value at that key is equal to it. -/
def uniqueGraphValueAt {n : Nat}
    (graph key output : Fin n) : FOFormula n :=
  .conj
    (graphValueAt graph key output)
    (.all <| .imp
      (graphValueAt graph.castSucc key.castSucc (Fin.last n))
      (.eq (Fin.last n) output.castSucc))

/-- There exists a unique graph value at the designated key. -/
def hasUniqueGraphValueAt {n : Nat}
    (graph key : Fin n) : FOFormula n :=
  .ex (uniqueGraphValueAt graph.castSucc key.castSucc (Fin.last n))

/-- Total graph-lookup formula with layout `[graph,key,output]`. -/
def uniqueGraphLookupFormula : FOFormula 3 :=
  .disj
    (uniqueGraphValueAt (0 : Fin 3) (1 : Fin 3) (2 : Fin 3))
    (.conj
      (.neg (hasUniqueGraphValueAt (0 : Fin 3) (1 : Fin 3)))
      (Delta0Formula.emptyDeltaAt (2 : Fin 3)).toFO)

@[simp]
theorem satisfies_uniqueGraphValueAt {n : Nat}
    (graph key output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (uniqueGraphValueAt graph key output) s ↔
      IsUniqueGraphValue (s graph) (s key) (s output) := by
  simp only [uniqueGraphValueAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphValueAt, snoc_last, snoc_castSucc,
    IsUniqueGraphValue]

@[simp]
theorem satisfies_hasUniqueGraphValueAt {n : Nat}
    (graph key : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (hasUniqueGraphValueAt graph key) s ↔
      ∃ value : ZFSet.{u}, IsUniqueGraphValue (s graph) (s key) value := by
  simp only [hasUniqueGraphValueAt, FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt, snoc_last, snoc_castSucc]

theorem satisfies_uniqueGraphLookupFormula_components
    (graph key output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueGraphLookupFormula
        ![graph, key, output] ↔
      IsUniqueGraphValue graph key output ∨
        ((¬ ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value) ∧
          output = (∅ : ZFSet.{u})) := by
  simp only [uniqueGraphLookupFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_uniqueGraphValueAt,
    satisfies_hasUniqueGraphValueAt, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_emptyDeltaAt]
  rfl

/-- Exact ambient semantics of the total graph-lookup formula. -/
@[simp]
theorem satisfies_uniqueGraphLookupFormula_iff
    (graph key output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueGraphLookupFormula
        ![graph, key, output] ↔
      output = uniqueGraphLookupZF graph key := by
  rw [satisfies_uniqueGraphLookupFormula_components]
  constructor
  · rintro (houtput | ⟨hnot, hempty⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        houtput.1 houtput.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hempty, uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro houtput
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookup := uniqueGraphLookupZF_eq_of_unique hvalue hunique
      rw [houtput, hlookup]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← existsUnique_graphValue_iff] using hunique
      · rw [houtput,
          uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

end TextbookDefFormula

namespace Model

/-- A graph value belongs to any transitive set containing the graph.  No
functionality assumption on `graph` is used. -/
theorem graphValue_mem_of_transitive
    {M graph key value : ZFSet.{u}} (hM : M.IsTransitive)
    (hgraph : graph ∈ M)
    (hvalue : ZFSet.pair key value ∈ graph) :
    value ∈ M := by
  have hpairM : ZFSet.pair key value ∈ M :=
    hM.mem_trans hvalue hgraph
  have hcoordinatesM : ({key, value} : ZFSet.{u}) ∈ M :=
    hM.mem_trans (by simp [ZFSet.pair]) hpairM
  exact hM.mem_trans (by simp) hcoordinatesM

private theorem satisfiesIn_lookupAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_lookupImp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s ↔
      (SatisfiesIn M left s → SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

private theorem satisfiesIn_lookupDisj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

theorem satisfiesIn_textbookGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key value : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.graphValueAt graph key value) s ↔
      ZFSet.pair (s key) (s value) ∈ s graph := by
  rw [TextbookDefFormula.graphValueAt,
    satisfiesIn_delta0_iff hM
      (TextbookDefFormula.graphValueDeltaAt graph key value) s hs,
    Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_graphValueDeltaAt]

/-- Restricted semantics of unique graph values is ambient semantics.  The
unbounded uniqueness quantifier causes no loss, because every competing graph
value is forced into the transitive carrier by pair membership. -/
theorem satisfiesIn_uniqueGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key output : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.uniqueGraphValueAt graph key output) s ↔
      IsUniqueGraphValue (s graph) (s key) (s output) := by
  rw [TextbookDefFormula.uniqueGraphValueAt]
  simp only [SatisfiesIn, satisfiesIn_lookupAll_iff,
    satisfiesIn_lookupImp_iff]
  constructor
  · rintro ⟨hvalueFormula, huniqueFormula⟩
    have hvalue := (satisfiesIn_textbookGraphValueAt_iff hM
      graph key output s hs).mp hvalueFormula
    refine ⟨hvalue, ?_⟩
    intro other hother
    have hotherM : other ∈ M :=
      graphValue_mem_of_transitive hM (hs graph) hother
    have hsOther : ∀ i, snoc s other i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hotherM
      · simpa using hs j
    have hotherFormula :
        SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.graphValueAt
            graph.castSucc key.castSucc (Fin.last n))
          (snoc s other) := by
      apply (satisfiesIn_textbookGraphValueAt_iff hM
        graph.castSucc key.castSucc (Fin.last n)
        (snoc s other) hsOther).mpr
      simpa only [snoc_last, snoc_castSucc] using hother
    have heq := huniqueFormula other hotherM hotherFormula
    simpa only [SatisfiesIn, snoc_last, snoc_castSucc] using heq
  · rintro ⟨hvalue, hunique⟩
    constructor
    · exact (satisfiesIn_textbookGraphValueAt_iff hM
        graph key output s hs).mpr hvalue
    · intro other hotherM hotherFormula
      have hsOther : ∀ i, snoc s other i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hotherM
        · simpa using hs j
      have hother := (satisfiesIn_textbookGraphValueAt_iff hM
        graph.castSucc key.castSucc (Fin.last n)
        (snoc s other) hsOther).mp hotherFormula
      have heq : other = s output :=
        hunique other (by simpa only [snoc_last, snoc_castSucc] using hother)
      simpa only [SatisfiesIn, snoc_last, snoc_castSucc] using heq

theorem satisfiesIn_hasUniqueGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.hasUniqueGraphValueAt graph key) s ↔
      ∃ value : ZFSet.{u},
        IsUniqueGraphValue (s graph) (s key) value := by
  rw [TextbookDefFormula.hasUniqueGraphValueAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨value, hvalueM, hvalueFormula⟩
    refine ⟨value, ?_⟩
    simpa only [snoc_last, snoc_castSucc] using
      (satisfiesIn_uniqueGraphValueAt_iff hM
      graph.castSucc key.castSucc (Fin.last n)
      (snoc s value) (by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · simpa using hs j)).mp hvalueFormula
  · rintro ⟨value, hvalue⟩
    have hvalueM : value ∈ M :=
      graphValue_mem_of_transitive hM (hs graph) hvalue.1
    refine ⟨value, hvalueM, ?_⟩
    apply (satisfiesIn_uniqueGraphValueAt_iff hM
      graph.castSucc key.castSucc (Fin.last n)
      (snoc s value) (by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · simpa using hs j)).mpr
    simpa only [snoc_last, snoc_castSucc] using hvalue

/-- Exact restricted semantics of total lookup. -/
theorem satisfiesIn_uniqueGraphLookupFormula_iff
    {M graph key output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hgraph : graph ∈ M) (hkey : key ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.uniqueGraphLookupFormula
        ![graph, key, output] ↔
      output = uniqueGraphLookupZF graph key := by
  have hs : ∀ i : Fin 3, ![graph, key, output] i ∈ M := by
    intro i
    fin_cases i
    · exact hgraph
    · exact hkey
    · exact houtput
  rw [TextbookDefFormula.uniqueGraphLookupFormula]
  have hsuccess := satisfiesIn_uniqueGraphValueAt_iff hM.1
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    ![graph, key, output] hs
  have hexists := satisfiesIn_hasUniqueGraphValueAt_iff hM.1
    (0 : Fin 3) (1 : Fin 3) ![graph, key, output] hs
  have hempty := satisfiesIn_delta0_iff hM.1
    (Delta0Formula.emptyDeltaAt (2 : Fin 3))
    ![graph, key, output] hs
  have hsuccess' :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.uniqueGraphValueAt
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3))
          ![graph, key, output] ↔
        IsUniqueGraphValue graph key output := by
    simpa using hsuccess
  have hexists' :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.hasUniqueGraphValueAt
            (0 : Fin 3) (1 : Fin 3))
          ![graph, key, output] ↔
        ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value := by
    simpa using hexists
  have hempty' :
      SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.emptyDeltaAt (2 : Fin 3)).toFO
          ![graph, key, output] ↔ output = (∅ : ZFSet.{u}) := by
    rw [hempty, Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_emptyDeltaAt]
    rfl
  rw [satisfiesIn_lookupDisj_iff]
  simp only [SatisfiesIn]
  rw [hsuccess', hexists', hempty']
  constructor
  · rintro (hvalue | ⟨hnot, hzero⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        hvalue.1 hvalue.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hzero, uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro hlookup
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookupValue := uniqueGraphLookupZF_eq_of_unique hvalue hunique
      rw [hlookup, hlookupValue]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← existsUnique_graphValue_iff] using hunique
      · rw [hlookup,
          uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

/-- The total lookup is closed in every transitive ZF model on model
arguments. -/
theorem uniqueGraphLookupZF_mem_of_isTransitiveZFModel
    {M graph key : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hgraph : graph ∈ M) (_hkey : key ∈ M) :
    uniqueGraphLookupZF graph key ∈ M := by
  by_cases hunique :
      ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
  · rcases hunique with ⟨value, hvalue, hunique⟩
    rw [uniqueGraphLookupZF_eq_of_unique hvalue hunique]
    exact graphValue_mem_of_transitive hM.1 hgraph hvalue
  · rw [uniqueGraphLookupZF_eq_empty_of_not_unique hunique]
    exact empty_mem_of_isTransitiveZFModel hM

/-- Standard absoluteness package for the total binary lookup operation. -/
theorem uniqueGraphLookupZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) Set.univ
      (fun s : Tuple ZFSet.{u} 2 =>
        uniqueGraphLookupZF (s 0) (s 1))
      TextbookDefFormula.uniqueGraphLookupFormula := by
  constructor
  · intro s hs _hdomain
    exact uniqueGraphLookupZF_mem_of_isTransitiveZFModel
      hM (hs 0) (hs 1)
  · intro s output hs houtput
    have hassign : snoc s output = ![s 0, s 1, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa using
      (satisfiesIn_uniqueGraphLookupFormula_iff hM
        (hs 0) (hs 1) houtput)

end Model

end

end Constructible
