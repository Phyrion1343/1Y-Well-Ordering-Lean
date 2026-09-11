/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookAtomicAbsolute

/-!
# Absoluteness of the textbook existential projection

This file gives a first-order graph for the total set-coded operation
`textbookExistsProjCodeZF`.  The finite-arity and nonempty-arity conditions
are part of the member condition.  In particular, the graph defines the
empty output at arity zero, exactly as in the textbook definition.

The formula describing an extended tuple graph is genuinely bounded: it
says that the extended graph is obtained by adjoining the Kuratowski pair
`<arity, value>` to the original graph.  Closure of the projection output is
then obtained by Separation from the already internalized finite tuple
space; no ambient powerset is identified with an internal powerset.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookDefFormula

/-! ## A bounded formula for adjoining the final graph entry -/

/--
`extended` is exactly `insert (pair arity value) graph`.

The three conjuncts respectively give the upper inclusion, inclusion of the
old graph, and membership of the newly adjoined pair.  Every quantifier is
bounded by either `extended` or `graph`.
-/
def insertPairEqDeltaAt {n : Nat}
    (extended graph arity value : Fin n) : Delta0Formula n :=
  .conj
    (Delta0Formula.boundedAll extended
      (.disj
        (.mem (Fin.last n) graph.castSucc)
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n) arity.castSucc value.castSucc)))
    (.conj
      (Delta0Formula.boundedAll graph
        (.mem (Fin.last n) extended.castSucc))
      (Delta0Formula.boundedEx extended
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n) arity.castSucc value.castSucc)))

@[simp]
theorem satisfies_insertPairEqDeltaAt {n : Nat}
    (extended graph arity value : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (insertPairEqDeltaAt extended graph arity value) s ↔
      s extended = insert (ZFSet.pair (s arity) (s value)) (s graph) := by
  simp only [insertPairEqDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll,
    Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hupper, hlower, pairWitness, hpairMem, hpairWitness⟩
    have hnew : ZFSet.pair (s arity) (s value) ∈ s extended := by
      rwa [hpairWitness] at hpairMem
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases hupper z hz with hzGraph | hzPair
      · exact Or.inr hzGraph
      · exact Or.inl hzPair
    · rintro (rfl | hzGraph)
      · exact hnew
      · exact hlower z hzGraph
  · intro hextended
    constructor
    · intro z hz
      change z ∈ s extended at hz
      rw [hextended, ZFSet.mem_insert_iff] at hz
      rcases hz with hzPair | hzGraph
      · exact Or.inr hzPair
      · exact Or.inl hzGraph
    · constructor
      · intro z hz
        change z ∈ s graph at hz
        change z ∈ s extended
        rw [hextended, ZFSet.mem_insert_iff]
        exact Or.inr hz
      · refine ⟨ZFSet.pair (s arity) (s value), ?_, rfl⟩
        change ZFSet.pair (s arity) (s value) ∈ s extended
        rw [hextended, ZFSet.mem_insert_iff]
        exact Or.inl rfl

/-- Layout `[extended, graph, arity, value]`. -/
def insertPairEqDelta : Delta0Formula 4 :=
  insertPairEqDeltaAt
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

@[simp]
theorem satisfies_insertPairEqDelta
    (extended graph arity value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem insertPairEqDelta
        ![extended, graph, arity, value] ↔
      extended = insert (ZFSet.pair arity value) graph := by
  simp [insertPairEqDelta]

/-! ## The bounded projection-member predicate -/

/--
A graph is an `arity`-tuple over `a`, `arity` is nonempty, and adjoining one
last value from `a` gives a graph in `relation`.  Standard finiteness is a
separate first-order guard below, since membership in the standard omega is
not Delta-zero without an omega parameter.
-/
def existsProjMemberDeltaAt {n : Nat}
    (a arity relation graph : Fin n) : Delta0Formula n :=
  .conj
    (Delta0Formula.boundedEx arity
      (.eq (Fin.last n) (Fin.last n)))
    (.conj
      (isFunctionDeltaAt graph arity a)
      (Delta0Formula.boundedEx a
        (Delta0Formula.boundedEx relation.castSucc
          (insertPairEqDeltaAt
            (Fin.last (n + 1))
            graph.castSucc.castSucc
            arity.castSucc.castSucc
            (Fin.last n).castSucc))))

@[simp]
theorem satisfies_existsProjMemberDeltaAt {n : Nat}
    (a arity relation graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (existsProjMemberDeltaAt a arity relation graph) s ↔
      (∃ index : ZFSet.{u}, index ∈ s arity) ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ value ∈ s a,
            insert (ZFSet.pair (s arity) value) (s graph) ∈ s relation := by
  simp [existsProjMemberDeltaAt]

/-- Layout `[a, arity, relation, graph]`. -/
def existsProjMemberDelta : Delta0Formula 4 :=
  existsProjMemberDeltaAt
    (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

@[simp]
theorem satisfies_existsProjMemberDelta
    (a arity relation graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem existsProjMemberDelta
        ![a, arity, relation, graph] ↔
      (∃ index : ZFSet.{u}, index ∈ arity) ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ value ∈ a,
            insert (ZFSet.pair arity value) graph ∈ relation := by
  simp [existsProjMemberDelta]

/-! ## Guarded extensional graph of the total operation -/

/--
Layout `[a, arity, relation, output, graph]`; `output` is unused.  The first
conjunct says that `arity` is a standard finite ordinal.  Nonemptiness remains
explicit in `existsProjMemberDeltaAt`, so arity zero has no members.
-/
def existsProjOutputMemberCondition : FOFormula 5 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 5))
    (existsProjMemberDeltaAt
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)).toFO

/-- Layout `[a, arity, relation, output]`. -/
def existsProjOutputFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      existsProjOutputMemberCondition)

end TextbookDefFormula

/-! ## Exact ambient membership of the totalized operation -/

private theorem exists_mem_natCode_iff (n : Nat) :
    (∃ index : ZFSet.{u}, index ∈ natCode n) ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst n
    rcases h with ⟨index, hindex⟩
    simp [natCode] at hindex
  · intro hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
        exact ⟨natCode n,
          (natCode_mem_natCode_iff n (n + 1)).mpr (Nat.lt_succ_self n)⟩

@[simp]
theorem mem_textbookExistsProjCodeZF_iff
    {a arity relation graph : ZFSet.{u}} :
    graph ∈ textbookExistsProjCodeZF a arity relation ↔
      (∃ n : Nat, arity = natCode n) ∧
        (∃ index : ZFSet.{u}, index ∈ arity) ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ value ∈ a,
              insert (ZFSet.pair arity value) graph ∈ relation := by
  constructor
  · intro hgraph
    unfold textbookExistsProjCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        have harityEq : arity = natCode n :=
          textbookNatDecode_eq_some_iff.mp harity
        subst arity
        simp only [harity] at hgraph
        have hn : n ≠ 0 := by
          intro hn
          subst n
          rw [textbookExistsProjZF_zero] at hgraph
          exact ZFSet.notMem_empty graph hgraph
        rcases (mem_textbookExistsProjZF_iff hn).mp hgraph with
          ⟨hspace, value, hvalue, hextended⟩
        exact ⟨⟨n, rfl⟩, (exists_mem_natCode_iff n).2 hn,
          mem_textbookTupleSpace_iff.mp hspace,
          value, hvalue, by
            simpa only [textbookTupleSnocGraph] using hextended⟩
  · rintro ⟨⟨n, rfl⟩, hnonempty, hfunc,
      value, hvalue, hextended⟩
    have hn : n ≠ 0 := (exists_mem_natCode_iff n).1 hnonempty
    rw [textbookExistsProjCodeZF_natCode,
      mem_textbookExistsProjZF_iff hn]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      value, hvalue, by
        simpa only [textbookTupleSnocGraph] using hextended⟩

namespace Model

noncomputable section

private theorem satisfiesIn_projectionAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_projectionBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Restricted semantics of the bounded member predicate -/

theorem satisfiesIn_existsProjMemberDelta_iff
    {M a arity relation graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjMemberDelta.toFO
        ![a, arity, relation, graph] ↔
      (∃ index : ZFSet.{u}, index ∈ arity) ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ value ∈ a,
            insert (ZFSet.pair arity value) graph ∈ relation := by
  have hs : ∀ i : Fin 4, ![a, arity, relation, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hrelation
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM
    TextbookDefFormula.existsProjMemberDelta
    ![a, arity, relation, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_existsProjMemberDelta
      a arity relation graph)

theorem satisfiesIn_existsProjOutputMemberCondition_iff
    {M a arity relation output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M)
    (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph] ↔
      graph ∈ textbookExistsProjCodeZF a arity relation := by
  rw [TextbookDefFormula.existsProjOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 5,
      ![a, arity, relation, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hrelation
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 5) ![a, arity, relation, output, graph] hs]
  have hdelta := satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.existsProjMemberDeltaAt
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4))
    ![a, arity, relation, output, graph] hs
  rw [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_existsProjMemberDeltaAt] at hdelta
  rw [hdelta]
  exact mem_textbookExistsProjCodeZF_iff.symm

/-! ## Closure under the standard and total projections -/

theorem textbookExistsProjZF_mem_of_isTransitiveZFModel
    {M a relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (n : Nat) :
    textbookExistsProjZF a n relation ∈ M := by
  by_cases hn : n = 0
  · subst n
    simp only [textbookExistsProjZF_zero]
    exact empty_mem_of_isTransitiveZFModel hM
  · have hnM : (natCode n : ZFSet.{u}) ∈ M :=
      natOrdinal_mem_of_isTransitiveZFModel hM n
    have hspaceM : textbookTupleSpace a n ∈ M :=
      textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
    let params : Tuple (ZFCarrier M) 3 :=
      ![⟨a, ha⟩, ⟨natCode n, hnM⟩, ⟨relation, hrelation⟩]
    let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
    have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
      TextbookDefFormula.existsProjMemberDelta.toFO params space
    have hassign (graph : ZFSet.{u}) :
        snoc (zfCarrierTupleVal params) graph =
          ![a, natCode n, relation, graph] := by
      funext i
      fin_cases i <;> rfl
    have hsepEq :
        (space.1.sep fun graph =>
          SatisfiesIn (M : Set ZFSet.{u})
            TextbookDefFormula.existsProjMemberDelta.toFO
            (snoc (zfCarrierTupleVal params) graph)) =
          textbookExistsProjZF a n relation := by
      apply ZFSet.ext
      intro graph
      rw [ZFSet.mem_sep, mem_textbookExistsProjZF_iff hn]
      constructor
      · rintro ⟨hgraphSpace, hformula⟩
        have hgraphM : graph ∈ M :=
          hM.1.mem_trans hgraphSpace hspaceM
        rw [hassign graph] at hformula
        rcases (satisfiesIn_existsProjMemberDelta_iff
            hM.1 ha hnM hrelation hgraphM).mp hformula with
          ⟨_hnonempty, _hfunc, value, hvalue, hextendedRelation⟩
        refine ⟨hgraphSpace, value, hvalue, ?_⟩
        simpa only [textbookTupleSnocGraph] using hextendedRelation
      · rintro ⟨hgraphSpace, value, hvalue, hextendedRelation⟩
        have hgraphM : graph ∈ M :=
          hM.1.mem_trans hgraphSpace hspaceM
        have hfunc : ZFSet.IsFunc (natCode n) a graph :=
          mem_textbookTupleSpace_iff.mp hgraphSpace
        refine ⟨hgraphSpace, ?_⟩
        rw [hassign graph]
        apply (satisfiesIn_existsProjMemberDelta_iff
          hM.1 ha hnM hrelation hgraphM).mpr
        refine ⟨(exists_mem_natCode_iff n).2 hn, hfunc,
          value, hvalue, ?_⟩
        simpa only [textbookTupleSnocGraph] using hextendedRelation
    rw [hsepEq] at hsep
    exact hsep

theorem textbookExistsProjCodeZF_mem_of_isTransitiveZFModel
    {M a relation : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (hrelation : relation ∈ M) (arity : ZFSet.{u}) :
    textbookExistsProjCodeZF a arity relation ∈ M := by
  unfold textbookExistsProjCodeZF
  cases harity : textbookNatDecode arity with
  | none => exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      exact textbookExistsProjZF_mem_of_isTransitiveZFModel
        hM ha hrelation n

/-! ## Exact restricted semantics of the output formula -/

theorem satisfiesIn_existsProjOutputFormula_components
    {M a arity relation output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputFormula
        ![a, arity, relation, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookExistsProjCodeZF a arity relation) := by
  rw [TextbookDefFormula.existsProjOutputFormula,
    satisfiesIn_projectionAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, relation, output] graph =
        ![a, arity, relation, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_projectionBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      TextbookDefFormula.existsProjOutputMemberCondition
      (snoc ![a, arity, relation, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_existsProjOutputMemberCondition_iff hM
        ha harity hrelation houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_projectionBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 4) (3 : Fin 4).castSucc)
      TextbookDefFormula.existsProjOutputMemberCondition
      (snoc ![a, arity, relation, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, arity, relation, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_existsProjOutputMemberCondition_iff hM
        ha harity hrelation houtput hgraph).symm

theorem satisfiesIn_existsProjOutputFormula_iff
    {M a arity relation output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hrelation : relation ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.existsProjOutputFormula
        ![a, arity, relation, output] ↔
      output = textbookExistsProjCodeZF a arity relation := by
  rw [satisfiesIn_existsProjOutputFormula_components hM
    ha harity hrelation houtput]
  have hcode : textbookExistsProjCodeZF a arity relation ∈ M :=
    textbookExistsProjCodeZF_mem_of_isTransitiveZFModel
      hM ha hrelation arity
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph houtput)).mp hgraph
    · intro hgraph
      exact (h graph (hM.1.mem_trans hgraph hcode)).mpr hgraph
  · intro h graph _hgraph
    rw [h]

/-! ## Standard `FunctionAbsoluteTo` package -/

/-- Existential projection is total on its three set-valued inputs. -/
theorem textbookExistsProjCodeZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u}) Set.univ
      (fun s : Tuple ZFSet.{u} 3 =>
        textbookExistsProjCodeZF (s 0) (s 1) (s 2))
      TextbookDefFormula.existsProjOutputFormula := by
  constructor
  · intro s hs _hsDomain
    exact textbookExistsProjCodeZF_mem_of_isTransitiveZFModel
      hM (hs 0) (hs 2) (s 1)
  · intro s output hs houtput
    have hassign : snoc s output =
        ![s 0, s 1, s 2, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa using
      (satisfiesIn_existsProjOutputFormula_iff hM
        (hs 0) (hs 1) (hs 2) houtput)

end

end Model

end Constructible
