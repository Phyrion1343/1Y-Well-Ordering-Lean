/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalLiterals
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookTupleSpaceAbsolute
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDefinabilityCode

/-!
# The set-theoretic graph of addition on the standard natural numbers

This file defines addition without adding an arithmetic symbol to the
language of set theory.  The formula says that a finite function graph starts
at `x`, is closed under von Neumann successor along the indices below `y`,
and has value `z` at `y`.  Its free-variable layout is `[omega, x, y, z]`.

The use of Lean's `Nat.add` below is confined to the canonical witness and to
the metatheoretic statement of the semantics.  The defining formula itself
uses only equality and membership.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

/-! ## The bounded finite-recursion body -/

/--
The transition clause for a graph with layout
`[omega, x, y, z, ySucc, graph]`.

For every `k ∈ y`, it chooses `kSucc = k ∪ {k}` and graph values at `k`
and `kSucc`, and requires the latter value to be the successor of the former.
-/
def natAddTransitionDeltaAt {n : Nat}
    (omega y ySucc graph : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedAll y
    (Delta0Formula.boundedEx ySucc.castSucc
      (.conj
        (Delta0Formula.successorAt
          (Fin.last (n + 1)) (Fin.last n).castSucc)
        (Delta0Formula.boundedEx omega.castSucc.castSucc
          (.conj
            (TextbookDefFormula.graphValueDeltaAt
              graph.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2)))
            (Delta0Formula.boundedEx omega.castSucc.castSucc.castSucc
              (.conj
                (TextbookDefFormula.graphValueDeltaAt
                  graph.castSucc.castSucc.castSucc.castSucc
                  (Fin.last (n + 1)).castSucc.castSucc
                  (Fin.last (n + 3)))
                (Delta0Formula.successorAt
                  (Fin.last (n + 3))
                  (Fin.last (n + 2)).castSucc)))))))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natAddTransitionDelta : Delta0Formula 6 :=
  natAddTransitionDeltaAt
    (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
The complete bounded condition on `[omega, x, y, z, ySucc, graph]`:
`graph : ySucc → omega`, its zero value is `x`, its `y` value is `z`, and
successive indices have successive values.
-/
def natAddGraphDeltaAt {n : Nat}
    (omega x y z ySucc graph : Fin n) : Delta0Formula n :=
  .conj
    (TextbookDefFormula.isFunctionDeltaAt
      graph ySucc omega)
    (.conj
      (Delta0Formula.boundedEx ySucc
        (.conj
          (Delta0Formula.emptyDeltaAt (Fin.last n))
          (TextbookDefFormula.graphValueDeltaAt
            graph.castSucc (Fin.last n) x.castSucc)))
      (.conj
        (TextbookDefFormula.graphValueDeltaAt
          graph y z)
        (natAddTransitionDeltaAt omega y ySucc graph)))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natAddGraphDelta : Delta0Formula 6 :=
  natAddGraphDeltaAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
Pure membership-language formula for natural-number addition.  The free
layout is `[omega, x, y, z]`.  The first conjunct identifies `omega` as the
least inductive set, so this is not merely addition relative to an arbitrary
set called `omega`.
-/
def natAddFormula : FOFormula 4 :=
  .conj
    (Model.standardOmegaAt (0 : Fin 4))
    (.conj
      (.mem (1 : Fin 4) (0 : Fin 4))
      (.conj
        (.mem (2 : Fin 4) (0 : Fin 4))
        (.conj
          (.mem (3 : Fin 4) (0 : Fin 4))
          (.ex
            (.conj
              (Delta0Formula.successorAt
                (Fin.last 4) (2 : Fin 4).castSucc).toFO
              (.ex natAddGraphDelta.toFO))))))

/-! ## Ambient semantics of the bounded body -/

@[simp]
theorem satisfies_natAddTransitionDeltaAt {n : Nat}
    (omega y ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natAddTransitionDeltaAt omega y ySucc graph) s <->
      forall k, k ∈ s y ->
        insert k k ∈ s ySucc /\
          exists value, value ∈ s omega /\
            ZFSet.pair k value ∈ s graph /\
            insert value value ∈ s omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ s graph := by
  simp [natAddTransitionDeltaAt]

@[simp]
theorem satisfies_natAddTransitionDelta
    (omega x y z ySucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddTransitionDelta
        ![omega, x, y, z, ySucc, graph] <->
      forall k, k ∈ y ->
        insert k k ∈ ySucc /\
          exists value, value ∈ omega /\
            ZFSet.pair k value ∈ graph /\
            insert value value ∈ omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ graph := by
  simp [natAddTransitionDelta]

@[simp]
theorem satisfies_natAddGraphDeltaAt {n : Nat}
    (omega x y z ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natAddGraphDeltaAt omega x y z ySucc graph) s <->
      ZFSet.IsFunc (s ySucc) (s omega) (s graph) /\
      ((∅ : ZFSet.{u}) ∈ s ySucc /\ ZFSet.pair ∅ (s x) ∈ s graph) /\
      ZFSet.pair (s y) (s z) ∈ s graph /\
      (forall k, k ∈ s y ->
        insert k k ∈ s ySucc /\
          exists value, value ∈ s omega /\
            ZFSet.pair k value ∈ s graph /\
            insert value value ∈ s omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ s graph) := by
  simp [natAddGraphDeltaAt]

@[simp]
theorem satisfies_natAddGraphDelta
    (omega x y z ySucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
        ![omega, x, y, z, ySucc, graph] <->
      ZFSet.IsFunc ySucc omega graph /\
      ((∅ : ZFSet.{u}) ∈ ySucc /\ ZFSet.pair ∅ x ∈ graph) /\
      ZFSet.pair y z ∈ graph /\
      (forall k, k ∈ y ->
        insert k k ∈ ySucc /\
          exists value, value ∈ omega /\
            ZFSet.pair k value ∈ graph /\
            insert value value ∈ omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ graph) := by
  simp [natAddGraphDelta]

/-! ## Ambient semantics of the standard-omega guard -/

@[simp]
theorem satisfies_transitiveZFEmptyAt_ambient {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFEmptyAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  simp only [Model.transitiveZFEmptyAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    exact ZFSet.eq_empty _ |>.mpr (fun x hx => h x hx)
  · intro hempty x hx
    rw [hempty] at hx
    exact ZFSet.notMem_empty x hx

@[simp]
theorem satisfies_transitiveZFSuccessorAt_ambient {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFSuccessorAt successor index) s <->
      s successor = insert (s index) (s index) := by
  simp only [Model.transitiveZFSuccessorAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hforward, hbackward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases hforward z hz with hzIndex | hzEq
      · exact Or.inr hzIndex
      · exact Or.inl hzEq
    · rintro (rfl | hz)
      · exact hindex
      · exact hbackward z hz
  · intro hsuccessor
    rw [hsuccessor]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro z hz
      rcases ZFSet.mem_insert_iff.mp hz with hzEq | hzIndex
      · exact Or.inr hzEq
      · exact Or.inl hzIndex
    · intro z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr hz)

@[simp]
theorem satisfies_transitiveZFInductiveAt_ambient {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFInductiveAt i) s <->
      (∅ : ZFSet.{u}) ∈ s i /\
        forall x, x ∈ s i -> insert x x ∈ s i := by
  simp [Model.transitiveZFInductiveAt]

theorem ambient_inductive_contains_natCode
    {w : ZFSet.{u}}
    (hw : (∅ : ZFSet.{u}) ∈ w /\
      forall x, x ∈ w -> insert x x ∈ w) :
    forall n : Nat, (natCode n : ZFSet.{u}) ∈ w := by
  intro n
  induction n with
  | zero =>
      simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      rw [natCode_succ_eq_insert]
      exact hw.2 (natCode n) ih

@[simp]
theorem satisfies_standardOmegaAt_ambient_iff {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  rw [Model.standardOmegaAt]
  simp only [FOFormula.Satisfies, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedAll,
    satisfies_transitiveZFInductiveAt_ambient,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinductive, hminimal⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact hminimal Ordinal.omega0.toZFSet
        (by
          constructor
          · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode ∅).mpr
              ⟨0, by simp [natCode]⟩
          · intro x hx
            rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
              ⟨k, rfl⟩
            rw [← natCode_succ_eq_insert]
            exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode (k + 1))).mpr ⟨k + 1, rfl⟩) z hz
    · intro hz
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode z).mp hz with
        ⟨k, rfl⟩
      exact ambient_inductive_contains_natCode hinductive k
  · intro homega
    rw [homega]
    constructor
    · constructor
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode ∅).mpr
          ⟨0, by simp [natCode]⟩
      · intro x hx
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
          ⟨k, rfl⟩
        rw [← natCode_succ_eq_insert]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (k + 1))).mpr ⟨k + 1, rfl⟩
    · intro w hw z hz
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode z).mp hz with
        ⟨k, rfl⟩
      exact ambient_inductive_contains_natCode hw k

/-! ## Canonical finite graphs -/

/-- The canonical tuple `k ↦ natCode (a + k)` of length `b + 1`. -/
noncomputable def natAddCanonicalTuple (a b : Nat) :
    Tuple (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) (b + 1) :=
  fun i =>
    ⟨natCode (a + i.1),
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + i.1))).mpr ⟨a + i.1, rfl⟩⟩

/-- The Kuratowski graph of the canonical addition recursion. -/
noncomputable def natAddCanonicalGraph (a b : Nat) : ZFSet.{u} :=
  textbookTupleGraph (natAddCanonicalTuple a b)

theorem natAddCanonicalGraph_isFunc (a b : Nat) :
    ZFSet.IsFunc (natCode (b + 1)) Ordinal.omega0.toZFSet
      (natAddCanonicalGraph a b) := by
  exact textbookTupleGraph_isFunc (natAddCanonicalTuple a b)

/-- The canonical recursion graph is an element of every transitive ZF model.
This is the finite-witness closure needed for restricted existential
satisfaction. -/
theorem natAddCanonicalGraph_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M) (a b : Nat) :
    natAddCanonicalGraph a b ∈ M := by
  apply Model.finiteIsFunc_mem_of_isTransitiveZFModel hM
    (Model.omega_toZFSet_mem_of_isTransitiveZFModel hM)
  exact natAddCanonicalGraph_isFunc a b

@[simp]
theorem natAddCanonicalGraph_value (a b : Nat) (i : Fin (b + 1)) :
    ZFSet.pair (natCode i.1) (natCode (a + i.1)) ∈
      natAddCanonicalGraph a b := by
  exact textbookTupleGraph_value
    (natAddCanonicalTuple a b) i

theorem natAddCanonicalGraph_satisfies (a b : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
        natCode (a + b), natCode (b + 1), natAddCanonicalGraph a b] := by
  rw [satisfies_natAddGraphDelta]
  refine ⟨natAddCanonicalGraph_isFunc a b, ?_, ?_, ?_⟩
  · constructor
    · apply (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (∅ : ZFSet.{u}) (b + 1)).mpr
      exact ⟨0, Nat.zero_lt_succ b, by simp [natCode]⟩
    · simpa [natCode] using
        (natAddCanonicalGraph_value a b ⟨0, Nat.zero_lt_succ b⟩)
  · simpa using
      (natAddCanonicalGraph_value a b ⟨b, Nat.lt_succ_self b⟩)
  · intro k hk
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt k b).mp hk with
      ⟨j, hj, rfl⟩
    constructor
    · rw [← natCode_succ_eq_insert]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode (j + 1)) (b + 1)).mpr
          ⟨j + 1, Nat.succ_lt_succ hj, rfl⟩
    · refine ⟨natCode (a + j),
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (a + j))).mpr ⟨a + j, rfl⟩, ?_, ?_, ?_⟩
      · exact natAddCanonicalGraph_value a b ⟨j, hj.trans (Nat.lt_succ_self b)⟩
      · rw [← natCode_succ_eq_insert]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (a + j + 1))).mpr ⟨a + j + 1, rfl⟩
      · rw [← natCode_succ_eq_insert, ← natCode_succ_eq_insert]
        simpa [Nat.add_assoc] using natAddCanonicalGraph_value a b
          ⟨j + 1, Nat.succ_lt_succ hj⟩

/-! ## Uniqueness of the finite recursion -/

theorem natAddGraphDelta_output_unique
    (a b : Nat) (z ySucc graph : ZFSet.{u})
    (hySucc : ySucc = natCode (b + 1))
    (hgraph :
      Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
          z, ySucc, graph]) :
    z = natCode (a + b) := by
  rw [satisfies_natAddGraphDelta] at hgraph
  rcases hgraph with ⟨hfunc, hzero, hyValue, hstep⟩
  have hvalues : forall j : Nat, j <= b ->
      ZFSet.pair (natCode j) (natCode (a + j)) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        simpa [natCode] using hzero.2
    | succ j ih =>
        have hjb : j < b := Nat.lt_of_succ_le hj
        have hjDomain : (natCode j : ZFSet.{u}) ∈ ySucc := by
          rw [hySucc]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (b + 1)).mpr
              ⟨j, hjb.trans (Nat.lt_succ_self b), rfl⟩
        rcases hfunc.2 (natCode j) hjDomain with
          ⟨output, _houtput, hunique⟩
        rcases hstep (natCode j)
            ((IndexedSequenceZF.mem_natCode_iff_exists_lt
              (natCode j) b).mpr ⟨j, hjb, rfl⟩) with
          ⟨_hnextDomain, value, _hvalueOmega, hvalue,
            _hnextOmega, hnext⟩
        have hprevious := ih (Nat.le_of_lt hjb)
        have hvalueEq : value = natCode (a + j) :=
          (hunique value hvalue).trans
            (hunique (natCode (a + j)) hprevious).symm
        rw [hvalueEq, ← natCode_succ_eq_insert,
          ← natCode_succ_eq_insert] at hnext
        simpa [Nat.add_assoc] using hnext
  have hbDomain : (natCode b : ZFSet.{u}) ∈ ySucc := by
    rw [hySucc]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode b) (b + 1)).mpr ⟨b, Nat.lt_succ_self b, rfl⟩
  rcases hfunc.2 (natCode b) hbDomain with
    ⟨output, _houtput, hunique⟩
  exact (hunique z hyValue).trans
    (hunique (natCode (a + b)) (hvalues b le_rfl)).symm

@[simp]
theorem satisfies_natAddFormula_ambient
    (omega x y z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
        ![omega, x, y, z] <->
      omega = Ordinal.omega0.toZFSet /\
      x ∈ omega /\ y ∈ omega /\ z ∈ omega /\
      exists ySucc, ySucc = insert y y /\
        exists graph,
          Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
            ![omega, x, y, z, ySucc, graph] := by
  let s : Tuple ZFSet.{u} 4 := ![omega, x, y, z]
  have hs0 : s (0 : Fin 4) = omega := rfl
  have hs1 : s (1 : Fin 4) = x := rfl
  have hs2 : s (2 : Fin 4) = y := rfl
  have hs3 : s (3 : Fin 4) = z := rfl
  change
    (FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (Delta0Formula.ZFMem (s 1) (s 0) /\
      (Delta0Formula.ZFMem (s 2) (s 0) /\
      (Delta0Formula.ZFMem (s 3) (s 0) /\
      exists ySucc,
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph))))) <-> _
  rw [satisfies_standardOmegaAt_ambient_iff]
  simp only [hs0, hs1, hs2, hs3]
  constructor
  · rintro ⟨homega, hx, hy, hz, ySucc, hySuccFormula,
      graph, hgraphFormula⟩
    have hySucc : ySucc = insert y y := by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt] at hySuccFormula
      simpa only [snoc_last, snoc_castSucc, hs2] using hySuccFormula
    have hassign : snoc (snoc s ySucc) graph =
        ![omega, x, y, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [Delta0Formula.satisfies_toFO, hassign] at hgraphFormula
    exact ⟨homega, hx, hy, hz, ySucc, hySucc, graph, hgraphFormula⟩
  · rintro ⟨homega, hx, hy, hz, ySucc, hySucc, graph, hgraph⟩
    refine ⟨homega, hx, hy, hz, ySucc, ?_, graph, ?_⟩
    · rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hs2] using hySucc
    · have hassign : snoc (snoc s ySucc) graph =
          ![omega, x, y, z, ySucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [Delta0Formula.satisfies_toFO, hassign]
      exact hgraph

@[simp]
theorem satisfies_natAddFormula_natCode_iff
    (a b : Nat) (z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a + b) := by
  rw [satisfies_natAddFormula_ambient]
  constructor
  · rintro ⟨_homega, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySucc, graph, hgraph⟩
    apply natAddGraphDelta_output_unique a b z ySucc graph
    · exact hySucc.trans (natCode_succ_eq_insert b).symm
    · exact hgraph
  · intro hz
    subst z
    refine ⟨rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + b))).mpr ⟨a + b, rfl⟩,
      natCode (b + 1), ?_, natAddCanonicalGraph a b, ?_⟩
    · exact (natCode_succ_eq_insert b)
    · exact natAddCanonicalGraph_satisfies a b

/-! ## Restricted semantics in transitive ZF models -/

theorem satisfiesIn_natAddFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (a b : Nat) {z : ZFSet.{u}} (hzM : z ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natAddFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a + b) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let s : Tuple ZFSet.{u} 4 := ![omega, natCode a, natCode b, z]
  have homegaM : omega ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have haM : (natCode a : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM a
  have hbM : (natCode b : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM b
  have hsM : forall i, s i ∈ M := by
    intro i
    fin_cases i
    · exact homegaM
    · exact haM
    · exact hbM
    · exact hzM
  change
    ((Model.SatisfiesIn (M : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (natCode a : ZFSet.{u}) ∈ omega /\
      (natCode b : ZFSet.{u}) ∈ omega /\
      z ∈ omega /\
      exists ySucc, ySucc ∈ M /\
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        exists graph, graph ∈ M /\
          Model.SatisfiesIn (M : Set ZFSet.{u}) natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph)) <-> _)
  constructor
  · rintro ⟨homegaFormula, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySuccM, hySuccFormula, graph, hgraphM, hgraphFormula⟩
    have _homega : s (0 : Fin 4) = Ordinal.omega0.toZFSet :=
      (Model.satisfiesIn_standardOmegaAt_iff hM
        (0 : Fin 4) s hsM).mp homegaFormula
    have hsuccAssign : snoc s ySucc =
        ![omega, natCode a, natCode b, z, ySucc] := by
      funext i
      fin_cases i <;> rfl
    have hsuccAssignM : forall i, snoc s ySucc i ∈ M := by
      rw [hsuccAssign]
      intro i
      fin_cases i
      · exact homegaM
      · exact haM
      · exact hbM
      · exact hzM
      · exact hySuccM
    have hySuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc) hsuccAssignM).mp hySuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hySuccAmbient
    have hySucc : ySucc = natCode (b + 1) := by
      have hraw : ySucc = insert (natCode b) (natCode b) := by
        rw [hsuccAssign] at hySuccAmbient
        simpa using hySuccAmbient
      exact hraw.trans (natCode_succ_eq_insert b).symm
    have hassign : snoc (snoc s ySucc) graph =
        ![omega, natCode a, natCode b, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    have hgraphAssignM : forall i,
        snoc (snoc s ySucc) graph i ∈ M := by
      rw [hassign]
      intro i
      fin_cases i
      · exact homegaM
      · exact haM
      · exact hbM
      · exact hzM
      · exact hySuccM
      · exact hgraphM
    have hgraphAbsolute :
        Model.SatisfiesIn (M : Set ZFSet.{u}) natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph) <->
          FOFormula.Satisfies Delta0Formula.ZFMem natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph) :=
      Model.satisfiesIn_delta0_iff hM.1 natAddGraphDelta
        (snoc (snoc s ySucc) graph) hgraphAssignM
    have hgraphAmbient := hgraphAbsolute.mp hgraphFormula
    rw [Delta0Formula.satisfies_toFO] at hgraphAmbient
    rw [hassign] at hgraphAmbient
    have hresult := natAddGraphDelta_output_unique
      a b z ySucc graph hySucc hgraphAmbient
    exact hresult
  · intro hz
    have hzEq : z = (natCode (a + b) : ZFSet.{u}) := hz
    have hySuccM : (natCode (b + 1) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (b + 1)
    have hcanonicalFunc := natAddCanonicalGraph_isFunc a b
    have hgraphM : natAddCanonicalGraph a b ∈ M :=
      Model.finiteIsFunc_mem_of_isTransitiveZFModel
        hM homegaM hcanonicalFunc
    refine ⟨(Model.satisfiesIn_standardOmegaAt_iff hM
      (0 : Fin 4) s hsM).mpr rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩, ?_,
      natCode (b + 1), hySuccM, ?_,
      natAddCanonicalGraph a b, hgraphM, ?_⟩
    · rw [hzEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + b))).mpr ⟨a + b, rfl⟩
    · have hsuccAssign : snoc s (natCode (b + 1)) =
          ![omega, natCode a, natCode b, z, natCode (b + 1)] := by
        funext i
        fin_cases i <;> rfl
      have hsuccAssignM : forall i,
          snoc s (natCode (b + 1)) i ∈ M := by
        rw [hsuccAssign]
        intro i
        fin_cases i
        · exact homegaM
        · exact haM
        · exact hbM
        · exact hzM
        · exact hySuccM
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s (natCode (b + 1))) hsuccAssignM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      rw [hsuccAssign]
      simpa using
        (natCode_succ_eq_insert b)
    · have hassign :
          snoc (snoc s (natCode (b + 1)))
              (natAddCanonicalGraph a b) =
            ![omega, natCode a, natCode b, z,
              natCode (b + 1), natAddCanonicalGraph a b] := by
        funext i
        fin_cases i <;> rfl
      have hgraphAssignM : forall i,
          snoc (snoc s (natCode (b + 1)))
            (natAddCanonicalGraph a b) i ∈ M := by
        rw [hassign]
        intro i
        fin_cases i
        · exact homegaM
        · exact haM
        · exact hbM
        · exact hzM
        · exact hySuccM
        · exact hgraphM
      apply (Model.satisfiesIn_delta0_iff hM.1 natAddGraphDelta
        (snoc (snoc s (natCode (b + 1)))
          (natAddCanonicalGraph a b)) hgraphAssignM).mpr
      rw [Delta0Formula.satisfies_toFO]
      rw [hassign, hzEq]
      exact natAddCanonicalGraph_satisfies a b

/-! ## Standard function-absoluteness packaging -/

/-- Total ambient operation on arbitrary set codes.  Invalid inputs are sent
to the empty set; the graph formula is restricted to standard codes by its
domain predicate. -/
noncomputable def natAddCodeZF (x y : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode x, textbookNatDecode y with
  | some a, some b => natCode (a + b)
  | _, _ => ∅

@[simp]
theorem natAddCodeZF_natCode (a b : Nat) :
    natAddCodeZF (natCode a : ZFSet.{u}) (natCode b) =
      natCode (a + b) := by
  simp [natAddCodeZF]

/-- Input domain for the ternary-parameter presentation `[omega, x, y]` of
addition.  The graph output is the fourth coordinate of `natAddFormula`. -/
def NatAddTupleDomain : Set (Tuple ZFSet.{u} 3) :=
  {s | s 0 = Ordinal.omega0.toZFSet /\
    exists a b : Nat, s 1 = natCode a /\ s 2 = natCode b}

/-- Ambient value function matching `natAddFormula` on
`NatAddTupleDomain`. -/
noncomputable def natAddTupleFunction
    (s : Tuple ZFSet.{u} 3) : ZFSet.{u} :=
  natAddCodeZF (s 1) (s 2)

/-- Natural-number addition, expressed by a pure membership-language finite
recursion graph, is absolute to every transitive set model of ZF. -/
theorem natAdd_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M) :
    Model.FunctionAbsoluteTo (M : Set ZFSet.{u})
      NatAddTupleDomain natAddTupleFunction natAddFormula := by
  constructor
  · intro s hsM hsDomain
    rcases hsDomain with ⟨_homega, a, b, hx, hy⟩
    rw [natAddTupleFunction, hx, hy, natAddCodeZF_natCode]
    exact Model.natCode_mem_of_isTransitiveZFModel hM (a + b)
  · intro s z hsM hzM
    constructor
    · intro hformula
      rw [natAddFormula] at hformula
      have homega : s 0 = Ordinal.omega0.toZFSet :=
        (Model.satisfiesIn_standardOmegaAt_iff hM
          (0 : Fin 4) (snoc s z)
          ((Model.tupleIn_snoc_iff.mpr ⟨hsM, hzM⟩))).mp hformula.1
      have hxOmega : s 1 ∈ Ordinal.omega0.toZFSet := by
        rw [← homega]
        have hxFormula := hformula.2.1
        change snoc s z (1 : Fin 3).castSucc ∈
          snoc s z (0 : Fin 3).castSucc at hxFormula
        simpa only [snoc_castSucc] using hxFormula
      have hyOmega : s 2 ∈ Ordinal.omega0.toZFSet := by
        rw [← homega]
        have hyFormula := hformula.2.2.1
        change snoc s z (2 : Fin 3).castSucc ∈
          snoc s z (0 : Fin 3).castSucc at hyFormula
        simpa only [snoc_castSucc] using hyFormula
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode (s 1)).mp
          hxOmega with ⟨a, hx⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode (s 2)).mp
          hyOmega with ⟨b, hy⟩
      have hassign : snoc s z =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
            natCode a, natCode b, z] := by
        funext i
        fin_cases i
        · exact homega
        · exact hx
        · exact hy
        · rfl
      have hvalue : z = natCode (a + b) :=
        (satisfiesIn_natAddFormula_natCode_iff hM a b hzM).mp
          (by rwa [← hassign])
      refine ⟨⟨homega, a, b, hx, hy⟩, ?_⟩
      rw [natAddTupleFunction, hx, hy, natAddCodeZF_natCode]
      exact hvalue
    · rintro ⟨⟨homega, a, b, hx, hy⟩, hvalue⟩
      have hfunction : natAddTupleFunction s = natCode (a + b) := by
        rw [natAddTupleFunction, hx, hy, natAddCodeZF_natCode]
      have hz : z = natCode (a + b) := hvalue.trans hfunction
      have hassign : snoc s z =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
            natCode a, natCode b, z] := by
        funext i
        fin_cases i
        · exact homega
        · exact hx
        · exact hy
        · rfl
      rw [hassign]
      exact (satisfiesIn_natAddFormula_natCode_iff hM a b hzM).mpr hz

end TextbookNatFormula

end Constructible
