/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookDefinabilityCode
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookTupleSpaceAbsolute

/-!
# Absoluteness of the textbook atomic relation generators

This file gives first-order graph formulas for the total set-coded operations
`textbookDInCodeZF` and `textbookDEqCodeZF`.  The standard-finite guard occurs
inside the extensional membership condition.  Consequently an invalid arity
has the uniquely specified empty output, rather than merely lying outside the
domain of the graph formula.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookDefFormula

/-! ## Bounded membership predicates -/

/-- A candidate finite function graph belongs to `D_in(a,n,i,j)`. -/
def dInMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) : Delta0Formula n :=
  .conj (.mem left arity)
    (.conj (.mem right arity)
      (.conj (isFunctionDeltaAt graph arity a)
        (Delta0Formula.boundedEx a
          (Delta0Formula.boundedEx a.castSucc
            (.conj
              (graphValueDeltaAt graph.castSucc.castSucc
                left.castSucc.castSucc (Fin.last n).castSucc)
              (.conj
                (graphValueDeltaAt graph.castSucc.castSucc
                  right.castSucc.castSucc (Fin.last (n + 1)))
                (.mem (Fin.last n).castSucc (Fin.last (n + 1)))))))))

@[simp]
theorem satisfies_dInMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (dInMemberDeltaAt a arity left right graph) s ↔
      s left ∈ s arity ∧ s right ∈ s arity ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ x ∈ s a, ∃ y ∈ s a,
            ZFSet.pair (s left) x ∈ s graph ∧
              ZFSet.pair (s right) y ∈ s graph ∧ x ∈ y := by
  simp [dInMemberDeltaAt]

/-- A candidate finite function graph belongs to `D_eq(a,n,i,j)`. -/
def dEqMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) : Delta0Formula n :=
  .conj (.mem left arity)
    (.conj (.mem right arity)
      (.conj (isFunctionDeltaAt graph arity a)
        (Delta0Formula.boundedEx a
          (.conj
            (graphValueDeltaAt graph.castSucc left.castSucc (Fin.last n))
            (graphValueDeltaAt graph.castSucc right.castSucc
              (Fin.last n))))))

@[simp]
theorem satisfies_dEqMemberDeltaAt {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (dEqMemberDeltaAt a arity left right graph) s ↔
      s left ∈ s arity ∧ s right ∈ s arity ∧
        ZFSet.IsFunc (s arity) (s a) (s graph) ∧
          ∃ x ∈ s a,
            ZFSet.pair (s left) x ∈ s graph ∧
              ZFSet.pair (s right) x ∈ s graph := by
  simp [dEqMemberDeltaAt]

/-- Layout `[a, arity, left, right, graph]`. -/
def dInMemberDelta : Delta0Formula 5 :=
  dInMemberDeltaAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)

/-- Layout `[a, arity, left, right, graph]`. -/
def dEqMemberDelta : Delta0Formula 5 :=
  dEqMemberDeltaAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)

@[simp]
theorem satisfies_dInMemberDelta
    (a arity left right graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem dInMemberDelta
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a, ∃ y ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  simp [dInMemberDelta]

@[simp]
theorem satisfies_dEqMemberDelta
    (a arity left right graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem dEqMemberDelta
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right x ∈ graph := by
  simp [dEqMemberDelta]

/-! ## Extensional output formulas -/

/-- The right-hand side of the extensional definition of `D_in` membership.
Layout `[a, arity, left, right, output, candidate]`; `output` is unused. -/
def dInOutputMemberCondition : FOFormula 6 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 6))
    (dInMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5)).toFO

/-- The right-hand side of the extensional definition of `D_eq` membership.
Layout `[a, arity, left, right, output, candidate]`; `output` is unused. -/
def dEqOutputMemberCondition : FOFormula 6 :=
  .conj
    (Model.standardFiniteDomainAt (1 : Fin 6))
    (dEqMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5)).toFO

/-- Layout `[a, arity, left, right, output]`. -/
def dInOutputFormula : FOFormula 5 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      dInOutputMemberCondition)

/-- Layout `[a, arity, left, right, output]`. -/
def dEqOutputFormula : FOFormula 5 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      dEqOutputMemberCondition)

end TextbookDefFormula

/-! ## Exact ambient specifications of the totalized operations -/

@[simp]
theorem mem_textbookDInCodeZF_iff
    {a arity left right graph : ZFSet.{u}} :
    graph ∈ textbookDInCodeZF a arity left right ↔
      (∃ n : Nat, arity = natCode n) ∧
        left ∈ arity ∧ right ∈ arity ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ x ∈ a, ∃ y ∈ a,
              ZFSet.pair left x ∈ graph ∧
                ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  constructor
  · intro hgraph
    unfold textbookDInCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        cases hleft : textbookNatDecode left with
        | none => simp [harity, hleft] at hgraph
        | some i =>
            cases hright : textbookNatDecode right with
            | none => simp [harity, hleft, hright] at hgraph
            | some j =>
                simp only [harity, hleft, hright] at hgraph
                have harityEq : arity = natCode n :=
                  textbookNatDecode_eq_some_iff.mp harity
                have hleftEq : left = natCode i :=
                  textbookNatDecode_eq_some_iff.mp hleft
                have hrightEq : right = natCode j :=
                  textbookNatDecode_eq_some_iff.mp hright
                subst arity
                subst left
                subst right
                rcases mem_textbookDInZF_iff.mp hgraph with
                  ⟨hspace, hi, hj, x, y, hx, hy, hxy⟩
                have hfunc : ZFSet.IsFunc (natCode n) a graph :=
                  mem_textbookTupleSpace_iff.mp hspace
                have hxa : x ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
                have hya : y ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hy)).2
                exact ⟨⟨n, rfl⟩,
                  (natCode_mem_natCode_iff i n).mpr hi,
                  (natCode_mem_natCode_iff j n).mpr hj,
                  hfunc, x, hxa, y, hya, hx, hy, hxy⟩
  · rintro ⟨⟨n, rfl⟩, hleft, hright, hfunc,
      x, hxa, y, hya, hx, hy, hxy⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt left n).mp hleft with
      ⟨i, hi, rfl⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt right n).mp hright with
      ⟨j, hj, rfl⟩
    rw [textbookDInCodeZF_natCode, mem_textbookDInZF_iff]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      hi, hj, x, y, hx, hy, hxy⟩

@[simp]
theorem mem_textbookDEqCodeZF_iff
    {a arity left right graph : ZFSet.{u}} :
    graph ∈ textbookDEqCodeZF a arity left right ↔
      (∃ n : Nat, arity = natCode n) ∧
        left ∈ arity ∧ right ∈ arity ∧
          ZFSet.IsFunc arity a graph ∧
            ∃ x ∈ a,
              ZFSet.pair left x ∈ graph ∧
                ZFSet.pair right x ∈ graph := by
  constructor
  · intro hgraph
    unfold textbookDEqCodeZF at hgraph
    cases harity : textbookNatDecode arity with
    | none => simp [harity] at hgraph
    | some n =>
        cases hleft : textbookNatDecode left with
        | none => simp [harity, hleft] at hgraph
        | some i =>
            cases hright : textbookNatDecode right with
            | none => simp [harity, hleft, hright] at hgraph
            | some j =>
                simp only [harity, hleft, hright] at hgraph
                have harityEq : arity = natCode n :=
                  textbookNatDecode_eq_some_iff.mp harity
                have hleftEq : left = natCode i :=
                  textbookNatDecode_eq_some_iff.mp hleft
                have hrightEq : right = natCode j :=
                  textbookNatDecode_eq_some_iff.mp hright
                subst arity
                subst left
                subst right
                rcases mem_textbookDEqZF_iff.mp hgraph with
                  ⟨hspace, hi, hj, x, hx, hx'⟩
                have hfunc : ZFSet.IsFunc (natCode n) a graph :=
                  mem_textbookTupleSpace_iff.mp hspace
                have hxa : x ∈ a :=
                  (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
                exact ⟨⟨n, rfl⟩,
                  (natCode_mem_natCode_iff i n).mpr hi,
                  (natCode_mem_natCode_iff j n).mpr hj,
                  hfunc, x, hxa, hx, hx'⟩
  · rintro ⟨⟨n, rfl⟩, hleft, hright, hfunc,
      x, hxa, hx, hx'⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt left n).mp hleft with
      ⟨i, hi, rfl⟩
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt right n).mp hright with
      ⟨j, hj, rfl⟩
    rw [textbookDEqCodeZF_natCode, mem_textbookDEqZF_iff]
    exact ⟨mem_textbookTupleSpace_iff.mpr hfunc,
      hi, hj, x, hx, hx'⟩

namespace Model

noncomputable section

private theorem satisfiesIn_atomicAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

private theorem satisfiesIn_atomicBiimp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s ↔
      (SatisfiesIn M left s ↔ SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj,
    SatisfiesIn]
  tauto

/-! ## Restricted semantics of the bounded predicates -/

theorem satisfiesIn_dInMemberDelta_iff
    {M a arity left right graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInMemberDelta.toFO
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a, ∃ y ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right y ∈ graph ∧ x ∈ y := by
  have hs : ∀ i : Fin 5, ![a, arity, left, right, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM TextbookDefFormula.dInMemberDelta
    ![a, arity, left, right, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_dInMemberDelta
      a arity left right graph)

theorem satisfiesIn_dEqMemberDelta_iff
    {M a arity left right graph : ZFSet.{u}}
    (hM : M.IsTransitive) (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqMemberDelta.toFO
        ![a, arity, left, right, graph] ↔
      left ∈ arity ∧ right ∈ arity ∧
        ZFSet.IsFunc arity a graph ∧
          ∃ x ∈ a,
            ZFSet.pair left x ∈ graph ∧
              ZFSet.pair right x ∈ graph := by
  have hs : ∀ i : Fin 5, ![a, arity, left, right, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact hgraph
  rw [satisfiesIn_delta0_iff hM TextbookDefFormula.dEqMemberDelta
    ![a, arity, left, right, graph] hs]
  simpa only [Delta0Formula.satisfies_toFO] using
    (TextbookDefFormula.satisfies_dEqMemberDelta
      a arity left right graph)

/-! ## Restricted semantics of the totalized member conditions -/

theorem satisfiesIn_dInOutputMemberCondition_iff
    {M a arity left right output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph] ↔
      graph ∈ textbookDInCodeZF a arity left right := by
  rw [TextbookDefFormula.dInOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 6,
      ![a, arity, left, right, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 6) ![a, arity, left, right, output, graph] hs]
  rw [satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.dInMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5))
    ![a, arity, left, right, output, graph] hs]
  simp [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dInMemberDeltaAt]

theorem satisfiesIn_dEqOutputMemberCondition_iff
    {M a arity left right output graph : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph] ↔
      graph ∈ textbookDEqCodeZF a arity left right := by
  rw [TextbookDefFormula.dEqOutputMemberCondition]
  simp only [SatisfiesIn]
  have hs : ∀ i : Fin 6,
      ![a, arity, left, right, output, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact ha
    · exact harity
    · exact hleft
    · exact hright
    · exact houtput
    · exact hgraph
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (1 : Fin 6) ![a, arity, left, right, output, graph] hs]
  rw [satisfiesIn_delta0_iff hM.1
    (TextbookDefFormula.dEqMemberDeltaAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (Fin.last 5))
    ![a, arity, left, right, output, graph] hs]
  simp [Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_dEqMemberDeltaAt]

/-! ## Closure of the standard-`Nat` atomic outputs -/

theorem textbookDInZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n i j : Nat) : textbookDInZF a n i j ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM j
  have hspaceM : textbookTupleSpace a n ∈ M :=
    textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
  let params : Tuple (ZFCarrier M) 4 :=
    ![⟨a, ha⟩, ⟨natCode n, hnM⟩,
      ⟨natCode i, hiM⟩, ⟨natCode j, hjM⟩]
  let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.dInMemberDelta.toFO params space
  have hassign (graph : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) graph =
        ![a, natCode n, natCode i, natCode j, graph] := by
    funext k
    fin_cases k <;> rfl
  have hsepEq :
      (space.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.dInMemberDelta.toFO
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookDInZF a n i j := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookDInZF_iff]
    constructor
    · rintro ⟨hgraphSpace, hformula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      rw [hassign graph] at hformula
      rcases (satisfiesIn_dInMemberDelta_iff hM.1 ha hnM hiM hjM
          hgraphM).mp hformula with
        ⟨hiCode, hjCode, _hfunc, x, _hxa, y, _hya, hx, hy, hxy⟩
      exact ⟨hgraphSpace,
        (natCode_mem_natCode_iff i n).mp hiCode,
        (natCode_mem_natCode_iff j n).mp hjCode,
        x, y, hx, hy, hxy⟩
    · rintro ⟨hgraphSpace, hi, hj, x, y, hx, hy, hxy⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      have hfunc : ZFSet.IsFunc (natCode n) a graph :=
        mem_textbookTupleSpace_iff.mp hgraphSpace
      have hxa : x ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
      have hya : y ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hy)).2
      refine ⟨hgraphSpace, ?_⟩
      rw [hassign graph]
      apply (satisfiesIn_dInMemberDelta_iff hM.1 ha hnM hiM hjM
        hgraphM).mpr
      exact ⟨(natCode_mem_natCode_iff i n).mpr hi,
        (natCode_mem_natCode_iff j n).mpr hj,
        hfunc, x, hxa, y, hya, hx, hy, hxy⟩
  rw [hsepEq] at hsep
  exact hsep

theorem textbookDEqZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n i j : Nat) : textbookDEqZF a n i j ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM j
  have hspaceM : textbookTupleSpace a n ∈ M :=
    textbookTupleSpace_mem_of_isTransitiveZFModel hM ha n
  let params : Tuple (ZFCarrier M) 4 :=
    ![⟨a, ha⟩, ⟨natCode n, hnM⟩,
      ⟨natCode i, hiM⟩, ⟨natCode j, hjM⟩]
  let space : ZFCarrier M := ⟨textbookTupleSpace a n, hspaceM⟩
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.dEqMemberDelta.toFO params space
  have hassign (graph : ZFSet.{u}) :
      snoc (zfCarrierTupleVal params) graph =
        ![a, natCode n, natCode i, natCode j, graph] := by
    funext k
    fin_cases k <;> rfl
  have hsepEq :
      (space.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.dEqMemberDelta.toFO
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookDEqZF a n i j := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookDEqZF_iff]
    constructor
    · rintro ⟨hgraphSpace, hformula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      rw [hassign graph] at hformula
      rcases (satisfiesIn_dEqMemberDelta_iff hM.1 ha hnM hiM hjM
          hgraphM).mp hformula with
        ⟨hiCode, hjCode, _hfunc, x, _hxa, hx, hx'⟩
      exact ⟨hgraphSpace,
        (natCode_mem_natCode_iff i n).mp hiCode,
        (natCode_mem_natCode_iff j n).mp hjCode,
        x, hx, hx'⟩
    · rintro ⟨hgraphSpace, hi, hj, x, hx, hx'⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspaceM
      have hfunc : ZFSet.IsFunc (natCode n) a graph :=
        mem_textbookTupleSpace_iff.mp hgraphSpace
      have hxa : x ∈ a :=
        (ZFSet.pair_mem_prod.mp (hfunc.1 hx)).2
      refine ⟨hgraphSpace, ?_⟩
      rw [hassign graph]
      apply (satisfiesIn_dEqMemberDelta_iff hM.1 ha hnM hiM hjM
        hgraphM).mpr
      exact ⟨(natCode_mem_natCode_iff i n).mpr hi,
        (natCode_mem_natCode_iff j n).mpr hj,
        hfunc, x, hxa, hx, hx'⟩
  rw [hsepEq] at hsep
  exact hsep

/-! ## Closure of the total set-coded outputs -/

theorem textbookDInCodeZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (arity left right : ZFSet.{u}) :
    textbookDInCodeZF a arity left right ∈ M := by
  unfold textbookDInCodeZF
  cases harity : textbookNatDecode arity with
  | none =>
      exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      cases hleft : textbookNatDecode left with
      | none =>
          exact empty_mem_of_isTransitiveZFModel hM
      | some i =>
          cases hright : textbookNatDecode right with
          | none =>
              exact empty_mem_of_isTransitiveZFModel hM
          | some j =>
              exact textbookDInZF_mem_of_isTransitiveZFModel
                hM ha n i j

theorem textbookDEqCodeZF_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (arity left right : ZFSet.{u}) :
    textbookDEqCodeZF a arity left right ∈ M := by
  unfold textbookDEqCodeZF
  cases harity : textbookNatDecode arity with
  | none =>
      exact empty_mem_of_isTransitiveZFModel hM
  | some n =>
      cases hleft : textbookNatDecode left with
      | none =>
          exact empty_mem_of_isTransitiveZFModel hM
      | some i =>
          cases hright : textbookNatDecode right with
          | none =>
              exact empty_mem_of_isTransitiveZFModel hM
          | some j =>
              exact textbookDEqZF_mem_of_isTransitiveZFModel
                hM ha n i j

/-! ## Exact restricted semantics of the output formulas -/

theorem satisfiesIn_dInOutputFormula_components
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputFormula
        ![a, arity, left, right, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookDInCodeZF a arity left right) := by
  rw [TextbookDefFormula.dInOutputFormula,
    satisfiesIn_atomicAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, left, right, output] graph =
        ![a, arity, left, right, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dInOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_dInOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dInOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputMemberCondition
        ![a, arity, left, right, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_dInOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph).symm

theorem satisfiesIn_dEqOutputFormula_components
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputFormula
        ![a, arity, left, right, output] ↔
      ∀ graph : ZFSet.{u}, graph ∈ M →
        (graph ∈ output ↔
          graph ∈ textbookDEqCodeZF a arity left right) := by
  rw [TextbookDefFormula.dEqOutputFormula,
    satisfiesIn_atomicAll_iff]
  have hassign (graph : ZFSet.{u}) :
      snoc ![a, arity, left, right, output] graph =
        ![a, arity, left, right, output, graph] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro h graph hgraph
    have hbiimp := (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dEqOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mp
        (h graph hgraph)
    rw [hassign graph] at hbiimp
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph] at hbiimp
    exact hbiimp.trans
      (satisfiesIn_dEqOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph)
  · intro h graph hgraph
    apply (satisfiesIn_atomicBiimp_iff
      (M : Set ZFSet.{u})
      (.mem (Fin.last 5) (4 : Fin 5).castSucc)
      TextbookDefFormula.dEqOutputMemberCondition
      (snoc ![a, arity, left, right, output] graph)).mpr
    rw [hassign graph]
    change graph ∈ output ↔
      SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, arity, left, right, output, graph]
    exact (h graph hgraph).trans
      (satisfiesIn_dEqOutputMemberCondition_iff hM
        ha harity hleft hright houtput hgraph).symm

theorem satisfiesIn_dInOutputFormula_iff
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dInOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDInCodeZF a arity left right := by
  rw [satisfiesIn_dInOutputFormula_components hM
    ha harity hleft hright houtput]
  have hcode : textbookDInCodeZF a arity left right ∈ M :=
    textbookDInCodeZF_mem_of_isTransitiveZFModel hM ha arity left right
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

theorem satisfiesIn_dEqOutputFormula_iff
    {M a arity left right output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (ha : a ∈ M) (harity : arity ∈ M)
    (hleft : left ∈ M) (hright : right ∈ M)
    (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.dEqOutputFormula
        ![a, arity, left, right, output] ↔
      output = textbookDEqCodeZF a arity left right := by
  rw [satisfiesIn_dEqOutputFormula_components hM
    ha harity hleft hright houtput]
  have hcode : textbookDEqCodeZF a arity left right ∈ M :=
    textbookDEqCodeZF_mem_of_isTransitiveZFModel hM ha arity left right
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

/-! ## Standard `FunctionAbsoluteTo` packages -/

/-- The atomic generators are total on their four set-valued inputs. -/
def TextbookAtomicTupleDomain : Set (Tuple ZFSet.{u} 4) := Set.univ

theorem textbookDInCodeZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u})
      TextbookAtomicTupleDomain
      (fun s : Tuple ZFSet.{u} 4 =>
        textbookDInCodeZF (s 0) (s 1) (s 2) (s 3))
      TextbookDefFormula.dInOutputFormula := by
  constructor
  · intro s hs _hsDomain
    exact textbookDInCodeZF_mem_of_isTransitiveZFModel
      hM (hs 0) (s 1) (s 2) (s 3)
  · intro s output hs houtput
    have hassign : snoc s output =
        ![s 0, s 1, s 2, s 3, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa [TextbookAtomicTupleDomain] using
      (satisfiesIn_dInOutputFormula_iff hM
        (hs 0) (hs 1) (hs 2) (hs 3) houtput)

theorem textbookDEqCodeZF_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    FunctionAbsoluteTo (M : Set ZFSet.{u})
      TextbookAtomicTupleDomain
      (fun s : Tuple ZFSet.{u} 4 =>
        textbookDEqCodeZF (s 0) (s 1) (s 2) (s 3))
      TextbookDefFormula.dEqOutputFormula := by
  constructor
  · intro s hs _hsDomain
    exact textbookDEqCodeZF_mem_of_isTransitiveZFModel
      hM (hs 0) (s 1) (s 2) (s 3)
  · intro s output hs houtput
    have hassign : snoc s output =
        ![s 0, s 1, s 2, s 3, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa [TextbookAtomicTupleDomain] using
      (satisfiesIn_dEqOutputFormula_iff hM
        (hs 0) (hs 1) (hs 2) (hs 3) houtput)

end

end Model

end Constructible
