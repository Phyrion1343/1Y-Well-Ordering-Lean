/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalMultiplication

/-!
# The set-theoretic graph of exponentiation on the standard natural numbers

Exponentiation is defined in the pure membership language by finite recursion
from the already constructed multiplication graph.  With free-variable layout
`[omega, base, exponent, output]`, the formula asserts the existence of a
finite function `f : exponent + 1 -> omega` such that `f(0) = 1`,
`f(exponent) = output`, and `f(k + 1) = f(k) * base` for every
`k in exponent`.

The object-language formula contains only membership and equality.  Lean's
`Nat.pow` occurs only in canonical witnesses and in metatheoretic statements
of the exact semantics.
-/

@[expose] public section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

private theorem satisfiesIn_boundedEx_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedEx set formula) s <->
      exists value : ZFSet.{u}, value ∈ M /\ value ∈ s set /\
        Model.SatisfiesIn M formula (snoc s value) := by
  simp [FOFormula.boundedEx]

private theorem satisfiesIn_boundedAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall value : ZFSet.{u}, value ∈ M -> value ∈ s set ->
        Model.SatisfiesIn M formula (snoc s value) := by
  classical
  simp only [FOFormula.boundedAll, Model.SatisfiesIn,
    satisfiesIn_boundedEx_iff]
  constructor
  · intro h value hvalueM hvalueSet
    by_contra hformula
    exact h ⟨value, hvalueM, hvalueSet, hformula⟩
  · intro h hex
    rcases hex with ⟨value, hvalueM, hvalueSet, hformula⟩
    exact hformula (h value hvalueM hvalueSet)

private theorem satisfiesIn_rename_iff
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    Model.SatisfiesIn M (FOFormula.rename rename formula) s <->
      Model.SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, Model.SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-! ## The finite-recursion formula -/

/-- Coordinate renaming for the multiplication step. -/
def natPowMulRenameAt {n : Nat} (omega base : Fin n) :
    Fin 4 -> Fin (n + 4) :=
  ![omega.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (n + 2)).castSucc,
    base.castSucc.castSucc.castSucc.castSucc,
    Fin.last (n + 3)]

theorem comp_natPowMulRenameAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega base : Fin n)
    (k kSucc value nextValue : A) :
    (fun i =>
      snoc (snoc (snoc (snoc s k) kSucc) value) nextValue
        (natPowMulRenameAt omega base i)) =
      ![s omega, value, s base, nextValue] := by
  funext i
  fin_cases i <;> simp [natPowMulRenameAt]

/-- The recursive multiplication transition in an arbitrary context. -/
def natPowTransitionAt {n : Nat}
    (omega base exponent exponentSucc graph : Fin n) : FOFormula n :=
  FOFormula.boundedAll exponent
    (FOFormula.boundedEx exponentSucc.castSucc
      (.conj
        (Delta0Formula.successorAt
          (Fin.last (n + 1)) (Fin.last n).castSucc).toFO
        (FOFormula.boundedEx omega.castSucc.castSucc
          (.conj
            (TextbookDefFormula.graphValueDeltaAt
              graph.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2))).toFO
            (FOFormula.boundedEx omega.castSucc.castSucc.castSucc
              (.conj
                (TextbookDefFormula.graphValueDeltaAt
                  graph.castSucc.castSucc.castSucc.castSucc
                  (Fin.last (n + 1)).castSucc.castSucc
                  (Fin.last (n + 3))).toFO
                (FOFormula.rename (natPowMulRenameAt omega base)
                  natMulFormula)))))))

/-- Fixed layout `[omega, base, exponent, output, exponentSucc, graph]`. -/
def natPowTransition : FOFormula 6 :=
  natPowTransitionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
The bounded graph shape.  It asserts that the graph is a function from
`exponentSucc` to `omega`, sends the standard literal zero to the standard
literal one, and sends `exponent` to `output`.
-/
def natPowGraphShapeDeltaAt {n : Nat}
    (omega exponent output exponentSucc graph : Fin n) : Delta0Formula n :=
  .conj
    (TextbookDefFormula.isFunctionDeltaAt graph exponentSucc omega)
    (.conj
      (Delta0Formula.boundedEx exponentSucc
        (.conj
          (Delta0Formula.natLiteralDeltaAt 0 (Fin.last n))
          (Delta0Formula.boundedEx omega.castSucc
            (.conj
              (Delta0Formula.natLiteralDeltaAt 1 (Fin.last (n + 1)))
              (TextbookDefFormula.graphValueDeltaAt
                graph.castSucc.castSucc
                (Fin.last n).castSucc
                (Fin.last (n + 1)))))))
      (TextbookDefFormula.graphValueDeltaAt graph exponent output))

/-- Fixed layout `[omega, base, exponent, output, exponentSucc, graph]`. -/
def natPowGraphShapeDelta : Delta0Formula 6 :=
  natPowGraphShapeDeltaAt
    (0 : Fin 6) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/-- Complete graph condition in the fixed six-variable layout. -/
def natPowGraphFormula : FOFormula 6 :=
  .conj natPowGraphShapeDelta.toFO natPowTransition

/--
Pure membership-language formula for natural-number exponentiation.  Its
free-variable layout is `[omega, base, exponent, output]`.
-/
def natPowFormula : FOFormula 4 :=
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
              (.ex natPowGraphFormula))))))

/-! ## Safe reuse in larger variable contexts -/

/-- Coordinate map for embedding `[omega, base, exponent, output]`. -/
def natPowParametersAt {n : Nat}
    (omega base exponent output : Fin n) : Fin 4 -> Fin n :=
  ![omega, base, exponent, output]

/-- Exponentiation embedded into an arbitrary free-variable context. -/
def natPowFormulaAt {n : Nat}
    (omega base exponent output : Fin n) : FOFormula n :=
  FOFormula.rename (natPowParametersAt omega base exponent output)
    natPowFormula

theorem comp_natPowParametersAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega base exponent output : Fin n) :
    (fun i => s (natPowParametersAt omega base exponent output i)) =
      ![s omega, s base, s exponent, s output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_natPowFormulaAt {n : Nat}
    (omega base exponent output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (natPowFormulaAt omega base exponent output) s <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![s omega, s base, s exponent, s output] := by
  rw [natPowFormulaAt, FOFormula.satisfies_rename,
    comp_natPowParametersAt]

@[simp]
theorem satisfiesIn_natPowFormulaAt
    (M : Set ZFSet.{u}) {n : Nat}
    (omega base exponent output : Fin n) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (natPowFormulaAt omega base exponent output) s <->
      Model.SatisfiesIn M natPowFormula
        ![s omega, s base, s exponent, s output] := by
  rw [natPowFormulaAt, satisfiesIn_rename_iff,
    comp_natPowParametersAt]

/-! ## Ambient semantics of the graph formula -/

@[simp]
theorem satisfies_natPowTransitionAt {n : Nat}
    (omega base exponent exponentSucc graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (natPowTransitionAt omega base exponent exponentSucc graph) s <->
      forall k, k ∈ s exponent ->
        insert k k ∈ s exponentSucc /\
        exists value, value ∈ s omega /\
          ZFSet.pair k value ∈ s graph /\
          exists nextValue, nextValue ∈ s omega /\
            ZFSet.pair (insert k k) nextValue ∈ s graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![s omega, value, s base, nextValue] := by
  simp only [natPowTransitionAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt,
    TextbookDefFormula.satisfies_graphValueDeltaAt,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_natPowMulRenameAt]
  constructor
  · intro h k hk
    rcases h k hk with
      ⟨kSucc, hkSuccDomain, rfl, value, hvalueOmega,
        hvalue, nextValue, hnextOmega, hnext, hmul⟩
    exact ⟨hkSuccDomain, value, hvalueOmega, hvalue,
      nextValue, hnextOmega, hnext, hmul⟩
  · intro h k hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalue,
        nextValue, hnextOmega, hnext, hmul⟩
    exact ⟨insert k k, hkSuccDomain, rfl, value, hvalueOmega,
      hvalue, nextValue, hnextOmega, hnext, hmul⟩

@[simp]
theorem satisfies_natPowTransition
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] <->
      forall k, k ∈ exponent ->
        insert k k ∈ exponentSucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![omega, value, base, nextValue] := by
  exact satisfies_natPowTransitionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (4 : Fin 6) (5 : Fin 6)
    ![omega, base, exponent, output, exponentSucc, graph]

@[simp]
theorem satisfies_natPowGraphShapeDeltaAt {n : Nat}
    (omega exponent output exponentSucc graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natPowGraphShapeDeltaAt omega exponent output exponentSucc graph) s <->
      ZFSet.IsFunc (s exponentSucc) (s omega) (s graph) /\
      ((natCode 0 : ZFSet.{u}) ∈ s exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ s omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ s graph) /\
      ZFSet.pair (s exponent) (s output) ∈ s graph := by
  simp [natPowGraphShapeDeltaAt]

@[simp]
theorem satisfies_natPowGraphShapeDelta
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natPowGraphShapeDelta
        ![omega, base, exponent, output, exponentSucc, graph] <->
      ZFSet.IsFunc exponentSucc omega graph /\
      ((natCode 0 : ZFSet.{u}) ∈ exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ graph) /\
      ZFSet.pair exponent output ∈ graph := by
  simp [natPowGraphShapeDelta]

@[simp]
theorem satisfies_natPowGraphFormula
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] <->
      ZFSet.IsFunc exponentSucc omega graph /\
      ((natCode 0 : ZFSet.{u}) ∈ exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ graph) /\
      ZFSet.pair exponent output ∈ graph /\
      (forall k, k ∈ exponent ->
        insert k k ∈ exponentSucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![omega, value, base, nextValue]) := by
  rw [natPowGraphFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    satisfies_natPowGraphShapeDelta, satisfies_natPowTransition]
  tauto

/-! ## Restricted semantics of the transition -/

theorem satisfiesIn_natPowTransition_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega base exponent output exponentSucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hbaseM : base ∈ M)
    (hexponentM : exponent ∈ M) (houtputM : output ∈ M)
    (hexponentSuccM : exponentSucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet)
    (hbaseOmega : base ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] := by
  subst omega
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode base).mp
      hbaseOmega with ⟨a, rfl⟩
  let s : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
      exponent, output, exponentSucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
    · exact hexponentSuccM
    · exact hgraphM
  change Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition s <->
    FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition s
  rw [satisfies_natPowTransition]
  rw [natPowTransition, natPowTransitionAt,
    satisfiesIn_boundedAll_iff]
  simp only [s]
  constructor
  · intro h k hk
    have hkM : k ∈ M := hM.1.mem_trans hk hexponentM
    have hkbody := h k hkM hk
    rw [satisfiesIn_boundedEx_iff] at hkbody
    rcases hkbody with
      ⟨kSucc, hkSuccM, hkSuccDomain, hsucc, hrest⟩
    have hskkM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc s k) kSucc) :=
      Model.tupleIn_snoc_iff.mpr
        ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
    have hsuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc s k) kSucc) hskkM).mp hsucc
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hsuccAmbient
    have hkSuccEq : kSucc = insert k k := by
      simpa only [snoc_last, snoc_castSucc] using hsuccAmbient
    rw [satisfiesIn_boundedEx_iff] at hrest
    rcases hrest with
      ⟨value, hvalueM, hvalueOmega, hvalueFormula, hnextRest⟩
    have hskkvM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc (snoc s k) kSucc) value) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
    have hvalueAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc s k) kSucc) value) hskkvM).mp
          hvalueFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hvalueAmbient
    have hvalueAssign :
        snoc (snoc (snoc s k) kSucc) value =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            exponent, output, exponentSucc, graph, k, kSucc, value] := by
      funext i
      fin_cases i <;> rfl
    rw [hvalueAssign] at hvalueAmbient
    have hvalueGraph : ZFSet.pair k value ∈ graph := hvalueAmbient
    rw [satisfiesIn_boundedEx_iff] at hnextRest
    rcases hnextRest with
      ⟨nextValue, hnextM, hnextOmega, hnextFormula, hmulRenamed⟩
    have hskkvnM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc (snoc (snoc s k) kSucc) value) nextValue) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkvM, hnextM⟩
    have hnextAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc s k) kSucc) value) nextValue)
        hskkvnM).mp hnextFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hnextAmbient
    change ZFSet.pair kSucc nextValue ∈ graph at hnextAmbient
    have hnextGraph : ZFSet.pair kSucc nextValue ∈ graph := hnextAmbient
    rw [satisfiesIn_rename_iff,
      comp_natPowMulRenameAt] at hmulRenamed
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hvalueOmega with ⟨c, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hnextOmega with ⟨d, rfl⟩
    have hmulEq : (natCode d : ZFSet.{u}) = natCode (c * a) :=
      (satisfiesIn_natMulFormula_natCode_iff hM c a hnextM).mp
        hmulRenamed
    have hmulAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode c,
            natCode a, natCode d] :=
      (satisfies_natMulFormula_natCode_iff c a (natCode d)).mpr hmulEq
    rw [hkSuccEq] at hkSuccDomain hnextGraph
    exact ⟨hkSuccDomain, natCode c, hvalueOmega, hvalueGraph,
      natCode d, hnextOmega, hnextGraph, hmulAmbient⟩
  · intro h k hkM hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, hmulAmbient⟩
    have hkSuccM : insert k k ∈ M :=
      hM.1.mem_trans hkSuccDomain hexponentSuccM
    have hvalueM : value ∈ M := hM.1.mem_trans hvalueOmega homegaM
    have hnextM : nextValue ∈ M := hM.1.mem_trans hnextOmega homegaM
    refine ⟨insert k k, hkSuccM, hkSuccDomain, ?_, ?_⟩
    · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc s k) (insert k k)) :=
        Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc s k) (insert k k)) hskkM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simp only [snoc_last, snoc_castSucc]
    · refine ⟨value, hvalueM, hvalueOmega, ?_,
        nextValue, hnextM, hnextOmega, ?_, ?_⟩
      · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc s k) (insert k k)) :=
          Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
        have hassignM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc s k) (insert k k)) value) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
        apply (Model.satisfiesIn_delta0_iff hM.1
          (TextbookDefFormula.graphValueDeltaAt
            (5 : Fin 6).castSucc.castSucc.castSucc
            (Fin.last 6).castSucc.castSucc
            (Fin.last (6 + 2)))
          (snoc (snoc (snoc s k) (insert k k)) value)
          hassignM).mpr
        rw [Delta0Formula.satisfies_toFO,
          TextbookDefFormula.satisfies_graphValueDeltaAt]
        have hvalueAssign :
            snoc (snoc (snoc s k) (insert k k)) value =
              ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
                exponent, output, exponentSucc, graph,
                k, insert k k, value] := by
          funext i
          fin_cases i <;> rfl
        rw [hvalueAssign]
        exact hvalueGraph
      · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc s k) (insert k k)) :=
          Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
        have hskkvM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc s k) (insert k k)) value) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
        have hassignM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc (snoc s k) (insert k k)) value)
              nextValue) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkvM, hnextM⟩
        apply (Model.satisfiesIn_delta0_iff hM.1
          (TextbookDefFormula.graphValueDeltaAt
            (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
            (Fin.last (6 + 1)).castSucc.castSucc
            (Fin.last (6 + 3)))
          (snoc (snoc (snoc (snoc s k) (insert k k)) value)
            nextValue) hassignM).mpr
        rw [Delta0Formula.satisfies_toFO,
          TextbookDefFormula.satisfies_graphValueDeltaAt]
        change ZFSet.pair (insert k k) nextValue ∈ graph
        exact hnextGraph
      · rw [satisfiesIn_rename_iff, comp_natPowMulRenameAt]
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
            hvalueOmega with ⟨c, rfl⟩
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
            hnextOmega with ⟨d, rfl⟩
        have hmulEq : (natCode d : ZFSet.{u}) = natCode (c * a) :=
          (satisfies_natMulFormula_natCode_iff c a (natCode d)).mp
            hmulAmbient
        exact (satisfiesIn_natMulFormula_natCode_iff hM c a hnextM).mpr
          hmulEq

theorem satisfiesIn_natPowGraphFormula_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega base exponent output exponentSucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hbaseM : base ∈ M)
    (hexponentM : exponent ∈ M) (houtputM : output ∈ M)
    (hexponentSuccM : exponentSucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet)
    (hbaseOmega : base ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] := by
  let s : Tuple ZFSet.{u} 6 :=
    ![omega, base, exponent, output, exponentSucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
    · exact hexponentSuccM
    · exact hgraphM
  change
    (Model.SatisfiesIn (M : Set ZFSet.{u})
        natPowGraphShapeDelta.toFO s /\
      Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition s) <->
    (FOFormula.Satisfies Delta0Formula.ZFMem
        natPowGraphShapeDelta.toFO s /\
      FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition s)
  rw [Model.satisfiesIn_delta0_iff hM.1
    natPowGraphShapeDelta s hsM]
  have htransition := satisfiesIn_natPowTransition_iff_ambient
    hM omega base exponent output exponentSucc graph
      homegaM hbaseM hexponentM houtputM hexponentSuccM hgraphM
      homega hbaseOmega
  simpa only [s] using and_congr Iff.rfl htransition

/-! ## Canonical finite graph -/

/-- The canonical tuple `k |-> natCode (base ^ k)`. -/
noncomputable def natPowCanonicalTuple (base exponent : Nat) :
    Tuple (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) (exponent + 1) :=
  fun i =>
    ⟨natCode (base ^ i.1),
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ i.1))).mpr ⟨base ^ i.1, rfl⟩⟩

/-- Kuratowski graph of the canonical exponentiation recursion. -/
noncomputable def natPowCanonicalGraph
    (base exponent : Nat) : ZFSet.{u} :=
  textbookTupleGraph (natPowCanonicalTuple base exponent)

theorem natPowCanonicalGraph_isFunc (base exponent : Nat) :
    ZFSet.IsFunc (natCode (exponent + 1)) Ordinal.omega0.toZFSet
      (natPowCanonicalGraph base exponent) := by
  exact textbookTupleGraph_isFunc (natPowCanonicalTuple base exponent)

/-- The canonical graph belongs to every transitive ZF model. -/
theorem natPowCanonicalGraph_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) :
    natPowCanonicalGraph base exponent ∈ M := by
  apply Model.finiteIsFunc_mem_of_isTransitiveZFModel hM
    (Model.omega_toZFSet_mem_of_isTransitiveZFModel hM)
  exact natPowCanonicalGraph_isFunc base exponent

@[simp]
theorem natPowCanonicalGraph_value
    (base exponent : Nat) (i : Fin (exponent + 1)) :
    ZFSet.pair (natCode i.1) (natCode (base ^ i.1)) ∈
      natPowCanonicalGraph base exponent := by
  exact textbookTupleGraph_value (natPowCanonicalTuple base exponent) i

theorem natPowCanonicalGraph_satisfies (base exponent : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
        natCode exponent, natCode (base ^ exponent),
        natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
  rw [satisfies_natPowGraphFormula]
  refine ⟨natPowCanonicalGraph_isFunc base exponent, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode 0) (exponent + 1)).mpr
          ⟨0, Nat.zero_lt_succ exponent, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode 1)).mpr ⟨1, rfl⟩
    · simpa using
        (natPowCanonicalGraph_value base exponent
          ⟨0, Nat.zero_lt_succ exponent⟩)
  · simpa using
      (natPowCanonicalGraph_value base exponent
        ⟨exponent, Nat.lt_succ_self exponent⟩)
  · intro k hk
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt k exponent).mp hk with
      ⟨j, hj, rfl⟩
    refine ⟨?_, natCode (base ^ j), ?_, ?_,
      natCode (base ^ (j + 1)), ?_, ?_, ?_⟩
    · rw [← natCode_succ_eq_insert j]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode (j + 1)) (exponent + 1)).mpr
          ⟨j + 1, Nat.succ_lt_succ hj, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ j))).mpr ⟨base ^ j, rfl⟩
    · exact natPowCanonicalGraph_value base exponent
        ⟨j, hj.trans (Nat.lt_succ_self exponent)⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ (j + 1)))).mpr ⟨base ^ (j + 1), rfl⟩
    · rw [← natCode_succ_eq_insert j]
      exact natPowCanonicalGraph_value base exponent
        ⟨j + 1, Nat.succ_lt_succ hj⟩
    · apply (satisfies_natMulFormula_natCode_iff
        (base ^ j) base (natCode (base ^ (j + 1)))).mpr
      simp [pow_succ]

/-- The canonical graph also satisfies the graph formula internally. -/
theorem natPowCanonicalGraph_satisfiesIn
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
        natCode exponent, natCode (base ^ exponent),
        natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
  have homegaM := Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hbaseM := Model.natCode_mem_of_isTransitiveZFModel hM base
  have hexponentM := Model.natCode_mem_of_isTransitiveZFModel hM exponent
  have houtputM :=
    Model.natCode_mem_of_isTransitiveZFModel hM (base ^ exponent)
  have hsuccM :=
    Model.natCode_mem_of_isTransitiveZFModel hM (exponent + 1)
  have hgraphM :=
    natPowCanonicalGraph_mem_of_isTransitiveZFModel hM base exponent
  have hbaseOmega :
      (natCode base : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode base)).mpr ⟨base, rfl⟩
  apply (satisfiesIn_natPowGraphFormula_iff_ambient hM
    Ordinal.omega0.toZFSet (natCode base) (natCode exponent)
    (natCode (base ^ exponent)) (natCode (exponent + 1))
    (natPowCanonicalGraph base exponent)
    homegaM hbaseM hexponentM houtputM hsuccM hgraphM
    rfl hbaseOmega).mpr
  exact natPowCanonicalGraph_satisfies base exponent

/-! ## Uniqueness and exact ambient semantics -/

theorem natPowGraphFormula_output_unique
    (base exponent : Nat) (output exponentSucc graph : ZFSet.{u})
    (hexponentSucc : exponentSucc = natCode (exponent + 1))
    (hgraph :
      FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output, exponentSucc, graph]) :
    output = natCode (base ^ exponent) := by
  rw [satisfies_natPowGraphFormula] at hgraph
  rcases hgraph with ⟨hfunc, hzero, hexponentValue, hstep⟩
  have hvalues : forall j : Nat, j <= exponent ->
      ZFSet.pair (natCode j) (natCode (base ^ j)) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        simpa [natCode] using hzero.2.2
    | succ j ih =>
        have hjExponent : j < exponent := Nat.lt_of_succ_le hj
        rcases hstep (natCode j)
            ((IndexedSequenceZF.mem_natCode_iff_exists_lt
              (natCode j) exponent).mpr ⟨j, hjExponent, rfl⟩) with
          ⟨_hjSuccDomain, value, _hvalueOmega, hvalue,
            nextValue, _hnextOmega, hnext, hmul⟩
        have hjDomain : (natCode j : ZFSet.{u}) ∈ exponentSucc := by
          rw [hexponentSucc]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (exponent + 1)).mpr
              ⟨j, hjExponent.trans (Nat.lt_succ_self exponent), rfl⟩
        rcases hfunc.2 (natCode j) hjDomain with
          ⟨graphValue, _hgraphValue, hunique⟩
        have hprevious := ih (Nat.le_of_lt hjExponent)
        have hvalueEq : value = natCode (base ^ j) :=
          (hunique value hvalue).trans
            (hunique (natCode (base ^ j)) hprevious).symm
        have hnextValueEq : nextValue = natCode (base ^ (j + 1)) := by
          rw [hvalueEq] at hmul
          have hmulEq :=
            (satisfies_natMulFormula_natCode_iff
              (base ^ j) base nextValue).mp hmul
          simpa [pow_succ] using hmulEq
        rw [← natCode_succ_eq_insert j, hnextValueEq] at hnext
        simpa using hnext
  have hexponentDomain : (natCode exponent : ZFSet.{u}) ∈ exponentSucc := by
    rw [hexponentSucc]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode exponent) (exponent + 1)).mpr
        ⟨exponent, Nat.lt_succ_self exponent, rfl⟩
  rcases hfunc.2 (natCode exponent) hexponentDomain with
    ⟨graphValue, _hgraphValue, hunique⟩
  exact (hunique output hexponentValue).trans
    (hunique (natCode (base ^ exponent))
      (hvalues exponent le_rfl)).symm

@[simp]
theorem satisfies_natPowFormula_ambient
    (omega base exponent output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![omega, base, exponent, output] <->
      omega = Ordinal.omega0.toZFSet /\
      base ∈ omega /\ exponent ∈ omega /\ output ∈ omega /\
      exists exponentSucc, exponentSucc = insert exponent exponent /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
            ![omega, base, exponent, output, exponentSucc, graph] := by
  let s : Tuple ZFSet.{u} 4 := ![omega, base, exponent, output]
  have hs0 : s (0 : Fin 4) = omega := rfl
  have hs1 : s (1 : Fin 4) = base := rfl
  have hs2 : s (2 : Fin 4) = exponent := rfl
  have hs3 : s (3 : Fin 4) = output := rfl
  change
    (FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (Delta0Formula.ZFMem (s 1) (s 0) /\
      (Delta0Formula.ZFMem (s 2) (s 0) /\
      (Delta0Formula.ZFMem (s 3) (s 0) /\
      exists exponentSucc,
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s exponentSucc) /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
            (snoc (snoc s exponentSucc) graph))))) <-> _
  rw [satisfies_standardOmegaAt_ambient_iff]
  simp only [hs0, hs1, hs2, hs3]
  constructor
  · rintro ⟨homega, hbase, hexponent, houtput, exponentSucc,
      hsuccFormula, graph, hgraphFormula⟩
    have hsucc : exponentSucc = insert exponent exponent := by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt] at hsuccFormula
      simpa only [snoc_last, snoc_castSucc, hs2] using hsuccFormula
    have hassign : snoc (snoc s exponentSucc) graph =
        ![omega, base, exponent, output, exponentSucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphFormula
    exact ⟨homega, hbase, hexponent, houtput,
      exponentSucc, hsucc, graph, hgraphFormula⟩
  · rintro ⟨homega, hbase, hexponent, houtput,
      exponentSucc, hsucc, graph, hgraph⟩
    refine ⟨homega, hbase, hexponent, houtput, exponentSucc, ?_, graph, ?_⟩
    · rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hs2] using hsucc
    · have hassign : snoc (snoc s exponentSucc) graph =
          ![omega, base, exponent, output, exponentSucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign]
      exact hgraph

@[simp]
theorem satisfies_natPowFormula_natCode_iff
    (base exponent : Nat) (output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output] <->
      output = natCode (base ^ exponent) := by
  rw [satisfies_natPowFormula_ambient]
  constructor
  · rintro ⟨_homega, _hbaseOmega, _hexponentOmega, _houtputOmega,
      exponentSucc, hsucc, graph, hgraph⟩
    apply natPowGraphFormula_output_unique
      base exponent output exponentSucc graph
    · exact hsucc.trans (natCode_succ_eq_insert exponent).symm
    · exact hgraph
  · intro houtput
    subst output
    refine ⟨rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode base)).mpr ⟨base, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩,
      natCode (exponent + 1), natCode_succ_eq_insert exponent,
      natPowCanonicalGraph base exponent,
      natPowCanonicalGraph_satisfies base exponent⟩

/-! ## Exact restricted semantics -/

theorem satisfiesIn_natPowFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) {output : ZFSet.{u}} (houtputM : output ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output] <->
      output = natCode (base ^ exponent) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let s : Tuple ZFSet.{u} 4 :=
    ![omega, natCode base, natCode exponent, output]
  have hsExponent : s (2 : Fin 4) = natCode exponent := rfl
  have homegaM : omega ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hbaseM : (natCode base : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM base
  have hexponentM : (natCode exponent : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM exponent
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
  have hbaseOmega : (natCode base : ZFSet.{u}) ∈ omega :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode base)).mpr ⟨base, rfl⟩
  change
    ((Model.SatisfiesIn (M : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      ((natCode base : ZFSet.{u}) ∈ omega /\
      ((natCode exponent : ZFSet.{u}) ∈ omega /\
      (output ∈ omega /\
      exists exponentSucc, exponentSucc ∈ M /\
        (Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s exponentSucc) /\
        exists graph, graph ∈ M /\
          Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
            (snoc (snoc s exponentSucc) graph)))))) <-> _)
  constructor
  · rintro ⟨omegaFormula, _hbaseOmega, _hexponentOmega, _houtputOmega,
      exponentSucc, hexponentSuccM, hsuccFormula,
      graph, hgraphM, hgraphFormula⟩
    have homega : s (0 : Fin 4) = Ordinal.omega0.toZFSet :=
      (Model.satisfiesIn_standardOmegaAt_iff hM
        (0 : Fin 4) s hsM).mp omegaFormula
    have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc s exponentSucc) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsM, hexponentSuccM⟩
    have hsuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s exponentSucc) hsuccAssignM).mp hsuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hsuccAmbient
    have hexponentSucc : exponentSucc = natCode (exponent + 1) := by
      have hraw :
          exponentSucc = insert (natCode exponent) (natCode exponent) := by
        simpa only [snoc_last, snoc_castSucc, hsExponent] using
          hsuccAmbient
      exact hraw.trans (natCode_succ_eq_insert exponent).symm
    have hgraphAssign : snoc (snoc s exponentSucc) graph =
        ![omega, natCode base, natCode exponent,
          output, exponentSucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hgraphAssign] at hgraphFormula
    have hgraphAmbient :=
      (satisfiesIn_natPowGraphFormula_iff_ambient hM
        omega (natCode base) (natCode exponent) output
        exponentSucc graph homegaM hbaseM hexponentM houtputM
        hexponentSuccM hgraphM rfl
        hbaseOmega).mp hgraphFormula
    exact natPowGraphFormula_output_unique
      base exponent output exponentSucc graph
      hexponentSucc hgraphAmbient
  · intro houtput
    have houtputEq : output = (natCode (base ^ exponent) : ZFSet.{u}) :=
      houtput
    have hexponentSuccM : (natCode (exponent + 1) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (exponent + 1)
    have hgraphM : natPowCanonicalGraph base exponent ∈ M :=
      natPowCanonicalGraph_mem_of_isTransitiveZFModel
        hM base exponent
    refine ⟨(Model.satisfiesIn_standardOmegaAt_iff hM
      (0 : Fin 4) s hsM).mpr rfl,
      hbaseOmega,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩, ?_,
      natCode (exponent + 1), hexponentSuccM, ?_,
      natPowCanonicalGraph base exponent, hgraphM, ?_⟩
    · rw [houtputEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩
    · have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
          (snoc s (natCode (exponent + 1))) :=
        Model.tupleIn_snoc_iff.mpr ⟨hsM, hexponentSuccM⟩
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s (natCode (exponent + 1))) hsuccAssignM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hsExponent] using
        (natCode_succ_eq_insert exponent)
    · have hgraphAssign :
          snoc (snoc s (natCode (exponent + 1)))
              (natPowCanonicalGraph base exponent) =
            ![omega, natCode base, natCode exponent, output,
              natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
        funext i
        fin_cases i <;> rfl
      rw [hgraphAssign, houtputEq]
      exact natPowCanonicalGraph_satisfiesIn hM base exponent

/-! ## Standard function-absoluteness packaging -/

/-- Total ambient operation on arbitrary set codes.  Invalid inputs map to
the empty set; the formula's domain predicate excludes them. -/
noncomputable def natPowCodeZF (base exponent : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode base, textbookNatDecode exponent with
  | some a, some b => natCode (a ^ b)
  | _, _ => ∅

@[simp]
theorem natPowCodeZF_natCode (base exponent : Nat) :
    natPowCodeZF (natCode base : ZFSet.{u}) (natCode exponent) =
      natCode (base ^ exponent) := by
  simp [natPowCodeZF]

/-- Input domain for the parameter tuple `[omega, base, exponent]`. -/
def NatPowTupleDomain : Set (Tuple ZFSet.{u} 3) :=
  {s | s 0 = Ordinal.omega0.toZFSet /\
    exists base exponent : Nat,
      s 1 = natCode base /\ s 2 = natCode exponent}

/-- Ambient value function represented by `natPowFormula`. -/
noncomputable def natPowTupleFunction
    (s : Tuple ZFSet.{u} 3) : ZFSet.{u} :=
  natPowCodeZF (s 1) (s 2)

/-- Standard exponentiation is absolute to every transitive set model of ZF. -/
theorem natPow_functionAbsoluteTo
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M) :
    Model.FunctionAbsoluteTo (M : Set ZFSet.{u})
      NatPowTupleDomain natPowTupleFunction natPowFormula := by
  constructor
  · intro s hsM hsDomain
    rcases hsDomain with ⟨_homega, base, exponent, hbase, hexponent⟩
    rw [natPowTupleFunction, hbase, hexponent, natPowCodeZF_natCode]
    exact Model.natCode_mem_of_isTransitiveZFModel
      hM (base ^ exponent)
  · intro s output hsM houtputM
    constructor
    · intro hformula
      rw [natPowFormula] at hformula
      have homega : s 0 = Ordinal.omega0.toZFSet :=
        (Model.satisfiesIn_standardOmegaAt_iff hM
          (0 : Fin 4) (snoc s output)
          (Model.tupleIn_snoc_iff.mpr ⟨hsM, houtputM⟩)).mp hformula.1
      have hbaseOmega : s 1 ∈ Ordinal.omega0.toZFSet := by
        rw [← homega]
        have hbaseFormula := hformula.2.1
        change snoc s output (1 : Fin 3).castSucc ∈
          snoc s output (0 : Fin 3).castSucc at hbaseFormula
        simpa only [snoc_castSucc] using hbaseFormula
      have hexponentOmega : s 2 ∈ Ordinal.omega0.toZFSet := by
        rw [← homega]
        have hexponentFormula := hformula.2.2.1
        change snoc s output (2 : Fin 3).castSucc ∈
          snoc s output (0 : Fin 3).castSucc at hexponentFormula
        simpa only [snoc_castSucc] using hexponentFormula
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode (s 1)).mp
          hbaseOmega with ⟨base, hbase⟩
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode (s 2)).mp
          hexponentOmega with ⟨exponent, hexponent⟩
      have hassign : snoc s output =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
            natCode base, natCode exponent, output] := by
        funext i
        fin_cases i
        · exact homega
        · exact hbase
        · exact hexponent
        · rfl
      have hvalue : output = natCode (base ^ exponent) :=
        (satisfiesIn_natPowFormula_natCode_iff
          hM base exponent houtputM).mp (by rwa [← hassign])
      refine ⟨⟨homega, base, exponent, hbase, hexponent⟩, ?_⟩
      rw [natPowTupleFunction, hbase, hexponent,
        natPowCodeZF_natCode]
      exact hvalue
    · rintro ⟨⟨homega, base, exponent, hbase, hexponent⟩, hvalue⟩
      have hfunction :
          natPowTupleFunction s = natCode (base ^ exponent) := by
        rw [natPowTupleFunction, hbase, hexponent,
          natPowCodeZF_natCode]
      have houtput : output = natCode (base ^ exponent) :=
        hvalue.trans hfunction
      have hassign : snoc s output =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
            natCode base, natCode exponent, output] := by
        funext i
        fin_cases i
        · exact homega
        · exact hbase
        · exact hexponent
        · rfl
      rw [hassign]
      exact (satisfiesIn_natPowFormula_natCode_iff
        hM base exponent houtputM).mpr houtput

end TextbookNatFormula

end Constructible
